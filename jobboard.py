#!/usr/bin/env python3
"""
Personal jobs board.

Reads organisations.csv, checks each organisation's website for open jobs,
remembers what it found before (data/jobs.json), and writes index.html:
a web page listing every job, with new and closed jobs marked.

How it finds jobs, in order:
  1. Recruitment software with a public job list (Greenhouse, Lever, Ashby,
     Workable, SmartRecruiters, Recruitee, Personio).
  2. Job details hidden in the page for Google (schema.org JobPosting).
  3. Links on the careers page that look like job titles.
If the address in the spreadsheet is a homepage, it first looks for a
"Careers" / "Jobs" / "Vacancies" link and follows it.
"""

import csv
import hashlib
import json
import re
import sys
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parent
ORGS_FILE = ROOT / "organisations.csv"
DATA_DIR = ROOT / "data"
JOBS_FILE = DATA_DIR / "jobs.json"
SOURCES_FILE = DATA_DIR / "sources.json"
BOARD_FILE = ROOT / "index.html"

HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; personal-job-board/1.0; checks once a day)",
    "Accept-Language": "en-GB,en;q=0.9",
}
TIMEOUT = 25
WORKERS = 8
MAX_PAGE_JOBS = 60


# --------------------------------------------------------------------------
# Fetching
# --------------------------------------------------------------------------

def get(url):
    """Download a web address. Raises an error if the site doesn't answer."""
    resp = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
    resp.raise_for_status()
    return resp


def clean(text):
    return re.sub(r"\s+", " ", text or "").strip()


# --------------------------------------------------------------------------
# 1. Recruitment software (ATS) feeds
# --------------------------------------------------------------------------

ATS_PATTERNS = [
    ("greenhouse", r"greenhouse\.io/embed/job_board(?:/js)?\?for=([A-Za-z0-9_-]+)"),
    ("greenhouse", r"(?:boards|job-boards)(?:\.eu)?\.greenhouse\.io/([A-Za-z0-9_-]+)"),
    ("lever", r"jobs\.(eu\.)?lever\.co/([A-Za-z0-9_.-]+)"),
    ("ashby", r"jobs\.ashbyhq\.com/([A-Za-z0-9_.%-]+)"),
    ("workable", r"apply\.workable\.com/([A-Za-z0-9_-]+)"),
    ("smartrecruiters", r"(?:jobs|careers)\.smartrecruiters\.com/([A-Za-z0-9_-]+)"),
    ("recruitee", r"([A-Za-z0-9-]+)\.recruitee\.com"),
    ("personio", r"([A-Za-z0-9-]+)\.jobs\.personio\.(de|com)"),
]
IGNORED_TOKENS = {"embed", "js", "api", "v1", "j", "jobs", "www", "careers", "static", "assets"}


def detect_ats(text):
    """Look through a web address or page for signs of recruitment software."""
    for name, pattern in ATS_PATTERNS:
        for m in re.finditer(pattern, text):
            if name == "lever":
                token, extra = m.group(2), m.group(1) or ""
            elif name == "personio":
                token, extra = m.group(1), m.group(2)
            else:
                token, extra = m.group(1), ""
            if token.lower() in IGNORED_TOKENS:
                continue
            return name, token, extra
    return None


def fetch_ats(name, token, extra):
    jobs = []
    if name == "greenhouse":
        data = get(f"https://boards-api.greenhouse.io/v1/boards/{token}/jobs").json()
        for j in data.get("jobs", []):
            jobs.append({"title": j.get("title"), "url": j.get("absolute_url"),
                         "location": (j.get("location") or {}).get("name", "")})
    elif name == "lever":
        host = "api.eu.lever.co" if extra else "api.lever.co"
        data = get(f"https://{host}/v0/postings/{token}?mode=json").json()
        for j in data:
            jobs.append({"title": j.get("text"), "url": j.get("hostedUrl"),
                         "location": (j.get("categories") or {}).get("location", "")})
    elif name == "ashby":
        data = get(f"https://api.ashbyhq.com/posting-api/job-board/{token}").json()
        for j in data.get("jobs", []):
            jobs.append({"title": j.get("title"), "url": j.get("jobUrl"),
                         "location": j.get("location", "")})
    elif name == "workable":
        data = get(f"https://apply.workable.com/api/v1/widget/accounts/{token}").json()
        for j in data.get("jobs", []):
            loc = ", ".join(x for x in [j.get("city"), j.get("country")] if x)
            jobs.append({"title": j.get("title"), "url": j.get("url"), "location": loc})
    elif name == "smartrecruiters":
        data = get(f"https://api.smartrecruiters.com/v1/companies/{token}/postings?limit=100").json()
        for j in data.get("content", []):
            loc = j.get("location") or {}
            jobs.append({"title": j.get("name"),
                         "url": f"https://jobs.smartrecruiters.com/{token}/{j.get('id')}",
                         "location": ", ".join(x for x in [loc.get("city"), loc.get("country")] if x)})
    elif name == "recruitee":
        data = get(f"https://{token}.recruitee.com/api/offers/").json()
        for j in data.get("offers", []):
            jobs.append({"title": j.get("title"), "url": j.get("careers_url"),
                         "location": j.get("location", "")})
    elif name == "personio":
        base = f"https://{token}.jobs.personio.{extra or 'de'}"
        root = ET.fromstring(get(f"{base}/xml").content)
        for p in root.iter("position"):
            jid = (p.findtext("id") or "").strip()
            jobs.append({"title": p.findtext("name"), "url": f"{base}/job/{jid}",
                         "location": p.findtext("office") or ""})
    return [j for j in jobs if j.get("title") and j.get("url")]


# --------------------------------------------------------------------------
# 2. Structured job data in the page (schema.org JobPosting)
# --------------------------------------------------------------------------

def _walk(obj):
    if isinstance(obj, dict):
        yield obj
        for v in obj.values():
            yield from _walk(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _walk(v)


def _is_job(d):
    t = d.get("@type")
    return t == "JobPosting" or (isinstance(t, list) and "JobPosting" in t)


def _location(d):
    loc = d.get("jobLocation")
    if isinstance(loc, list):
        loc = loc[0] if loc else None
    if isinstance(loc, dict):
        addr = loc.get("address") or {}
        if isinstance(addr, dict):
            return ", ".join(x for x in [addr.get("addressLocality"), addr.get("addressCountry")
                                         if isinstance(addr.get("addressCountry"), str) else None] if x)
    if d.get("jobLocationType") == "TELECOMMUTE":
        return "Remote"
    return ""


def find_structured_jobs(soup, page_url):
    jobs = []
    for tag in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(tag.string or tag.get_text() or "")
        except (ValueError, TypeError):
            continue
        for d in _walk(data):
            if _is_job(d) and d.get("title"):
                jobs.append({"title": clean(d["title"]),
                             "url": urljoin(page_url, d.get("url") or page_url),
                             "location": _location(d)})
    return jobs


# --------------------------------------------------------------------------
# 3. Links that look like jobs
# --------------------------------------------------------------------------

JOB_WORDS = re.compile(
    r"\b(manager|officer|director|co-?ordinator|lead|analyst|assistant|executive|head of|"
    r"consultant|advis[oe]r|specialist|intern(ship)?|engineer|associate|researcher|scientist|"
    r"developer|designer|administrator|campaigner|fundraiser|trustee|fellow(ship)?|technician|"
    r"accountant|editor|writer|producer|chief|planner|strategist|representative|apprentice|"
    r"graduate|programme|program|policy|communications|operations|secretary|chair|ceo|cfo|coo)\b",
    re.I)
JOB_HREF = re.compile(r"(job|vacanc|career|position|role|opportunit|recruit|apply|join)", re.I)
NOT_JOB = re.compile(
    r"(privacy|cookie|terms|log ?in|sign ?in|sign ?up|subscribe|newsletter|linkedin\.com|facebook|"
    r"twitter|x\.com|instagram|youtube|mailto:|tel:|javascript:)", re.I)
NAV_TEXT = re.compile(
    r"^(careers?|jobs?|vacancies|current vacancies|work (with|for) us|join (us|our team)|"
    r"opportunities|our team|meet the team|about us|contact( us)?|read more|apply( now)?|"
    r"learn more|find out more|view (all )?(jobs|roles|vacancies)|see all.*)$", re.I)


def find_link_jobs(soup, page_url):
    jobs, seen = [], set()
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        text = clean(a.get_text(" "))
        if not text or len(text) < 5 or len(text) > 140:
            continue
        if href.startswith("#") or NOT_JOB.search(href) or NOT_JOB.search(text):
            continue
        if NAV_TEXT.match(text):
            continue
        is_pdf = href.lower().split("?")[0].endswith((".pdf", ".docx", ".doc"))
        if not JOB_WORDS.search(text):
            continue
        if not (JOB_HREF.search(href) or is_pdf):
            continue
        url = urljoin(page_url, href)
        key = (text.lower(), url)
        if key in seen:
            continue
        seen.add(key)
        jobs.append({"title": text, "url": url, "location": ""})
        if len(jobs) >= MAX_PAGE_JOBS:
            break
    return jobs


CAREERS_TEXT = re.compile(
    r"\b(careers?|jobs?|vacanc(y|ies)|work (with|for) us|join (us|our team|the team)|"
    r"current opportunities|recruitment)\b", re.I)
CAREERS_HREF = re.compile(r"/(careers?|jobs?|vacanc(y|ies)|work-(with|for)-us|join-(us|our-team)|"
                          r"opportunities|recruitment)\b", re.I)


def find_careers_link(soup, page_url):
    """On a homepage, find the most likely 'Careers' / 'Jobs' page."""
    best, best_score = None, 0
    home_host = urlparse(page_url).netloc
    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if href.startswith(("#", "mailto:", "tel:", "javascript:")):
            continue
        text = clean(a.get_text(" "))
        score = 0
        if text and len(text) < 40 and CAREERS_TEXT.search(text):
            score += 2
        if CAREERS_HREF.search(href):
            score += 2
        if detect_ats(href):
            score += 3
        if score == 0:
            continue
        url = urljoin(page_url, href)
        if urlparse(url).netloc not in (home_host, "") and not detect_ats(url):
            score -= 1
        if score > best_score:
            best, best_score = url, score
    return best


# --------------------------------------------------------------------------
# Checking one organisation
# --------------------------------------------------------------------------

def is_homepage(url):
    return urlparse(url).path.strip("/") == ""


def check_page(url):
    """Look for jobs on one page. Returns (jobs, method, soup, html)."""
    # The address itself might be a recruitment-software page.
    ats = detect_ats(url)
    if ats:
        try:
            return fetch_ats(*ats), f"recruitment software ({ats[0]})", None, ""
        except Exception:
            pass
    resp = get(url)
    html = resp.text
    page_url = resp.url
    ats = detect_ats(html)
    if ats:
        try:
            return fetch_ats(*ats), f"recruitment software ({ats[0]})", None, html
        except Exception:
            pass
    soup = BeautifulSoup(html, "html.parser")
    jobs = find_structured_jobs(soup, page_url)
    if jobs:
        return jobs, "job data in page", soup, html
    return find_link_jobs(soup, page_url), "page scan", soup, html


def check_org(org):
    result = {"name": org["name"], "sector": org["sector"], "url": org["url"],
              "checked": "", "method": "", "jobs": [], "error": ""}
    start = (org.get("jobs_page") or org["url"]).strip()
    if not start:
        result["error"] = "No website address in the spreadsheet yet"
        return result
    if not start.startswith("http"):
        start = "https://" + start
    result["checked"] = start
    try:
        jobs, method, soup, _ = check_page(start)
        # A homepage usually has no jobs on it: follow its Careers link.
        if soup is not None and (not jobs or is_homepage(start)) and not org.get("jobs_page"):
            link = find_careers_link(soup, start)
            if link and link.rstrip("/") != start.rstrip("/"):
                result["checked"] = link
                jobs, method, soup2, _ = check_page(link)
                # Careers pages sometimes link one level deeper ("Current vacancies").
                if not jobs and soup2 is not None:
                    deeper = find_careers_link(soup2, link)
                    if deeper and deeper.rstrip("/") not in (link.rstrip("/"), start.rstrip("/")):
                        result["checked"] = deeper
                        jobs, method, _, _ = check_page(deeper)
            elif is_homepage(start):
                jobs = []
                result["error"] = "Couldn't find a careers page link on the homepage"
        result["jobs"] = jobs
        result["method"] = method
    except requests.HTTPError as e:
        result["error"] = f"Website returned an error ({e.response.status_code})"
    except requests.RequestException:
        result["error"] = "Website didn't respond"
    except Exception as e:  # keep going whatever happens with one site
        result["error"] = f"Unexpected problem: {type(e).__name__}"
    return result


# --------------------------------------------------------------------------
# Remembering jobs between runs
# --------------------------------------------------------------------------

def job_id(org_name, job):
    raw = f"{org_name}|{job['url']}|{job['title']}".lower()
    return hashlib.sha1(raw.encode()).hexdigest()[:12]


def load_json(path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, ValueError):
        return default


def read_orgs():
    with ORGS_FILE.open(newline="", encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    orgs = []
    for r in rows:
        r = {(k or "").strip().lower(): (v or "").strip() for k, v in r.items()}
        if not r.get("name") or r.get("skip", "").lower() in ("yes", "y", "true", "1"):
            continue
        orgs.append({"name": r["name"], "sector": r.get("sector", "") or "Other",
                     "url": r.get("website", ""), "jobs_page": r.get("jobs_page", "")})
    return orgs


def merge(state, results, today):
    jobs = state.setdefault("jobs", {})
    for res in results:
        if res["error"]:
            continue  # site was unreachable: leave its jobs as they were
        found = set()
        for j in res["jobs"]:
            jid = job_id(res["name"], j)
            found.add(jid)
            rec = jobs.get(jid)
            if rec is None:
                jobs[jid] = rec = {"org": res["name"], "first_seen": today}
            rec.update({"title": clean(j["title"]), "url": j["url"],
                        "location": clean(j.get("location") or ""), "sector": res["sector"],
                        "source": res["method"], "last_seen": today, "status": "open"})
            rec.pop("closed_on", None)
        for jid, rec in jobs.items():
            if rec["org"] == res["name"] and jid not in found and rec.get("status") == "open":
                rec["status"] = "closed"
                rec["closed_on"] = today
    # Forget jobs that closed more than 60 days ago.
    cutoff = datetime.strptime(today, "%Y-%m-%d").toordinal() - 60
    for jid in [k for k, v in jobs.items() if v.get("status") == "closed"
                and datetime.strptime(v.get("closed_on", today), "%Y-%m-%d").toordinal() < cutoff]:
        del jobs[jid]
    return state


# --------------------------------------------------------------------------
# Building the web page
# --------------------------------------------------------------------------

def build_board(state, sources, today):
    data = {"updated": today, "first_run": state.get("first_run", today),
            "jobs": [dict(id=k, **v) for k, v in state["jobs"].items()],
            "sources": sources}
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    template = (ROOT / "board_template.html").read_text(encoding="utf-8")
    BOARD_FILE.write_text(template.replace("__BOARD_DATA__", payload), encoding="utf-8")
    (ROOT / ".nojekyll").write_text("")


def main():
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    orgs = read_orgs()
    print(f"Checking {len(orgs)} organisations…")
    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        results = list(pool.map(check_org, orgs))

    state = load_json(JOBS_FILE, {})
    state.setdefault("first_run", today)
    merge(state, results, today)

    open_counts = {}
    for rec in state["jobs"].values():
        if rec.get("status") == "open":
            open_counts[rec["org"]] = open_counts.get(rec["org"], 0) + 1
    sources = [{"name": r["name"], "sector": r["sector"], "checked": r["checked"],
                "method": r["method"], "found": len(r["jobs"]), "open": open_counts.get(r["name"], 0),
                "error": r["error"]} for r in results]

    DATA_DIR.mkdir(exist_ok=True)
    JOBS_FILE.write_text(json.dumps(state, indent=1, ensure_ascii=False), encoding="utf-8")
    SOURCES_FILE.write_text(json.dumps(sources, indent=1, ensure_ascii=False), encoding="utf-8")
    build_board(state, sources, today)

    ok = sum(1 for r in results if not r["error"])
    total_open = sum(open_counts.values())
    print(f"Done: {ok}/{len(results)} sites checked, {total_open} open jobs on the board.")
    for r in results:
        status = r["error"] or f"{len(r['jobs'])} jobs via {r['method']}"
        print(f"  - {r['name']}: {status}")


if __name__ == "__main__":
    sys.exit(main())
