#!/usr/bin/env python3
from __future__ import annotations

import asyncio
import csv
import json
import logging
import os
import re
import sys
import time
import urllib3
import zipfile
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, timedelta
from io import BytesIO
from pathlib import Path
from typing import Any, Dict, Iterable, Iterator, List, Optional, Sequence, Tuple
from urllib.parse import urljoin
from xml.etree import ElementTree as ET

import requests
from bs4 import BeautifulSoup
from playwright.async_api import BrowserContext, Locator, Page, TimeoutError as PlaywrightTimeoutError
from playwright.async_api import async_playwright

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DASHBOARD_DIR = BASE_DIR / "dashboard"
TMP_DIR = BASE_DIR / ".tmp"
LOG_DIR = BASE_DIR / ".logs"

LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "7"))
REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "30"))
MAX_RETRIES = int(os.getenv("MAX_RETRIES", "3"))
HEADLESS = os.getenv("HEADLESS", "true").lower() != "false"

PUBLIC_NOTICE_URL = os.getenv(
    "PUBLIC_NOTICE_URL",
    "https://www.georgiapublicnotice.com/search.aspx",
)

PROPERTY_APPRAISER_BULK_DATA_URL = os.getenv(
    "PROPERTY_APPRAISER_BULK_DATA_URL",
    "https://gwinnettcountyga.gov/static/departments/gis-data/downloads/Parcel.zip",
).strip()

TARGET_COUNTY = os.getenv("TARGET_COUNTY", "Gwinnett").strip()

# Hard runtime caps so it cannot wander forever.
MAX_RESULTS_PAGES = int(os.getenv("MAX_RESULTS_PAGES", "1"))
MAX_DETAIL_LINKS_PER_SEARCH = int(os.getenv("MAX_DETAIL_LINKS_PER_SEARCH", "5"))
MAX_DETAIL_PAGES_TOTAL = int(os.getenv("MAX_DETAIL_PAGES_TOTAL", "10"))
PER_SEARCH_TIMEOUT_MS = int(os.getenv("PER_SEARCH_TIMEOUT_MS", "4000"))
PAGE_WAIT_MS = int(os.getenv("PAGE_WAIT_MS", "500"))

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

# Keep this tight until proven.
SEARCH_TERMS: List[Tuple[str, str]] = [
    ("NOFC", "foreclosure"),
    ("PRO", "estate"),
]

CATEGORY_LABELS: Dict[str, str] = {
    "LP": "Lis Pendens",
    "NOFC": "Notice of Foreclosure",
    "TAXDEED": "Tax Deed",
    "JUD": "Judgment",
    "CCJ": "Certified Judgment",
    "DRJUD": "Domestic Judgment",
    "LNCORPTX": "Corporate Tax Lien",
    "LNIRS": "IRS Lien",
    "LNFED": "Federal Lien",
    "LN": "Lien",
    "LNMECH": "Mechanic Lien",
    "LNHOA": "HOA Lien",
    "MEDLN": "Medicaid Lien",
    "PRO": "Probate / Estate",
    "NOC": "Notice of Commencement",
    "RELLP": "Release Lis Pendens",
}

FLAG_POINTS = {
    "Lis pendens": 10,
    "Pre-foreclosure": 10,
    "Judgment lien": 10,
    "Tax lien": 10,
    "Mechanic lien": 10,
    "Probate / estate": 10,
    "LLC / corp owner": 10,
    "New this week": 5,
}


@dataclass
class RawRecord:
    doc_num: str = ""
    doc_type: str = ""
    filed: str = ""
    cat: str = ""
    cat_label: str = ""
    owner: str = ""
    grantee: str = ""
    amount: str = ""
    legal: str = ""
    clerk_url: str = ""
    notice_text: str = ""


@dataclass
class LeadRecord(RawRecord):
    prop_address: str = ""
    prop_city: str = ""
    prop_state: str = ""
    prop_zip: str = ""
    mail_address: str = ""
    mail_city: str = ""
    mail_state: str = ""
    mail_zip: str = ""
    flags: List[str] = field(default_factory=list)
    score: int = 0


logger = logging.getLogger("gwinnett_scraper")


def setup_logging() -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s  %(levelname)-8s %(message)s",
        handlers=[
            logging.StreamHandler(sys.stdout),
            logging.FileHandler(LOG_DIR / "fetch.log", encoding="utf-8"),
        ],
    )


def ensure_dirs() -> None:
    for path in [DATA_DIR, DASHBOARD_DIR, TMP_DIR, LOG_DIR]:
        path.mkdir(parents=True, exist_ok=True)


def write_initial_empty_records() -> None:
    payload = {
        "fetched_at": None,
        "source": "Gwinnett County",
        "date_range": {"from": None, "to": None, "lookback_days": LOOKBACK_DAYS},
        "total": 0,
        "with_address": 0,
        "records": [],
    }
    for path in [DATA_DIR / "records.json", DASHBOARD_DIR / "records.json"]:
        if not path.exists():
            path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def retryable(fn):
    def wrapper(*args, **kwargs):
        last_exc = None
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                return fn(*args, **kwargs)
            except Exception as exc:
                last_exc = exc
                logger.warning(
                    "Attempt %s/%s failed for %s: %s",
                    attempt,
                    MAX_RETRIES,
                    fn.__name__,
                    exc,
                )
                if attempt < MAX_RETRIES:
                    time.sleep(min(attempt * 2, 6))
        raise last_exc
    return wrapper


def clean_text(value: Any) -> str:
    if value is None:
        return ""
    text = str(value).replace("\xa0", " ")
    text = re.sub(r"\s+", " ", text).strip()
    return text


def normalize_spaces(text: str) -> str:
    return re.sub(r"\s+", " ", clean_text(text))


def normalize_name(name: str) -> str:
    name = clean_text(name).upper().replace("&", " AND ")
    name = re.sub(r"[^A-Z0-9, ]+", " ", name)
    return normalize_spaces(name)


def parse_date_text(value: str) -> Optional[date]:
    text = clean_text(value)
    if not text:
        return None
    for fmt in ("%m/%d/%Y", "%m/%d/%y", "%Y-%m-%d", "%b %d, %Y", "%B %d, %Y"):
        try:
            return datetime.strptime(text, fmt).date()
        except ValueError:
            continue
    return None


def parse_amount_to_number(value: str) -> float:
    text = clean_text(value)
    if not text:
        return 0.0
    match = re.search(r"([0-9]{1,3}(?:,[0-9]{3})*(?:\.\d{1,2})?|\d+(?:\.\d{1,2})?)", text)
    if not match:
        return 0.0
    try:
        return float(match.group(1).replace(",", ""))
    except ValueError:
        return 0.0


def split_owner_name(owner: str) -> Tuple[str, str]:
    owner_clean = clean_text(owner)
    if not owner_clean:
        return "", ""
    normalized = normalize_name(owner_clean)
    if any(
        marker in normalized
        for marker in ["LLC", "INC", "CORP", "CORPORATION", "TRUST", "ESTATE", "LP", "LLP", "LTD", "BANK"]
    ):
        return "", owner_clean
    if "," in owner_clean:
        last, _, rest = owner_clean.partition(",")
        first = rest.strip().split()[0] if rest.strip() else ""
        return first, clean_text(last)
    parts = owner_clean.split()
    if len(parts) == 1:
        return parts[0], ""
    return parts[0], parts[-1]


def name_variants(name: str) -> List[str]:
    raw = normalize_name(name)
    if not raw:
        return []
    variants = {raw}
    if "," in raw:
        last, _, rest = raw.partition(",")
        rest = normalize_spaces(rest)
        if rest:
            variants.add(normalize_spaces(f"{rest} {last}"))
            variants.add(normalize_spaces(f"{last} {rest.split()[0]}"))
    else:
        parts = raw.split()
        if len(parts) >= 2:
            first = parts[0]
            last = parts[-1]
            variants.add(normalize_spaces(f"{last} {first}"))
            variants.add(normalize_spaces(f"{last}, {first}"))
    return sorted(v for v in variants if v)


def extract_money(text: str) -> str:
    match = re.search(r"\$\s?[\d,]+(?:\.\d{2})?", text)
    return match.group(0) if match else ""


def extract_first_match(patterns: Sequence[str], text: str) -> str:
    for pattern in patterns:
        match = re.search(pattern, text, flags=re.I | re.S)
        if match:
            return clean_text(match.group(1))
    return ""


def dedupe_records(records: Iterable[LeadRecord]) -> List[LeadRecord]:
    seen = set()
    output: List[LeadRecord] = []
    for record in records:
        key = (
            clean_text(record.doc_num),
            clean_text(record.doc_type),
            clean_text(record.filed),
            normalize_name(record.owner),
            record.cat,
        )
        if key in seen:
            continue
        seen.add(key)
        output.append(record)
    return output


@retryable
def http_get(url: str, session: Optional[requests.Session] = None, **kwargs) -> requests.Response:
    sess = session or requests.Session()
    headers = kwargs.pop("headers", {})
    headers.setdefault("User-Agent", USER_AGENT)

    try:
        response = sess.get(url, timeout=REQUEST_TIMEOUT, headers=headers, **kwargs)
        response.raise_for_status()
        return response
    except requests.exceptions.SSLError:
        logger.warning("SSL verification failed for %s. Retrying without certificate verification.", url)
        response = sess.get(url, timeout=REQUEST_TIMEOUT, headers=headers, verify=False, **kwargs)
        response.raise_for_status()
        return response


def iter_zip_members(blob: bytes) -> List[Tuple[str, bytes]]:
    try:
        with zipfile.ZipFile(BytesIO(blob)) as zf:
            return [(info.filename, zf.read(info.filename)) for info in zf.infolist() if not info.is_dir()]
    except zipfile.BadZipFile:
        return [("download.bin", blob)]


def col_letters_to_index(col_ref: str) -> int:
    value = 0
    for char in col_ref:
        if "A" <= char <= "Z":
            value = value * 26 + (ord(char) - 64)
    return value - 1


def read_xlsx_shared_strings(zf: zipfile.ZipFile) -> List[str]:
    try:
        root = ET.fromstring(zf.read("xl/sharedStrings.xml"))
    except KeyError:
        return []
    ns = {"x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    strings = []
    for si in root.findall("x:si", ns):
        parts = [t.text or "" for t in si.findall(".//x:t", ns)]
        strings.append("".join(parts))
    return strings


def read_xlsx_rows(xlsx_bytes: bytes) -> Iterator[Dict[str, Any]]:
    with zipfile.ZipFile(BytesIO(xlsx_bytes)) as zf:
        shared_strings = read_xlsx_shared_strings(zf)
        workbook = ET.fromstring(zf.read("xl/workbook.xml"))
        ns = {
            "x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main",
            "r": "http://schemas.openxmlformats.org/officeDocument/2006/relationships",
        }

        sheets = workbook.find("x:sheets", ns)
        if sheets is None:
            return

        first_sheet_rel_id = None
        for sheet in sheets.findall("x:sheet", ns):
            first_sheet_rel_id = sheet.attrib.get("{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id")
            if first_sheet_rel_id:
                break
        if not first_sheet_rel_id:
            return

        rels = ET.fromstring(zf.read("xl/_rels/workbook.xml.rels"))
        rel_ns = {"r": "http://schemas.openxmlformats.org/package/2006/relationships"}
        target = None
        for rel in rels.findall("r:Relationship", rel_ns):
            if rel.attrib.get("Id") == first_sheet_rel_id:
                target = rel.attrib.get("Target")
                break
        if not target:
            return

        sheet_xml = ET.fromstring(zf.read("xl/" + target.lstrip("/")))
        rows = sheet_xml.findall(".//x:sheetData/x:row", ns)
        if not rows:
            return

        def cell_value(cell: ET.Element) -> str:
            cell_type = cell.attrib.get("t", "")
            value_el = cell.find("x:v", ns)
            if value_el is None:
                is_el = cell.find("x:is", ns)
                if is_el is not None:
                    return clean_text("".join(t.text or "" for t in is_el.findall(".//x:t", ns)))
                return ""
            raw = value_el.text or ""
            if cell_type == "s":
                try:
                    return clean_text(shared_strings[int(raw)])
                except Exception:
                    return clean_text(raw)
            return clean_text(raw)

        header_map: Dict[int, str] = {}
        for cell in rows[0].findall("x:c", ns):
            ref = cell.attrib.get("r", "")
            idx = col_letters_to_index(re.sub(r"\d+", "", ref))
            header_map[idx] = cell_value(cell)

        for row in rows[1:]:
            row_values = {}
            for cell in row.findall("x:c", ns):
                ref = cell.attrib.get("r", "")
                idx = col_letters_to_index(re.sub(r"\d+", "", ref))
                header = header_map.get(idx, f"COL_{idx}")
                row_values[header] = cell_value(cell)
            if row_values:
                yield row_values


def build_row_lookup(row: Dict[str, Any], aliases: Sequence[str]) -> str:
    normalized = {normalize_name(k): v for k, v in row.items()}
    for alias in aliases:
        alias_norm = normalize_name(alias)
        for key, value in normalized.items():
            if alias_norm == key or alias_norm in key:
                return clean_text(value)
    return ""


def download_property_bulk_data(url: str) -> Optional[bytes]:
    if not url:
        logger.warning("PROPERTY_APPRAISER_BULK_DATA_URL is blank. Parcel enrichment skipped.")
        return None
    response = http_get(url, allow_redirects=True)
    return response.content


def build_parcel_index() -> Dict[str, Dict[str, str]]:
    parcel_index: Dict[str, Dict[str, str]] = {}
    blob = download_property_bulk_data(PROPERTY_APPRAISER_BULK_DATA_URL)
    if not blob:
        return parcel_index

    members = iter_zip_members(blob)
    found_xlsx = False

    for name, data in members:
        if not name.lower().endswith(".xlsx"):
            continue
        found_xlsx = True
        logger.info("Using parcel XLSX: %s", name)
        for row in read_xlsx_rows(data):
            try:
                owner = build_row_lookup(row, ["OWNER", "OWN1", "OWNER_NAME", "OWNNAME"])
                if not owner:
                    continue

                payload = {
                    "owner": owner,
                    "prop_address": build_row_lookup(row, ["SITE_ADDR", "SITEADDR", "SITUSADDR", "PROPERTY_ADDRESS"]),
                    "prop_city": build_row_lookup(row, ["SITE_CITY", "SITECITY", "PROP_CITY", "CITY"]),
                    "prop_state": "GA",
                    "prop_zip": build_row_lookup(row, ["SITE_ZIP", "SITEZIP", "PROP_ZIP", "ZIP"]),
                    "mail_address": build_row_lookup(row, ["ADDR_1", "MAILADR1", "MAIL_ADDR", "MAILADDR1"]),
                    "mail_city": build_row_lookup(row, ["MAILCITY", "MAIL_CITY"]),
                    "mail_state": build_row_lookup(row, ["MAILSTATE", "MAIL_STATE", "STATE"]) or "GA",
                    "mail_zip": build_row_lookup(row, ["MAILZIP", "MAIL_ZIP", "ZIP"]),
                }

                for variant in name_variants(owner):
                    parcel_index.setdefault(variant, payload)
            except Exception as exc:
                logger.warning("Skipping bad parcel row: %s", exc)

    if not found_xlsx:
        logger.warning("No XLSX files found in parcel download")

    logger.info("Indexed parcel owner keys: %s", len(parcel_index))
    return parcel_index


async def click_first_matching(page: Page, texts: Sequence[str]) -> bool:
    for text in texts:
        try:
            button = page.get_by_role("button", name=re.compile(text, re.I))
            if await button.count() > 0:
                await button.first.click()
                return True
        except Exception:
            pass
        try:
            link = page.get_by_role("link", name=re.compile(text, re.I))
            if await link.count() > 0:
                await link.first.click()
                return True
        except Exception:
            pass
    return False


async def fill_first_text_input(page: Page, value: str) -> bool:
    selectors = [
        "input[type='search']",
        "input[name*='search' i]",
        "input[id*='search' i]",
        "input[type='text']",
        "input:not([type])",
    ]
    for selector in selectors:
        try:
            locator = page.locator(selector)
            count = await locator.count()
            if count > 0:
                await locator.first.fill(value)
                return True
        except Exception:
            continue
    return False


def classify_notice(text: str, fallback_cat: str) -> Tuple[str, str]:
    blob = text.upper()

    if "LIS PENDENS" in blob:
        return "LP", CATEGORY_LABELS["LP"]
    if "FORECLOSURE" in blob:
        return "NOFC", CATEGORY_LABELS["NOFC"]
    if "TAX SALE" in blob or "TAX DEED" in blob or "TAX EXECUTION" in blob:
        return "TAXDEED", CATEGORY_LABELS["TAXDEED"]
    if "MECHANIC LIEN" in blob or "MATERIALMEN" in blob:
        return "LNMECH", CATEGORY_LABELS["LNMECH"]
    if "HOMEOWNERS ASSOCIATION" in blob or "HOA" in blob:
        return "LNHOA", CATEGORY_LABELS["LNHOA"]
    if "PROBATE" in blob or "ESTATE" in blob or "DECEASED" in blob or "EXECUTOR" in blob or "ADMINISTRATOR" in blob:
        return "PRO", CATEGORY_LABELS["PRO"]
    if "JUDGMENT" in blob:
        return "JUD", CATEGORY_LABELS["JUD"]
    if "LIEN" in blob:
        return "LN", CATEGORY_LABELS["LN"]

    return fallback_cat, CATEGORY_LABELS.get(fallback_cat, fallback_cat)


def parse_notice_text_to_record(text: str, url: str, fallback_cat: str) -> RawRecord:
    full_text = clean_text(text)
    cat, cat_label = classify_notice(full_text, fallback_cat)

    owner = extract_first_match(
        [
            r"(?:grantor|owner|defendant|decedent|estate of)\s*[:\-]\s*([A-Z0-9 ,.'&\-]+)",
            r"(?:estate of)\s+([A-Z][A-Z0-9 ,.'&\-]{4,})",
            r"(?:against)\s+([A-Z][A-Z0-9 ,.'&\-]{4,})",
        ],
        full_text,
    )

    grantee = extract_first_match(
        [
            r"(?:grantee|plaintiff|claimant|creditor|secured creditor)\s*[:\-]\s*([A-Z0-9 ,.'&\-]+)",
        ],
        full_text,
    )

    legal = extract_first_match(
        [
            r"(?:property address|premises known as)\s*[:\-]?\s*([0-9A-Z ,.#'\-]+(?:GA|Georgia)\s+\d{5})",
            r"(?:address)\s*[:\-]\s*([0-9A-Z ,.#'\-]{10,})",
        ],
        full_text,
    )

    filed = extract_first_match(
        [
            r"(?:date filed|filed|recorded|publication date)\s*[:\-]?\s*([0-9]{1,2}/[0-9]{1,2}/[0-9]{2,4})",
            r"([A-Z][a-z]+ \d{1,2}, \d{4})",
        ],
        full_text,
    )

    doc_num = extract_first_match(
        [
            r"(?:document no\.?|doc(?:ument)? no\.?|instrument no\.?|case no\.?|civil action no\.?)\s*[:\-]?\s*([A-Z0-9\-]+)",
            r"(book\s*\d+\s*page\s*\d+)",
        ],
        full_text,
    )

    amount = extract_money(full_text)

    if not owner:
        people_like = re.findall(r"\b[A-Z][A-Z ,.'&\-]{5,}\b", full_text)
        owner = clean_text(people_like[0]) if people_like else ""

    return RawRecord(
        doc_num=doc_num,
        doc_type=CATEGORY_LABELS.get(cat, cat_label),
        filed=filed,
        cat=cat,
        cat_label=cat_label,
        owner=owner,
        grantee=grantee,
        amount=amount,
        legal=legal,
        clerk_url=url,
        notice_text=full_text,
    )


async def scrape_notice_detail_text(context: BrowserContext, detail_url: str) -> str:
    detail_page = await context.new_page()
    try:
        await detail_page.goto(detail_url, wait_until="domcontentloaded", timeout=REQUEST_TIMEOUT * 1000)
        try:
            await detail_page.wait_for_load_state("networkidle", timeout=3000)
        except Exception:
            pass
        html = await detail_page.content()
        soup = BeautifulSoup(html, "lxml")
        return clean_text(soup.get_text(" ", strip=True))
    finally:
        await detail_page.close()


def collect_candidate_links_from_html(html: str, base_url: str) -> List[str]:
    soup = BeautifulSoup(html, "lxml")
    links: List[str] = []

    for a in soup.find_all("a", href=True):
        href = clean_text(a.get("href"))
        text = clean_text(a.get_text(" ", strip=True))
        full = urljoin(base_url, href)
        blob = f"{href} {text}".upper()

        if (
            "DETAIL" in blob
            or "NOTICE" in blob
            or "PUBLICNOTICE" in blob
            or "VIEW" in blob
        ):
            links.append(full)

    deduped: List[str] = []
    seen = set()
    for link in links:
        if link in seen:
            continue
        seen.add(link)
        deduped.append(link)

    return deduped[:MAX_DETAIL_LINKS_PER_SEARCH]


async def scrape_public_notice_search(
    page: Page,
    context: BrowserContext,
    category_code: str,
    search_term: str,
    from_date: str,
    to_date: str,
    remaining_detail_budget: int,
) -> Tuple[List[RawRecord], int]:
    records: List[RawRecord] = []

    logger.info("Searching public notice term=%s cat=%s", search_term, category_code)

    await page.goto(PUBLIC_NOTICE_URL, wait_until="domcontentloaded", timeout=REQUEST_TIMEOUT * 1000)
    await page.wait_for_timeout(1000)

    filled = await fill_first_text_input(page, search_term)
    if not filled:
        logger.warning("Could not locate search input for term=%s", search_term)
        return records, remaining_detail_budget

    clicked = await click_first_matching(page, ["Search"])
    if not clicked:
        logger.warning("Could not click search for term=%s", search_term)
        return records, remaining_detail_budget

    try:
        await page.wait_for_load_state("networkidle", timeout=PER_SEARCH_TIMEOUT_MS)
    except PlaywrightTimeoutError:
        logger.warning("Timed out waiting for search results for term=%s", search_term)

    await page.wait_for_timeout(PAGE_WAIT_MS)

    current_page = 1
    while True:
        html = await page.content()
        candidate_links = collect_candidate_links_from_html(html, page.url)

        if not candidate_links:
            logger.info("No candidate links found for term=%s page=%s", search_term, current_page)

        for detail_url in candidate_links:
            if remaining_detail_budget <= 0:
                logger.warning("Detail page budget exhausted")
                return records, remaining_detail_budget

            remaining_detail_budget -= 1

            try:
                detail_text = await scrape_notice_detail_text(context, detail_url)
                if TARGET_COUNTY.upper() not in detail_text.upper() and "GWINNETT" not in detail_text.upper():
                    continue

                record = parse_notice_text_to_record(detail_text, detail_url, category_code)

                from_dt = parse_date_text(from_date)
                to_dt = parse_date_text(to_date)
                filed_dt = parse_date_text(record.filed)

                if filed_dt and from_dt and to_dt and not (from_dt <= filed_dt <= to_dt):
                    continue

                records.append(record)
            except Exception as exc:
                logger.warning("Skipping detail page %s: %s", detail_url, exc)

        logger.info(
            "term=%s page=%s yielded cumulative %s records",
            search_term,
            current_page,
            len(records),
        )

        if current_page >= MAX_RESULTS_PAGES:
            break

        moved = await click_first_matching(page, ["Next"])
        if not moved:
            break

        try:
            await page.wait_for_load_state("networkidle", timeout=PER_SEARCH_TIMEOUT_MS)
        except Exception:
            pass
        await page.wait_for_timeout(PAGE_WAIT_MS)
        current_page += 1

    return records, remaining_detail_budget


async def scrape_public_notices(from_date: str, to_date: str) -> List[RawRecord]:
    all_records: List[RawRecord] = []
    seen = set()
    remaining_detail_budget = MAX_DETAIL_PAGES_TOTAL

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=HEADLESS)
        context: BrowserContext = await browser.new_context(user_agent=USER_AGENT)
        page = await context.new_page()

        for cat_code, term in SEARCH_TERMS:
            try:
                rows, remaining_detail_budget = await scrape_public_notice_search(
                    page=page,
                    context=context,
                    category_code=cat_code,
                    search_term=term,
                    from_date=from_date,
                    to_date=to_date,
                    remaining_detail_budget=remaining_detail_budget,
                )

                for row in rows:
                    key = (
                        clean_text(row.doc_num),
                        clean_text(row.filed),
                        normalize_name(row.owner),
                        row.cat,
                        clean_text(row.clerk_url),
                    )
                    if key in seen:
                        continue
                    seen.add(key)
                    all_records.append(row)

                if remaining_detail_budget <= 0:
                    logger.warning("Stopping early due to detail page budget limit")
                    break
            except Exception as exc:
                logger.warning("Search failed for %s / %s: %s", cat_code, term, exc)

        await context.close()
        await browser.close()

    logger.info("Scraped %s raw records before enrichment/dedupe", len(all_records))
    return all_records


def lookup_parcel(owner: str, parcel_index: Dict[str, Dict[str, str]]) -> Dict[str, str]:
    for variant in name_variants(owner):
        if variant in parcel_index:
            return parcel_index[variant]
    return {}


def flags_for_record(record: LeadRecord, lookback_cutoff: date) -> List[str]:
    flags: List[str] = []
    cat = record.cat.upper()
    owner_norm = normalize_name(record.owner)
    blob = f"{record.doc_type} {record.notice_text}".upper()

    if cat == "LP":
        flags.append("Lis pendens")
    if cat == "NOFC":
        flags.append("Pre-foreclosure")
    if cat in {"JUD", "CCJ", "DRJUD"}:
        flags.append("Judgment lien")
    if "TAX" in blob:
        flags.append("Tax lien")
    if cat == "LNMECH":
        flags.append("Mechanic lien")
    if cat == "PRO":
        flags.append("Probate / estate")

    if any(marker in owner_norm for marker in ["LLC", "INC", "CORP", "CORPORATION", "LLP", "LP", "TRUST", "HOLDINGS"]):
        flags.append("LLC / corp owner")

    filed_date = parse_date_text(record.filed)
    if filed_date and filed_date >= lookback_cutoff:
        flags.append("New this week")

    return sorted(set(flags))


def score_record(record: LeadRecord) -> int:
    score = 30
    score += sum(FLAG_POINTS.get(flag, 0) for flag in record.flags)

    if "Lis pendens" in record.flags and "Pre-foreclosure" in record.flags:
        score += 20

    amount_value = parse_amount_to_number(record.amount)
    if amount_value > 100000:
        score += 15
    elif amount_value > 50000:
        score += 10

    if record.prop_address:
        score += 5

    return min(score, 100)


def enrich_records(
    raw_records: List[RawRecord],
    parcel_index: Dict[str, Dict[str, str]],
    lookback_cutoff: date,
) -> List[LeadRecord]:
    enriched: List[LeadRecord] = []
    for raw in raw_records:
        try:
            parcel = lookup_parcel(raw.owner, parcel_index)
            lead = LeadRecord(
                **asdict(raw),
                prop_address=parcel.get("prop_address", ""),
                prop_city=parcel.get("prop_city", ""),
                prop_state=parcel.get("prop_state", "GA" if parcel else ""),
                prop_zip=parcel.get("prop_zip", ""),
                mail_address=parcel.get("mail_address", ""),
                mail_city=parcel.get("mail_city", ""),
                mail_state=parcel.get("mail_state", "GA" if parcel else ""),
                mail_zip=parcel.get("mail_zip", ""),
            )
            lead.flags = flags_for_record(lead, lookback_cutoff)
            lead.score = score_record(lead)
            enriched.append(lead)
        except Exception as exc:
            logger.warning("Skipping bad enriched row: %s", exc)

    return dedupe_records(enriched)


def build_json_payload(records: List[LeadRecord], from_date: str, to_date: str) -> Dict[str, Any]:
    return {
        "fetched_at": datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "source": "Georgia Public Notice + Gwinnett Ownership Data",
        "date_range": {"from": from_date, "to": to_date, "lookback_days": LOOKBACK_DAYS},
        "total": len(records),
        "with_address": sum(1 for r in records if r.prop_address),
        "records": [
            {
                "doc_num": r.doc_num,
                "doc_type": r.doc_type,
                "filed": r.filed,
                "cat": r.cat,
                "cat_label": r.cat_label,
                "owner": r.owner,
                "grantee": r.grantee,
                "amount": r.amount,
                "legal": r.legal,
                "prop_address": r.prop_address,
                "prop_city": r.prop_city,
                "prop_state": r.prop_state,
                "prop_zip": r.prop_zip,
                "mail_address": r.mail_address,
                "mail_city": r.mail_city,
                "mail_state": r.mail_state,
                "mail_zip": r.mail_zip,
                "clerk_url": r.clerk_url,
                "flags": r.flags,
                "score": r.score,
            }
            for r in records
        ],
    }


def write_json_outputs(payload: Dict[str, Any]) -> None:
    serialized = json.dumps(payload, indent=2, ensure_ascii=False)
    (DATA_DIR / "records.json").write_text(serialized, encoding="utf-8")
    (DASHBOARD_DIR / "records.json").write_text(serialized, encoding="utf-8")
    logger.info("Wrote JSON outputs")


def write_ghl_export(records: List[LeadRecord]) -> None:
    export_path = DATA_DIR / "ghl_export.csv"
    fieldnames = [
        "First Name",
        "Last Name",
        "Mailing Address",
        "Mailing City",
        "Mailing State",
        "Mailing Zip",
        "Property Address",
        "Property City",
        "Property State",
        "Property Zip",
        "Lead Type",
        "Document Type",
        "Date Filed",
        "Document Number",
        "Amount/Debt Owed",
        "Seller Score",
        "Motivated Seller Flags",
        "Source",
        "Public Records URL",
    ]

    with export_path.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames)
        writer.writeheader()

        for record in records:
            first_name, last_name = split_owner_name(record.owner)
            writer.writerow(
                {
                    "First Name": first_name,
                    "Last Name": last_name,
                    "Mailing Address": record.mail_address,
                    "Mailing City": record.mail_city,
                    "Mailing State": record.mail_state,
                    "Mailing Zip": record.mail_zip,
                    "Property Address": record.prop_address,
                    "Property City": record.prop_city,
                    "Property State": record.prop_state,
                    "Property Zip": record.prop_zip,
                    "Lead Type": record.cat_label,
                    "Document Type": record.doc_type,
                    "Date Filed": record.filed,
                    "Document Number": record.doc_num,
                    "Amount/Debt Owed": record.amount,
                    "Seller Score": record.score,
                    "Motivated Seller Flags": "; ".join(record.flags),
                    "Source": "Georgia Public Notice",
                    "Public Records URL": record.clerk_url,
                }
            )

    logger.info("Wrote %s", export_path)


async def async_main() -> int:
    setup_logging()
    ensure_dirs()
    write_initial_empty_records()

    today = datetime.utcnow().date()
    from_dt = today - timedelta(days=LOOKBACK_DAYS)
    from_date = from_dt.strftime("%m/%d/%Y")
    to_date = today.strftime("%m/%d/%Y")

    logger.info("============================================================")
    logger.info("Gwinnett Motivated Seller Scraper")
    logger.info("Notice source      : %s", PUBLIC_NOTICE_URL)
    logger.info("Parcel bulk url    : %s", PROPERTY_APPRAISER_BULK_DATA_URL or "<not provided>")
    logger.info("County             : %s", TARGET_COUNTY)
    logger.info("Range              : %s -> %s (%s days)", from_date, to_date, LOOKBACK_DAYS)
    logger.info("Search terms       : %s", ", ".join(f"{cat}:{term}" for cat, term in SEARCH_TERMS))
    logger.info("Max result pages   : %s", MAX_RESULTS_PAGES)
    logger.info("Max detail/search  : %s", MAX_DETAIL_LINKS_PER_SEARCH)
    logger.info("Max detail total   : %s", MAX_DETAIL_PAGES_TOTAL)
    logger.info("============================================================")

    parcel_index: Dict[str, Dict[str, str]] = {}
    try:
        parcel_index = build_parcel_index()
    except Exception as exc:
        logger.exception("Parcel enrichment failed. Continuing without parcel data: %s", exc)

    raw_records = await scrape_public_notices(from_date, to_date)
    lookback_cutoff = today - timedelta(days=7)
    records = enrich_records(raw_records, parcel_index, lookback_cutoff)

    records.sort(
        key=lambda r: (r.score, parse_date_text(r.filed) or date.min, normalize_name(r.owner)),
        reverse=True,
    )

    payload = build_json_payload(records, from_date, to_date)
    write_json_outputs(payload)
    write_ghl_export(records)

    logger.info("Done. Total leads: %s | With address: %s", payload["total"], payload["with_address"])
    return 0


def main() -> int:
    try:
        return asyncio.run(async_main())
    except KeyboardInterrupt:
        logger.warning("Interrupted by user")
        return 130
    except Exception as exc:
        logger.exception("Fatal error: %s", exc)
        ensure_dirs()
        write_initial_empty_records()
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
