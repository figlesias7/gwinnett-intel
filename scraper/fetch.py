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
import zipfile
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, timedelta
from io import BytesIO
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup
from dbfread import DBF
from playwright.async_api import BrowserContext, Page, async_playwright


# -----------------------------
# Configuration
# -----------------------------
BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DASHBOARD_DIR = BASE_DIR / "dashboard"
TMP_DIR = BASE_DIR / ".tmp"
LOG_DIR = BASE_DIR / ".logs"

CLERK_PORTAL_URL = os.getenv(
    "CLERK_PORTAL_URL",
    "https://www.gwinnettcourts.com/deeds-and-land-records/",
)
PROPERTY_APPRAISER_BULK_DATA_URL = os.getenv(
    "PROPERTY_APPRAISER_BULK_DATA_URL",
    "",
).strip()
LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "7"))
REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "60"))
MAX_RETRIES = 3
USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

GSCCCA_REAL_ESTATE_URL = os.getenv(
    "GSCCCA_REAL_ESTATE_URL",
    "https://search.gsccca.org/RealEstate/namesearch.asp",
)
GSCCCA_LIEN_URL = os.getenv(
    "GSCCCA_LIEN_URL",
    "https://search.gsccca.org/Lien/namesearch.asp",
)

HEADLESS = os.getenv("HEADLESS", "true").lower() != "false"


@dataclass
class CategoryConfig:
    cat: str
    cat_label: str
    source_kind: str  # lien | realestate
    instrument_label: str


CATEGORY_CONFIGS: List[CategoryConfig] = [
    CategoryConfig("LP", "Lis Pendens", "lien", "Lis Pendens"),
    CategoryConfig("NOFC", "Notice of Foreclosure", "realestate", "DEED - FORECLOSURE"),
    CategoryConfig("TAXDEED", "Tax Deed", "realestate", "TAX SALE DEED"),
    CategoryConfig("JUD", "Judgment", "lien", "FIFA"),
    CategoryConfig("CCJ", "Certified Judgment", "lien", "ORDER"),
    CategoryConfig("DRJUD", "Domestic Judgment", "lien", "ORDER"),
    CategoryConfig("LNCORPTX", "Corporate Tax Lien", "lien", "Lien"),
    CategoryConfig("LNIRS", "IRS Lien", "lien", "Federal Tax Lien"),
    CategoryConfig("LNFED", "Federal Lien", "lien", "Federal Tax Lien"),
    CategoryConfig("LN", "Lien", "lien", "Lien"),
    CategoryConfig("LNMECH", "Mechanic Lien", "lien", "Mechanics and Materialmens Lien"),
    CategoryConfig("LNHOA", "HOA Lien", "lien", "Lien"),
    CategoryConfig("MEDLN", "Medicaid Lien", "lien", "Lien"),
    CategoryConfig("PRO", "Probate / Estate", "realestate", "ESTATE DOCUMENTATION"),
    CategoryConfig("NOC", "Notice of Commencement", "lien", "Notice"),
    CategoryConfig("RELLP", "Release Lis Pendens", "lien", "Release"),
]

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


# -----------------------------
# Models
# -----------------------------
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


# -----------------------------
# Logging
# -----------------------------
def setup_logging() -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_file = LOG_DIR / "fetch.log"
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s  %(levelname)-8s %(message)s",
        handlers=[
            logging.StreamHandler(sys.stdout),
            logging.FileHandler(log_file, encoding="utf-8"),
        ],
    )


logger = logging.getLogger("gwinnett_scraper")


# -----------------------------
# Helpers
# -----------------------------
def ensure_dirs() -> None:
    for path in [DATA_DIR, DASHBOARD_DIR, TMP_DIR, LOG_DIR]:
        path.mkdir(parents=True, exist_ok=True)


def retryable(fn):
    def wrapper(*args, **kwargs):
        last_exc: Optional[Exception] = None
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                return fn(*args, **kwargs)
            except Exception as exc:  # noqa: BLE001
                last_exc = exc
                logger.warning("Attempt %s/%s failed for %s: %s", attempt, MAX_RETRIES, fn.__name__, exc)
                if attempt < MAX_RETRIES:
                    time.sleep(min(attempt * 2, 5))
        assert last_exc is not None
        raise last_exc

    return wrapper


def retryable_async(fn):
    async def wrapper(*args, **kwargs):
        last_exc: Optional[Exception] = None
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                return await fn(*args, **kwargs)
            except Exception as exc:  # noqa: BLE001
                last_exc = exc
                logger.warning("Attempt %s/%s failed for %s: %s", attempt, MAX_RETRIES, fn.__name__, exc)
                if attempt < MAX_RETRIES:
                    await asyncio.sleep(min(attempt * 2, 5))
        assert last_exc is not None
        raise last_exc

    return wrapper


def clean_text(value: Any) -> str:
    if value is None:
        return ""
    text = str(value)
    text = re.sub(r"\s+", " ", text.replace("\xa0", " ")).strip()
    return text


def normalize_spaces(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def parse_amount_to_number(value: str) -> float:
    if not value:
        return 0.0
    text = clean_text(value)
    match = re.search(r"\$?\s*([0-9]{1,3}(?:,[0-9]{3})*(?:\.\d{1,2})?|\d+(?:\.\d{1,2})?)", text)
    if not match:
        return 0.0
    try:
        return float(match.group(1).replace(",", ""))
    except ValueError:
        return 0.0


def parse_date_text(value: str) -> Optional[date]:
    text = clean_text(value)
    if not text:
        return None
    patterns = ["%m/%d/%Y", "%m/%d/%y", "%Y-%m-%d", "%B %d, %Y", "%b %d, %Y"]
    for pattern in patterns:
        try:
            return datetime.strptime(text, pattern).date()
        except ValueError:
            continue
    return None


def normalize_name(name: str) -> str:
    name = clean_text(name).upper()
    name = name.replace("&", " AND ")
    name = re.sub(r"[^A-Z0-9, ]+", " ", name)
    name = normalize_spaces(name)
    return name


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
            first_token = rest.split()[0]
            variants.add(normalize_spaces(f"{last} {first_token}"))
    else:
        parts = raw.split()
        if len(parts) >= 2:
            first = parts[0]
            last = parts[-1]
            middle = " ".join(parts[1:-1]).strip()
            variants.add(normalize_spaces(f"{last} {first}"))
            variants.add(normalize_spaces(f"{last}, {first}"))
            if middle:
                variants.add(normalize_spaces(f"{last}, {first} {middle}"))

    return sorted(v for v in variants if v)


def split_owner_name(owner: str) -> Tuple[str, str]:
    owner_clean = clean_text(owner)
    if not owner_clean:
        return "", ""

    normalized = normalize_name(owner_clean)
    business_markers = [
        "LLC",
        "INC",
        "CORP",
        "CORPORATION",
        "COMPANY",
        "TRUST",
        "ESTATE",
        "LP",
        "LLP",
        "LTD",
        "BANK",
        "HOLDINGS",
    ]
    if any(marker in normalized for marker in business_markers):
        return "", owner_clean

    if "," in owner_clean:
        last, _, rest = owner_clean.partition(",")
        first = rest.strip().split()[0] if rest.strip() else ""
        return first, clean_text(last)

    parts = owner_clean.split()
    if len(parts) == 1:
        return parts[0], ""
    return parts[0], parts[-1]


def extract_best(headers: Sequence[str], row: Dict[str, str], candidates: Sequence[str]) -> str:
    header_map = {normalize_name(h): h for h in headers}
    for candidate in candidates:
        candidate_key = normalize_name(candidate)
        for header_norm, original_header in header_map.items():
            if candidate_key == header_norm or candidate_key in header_norm:
                return clean_text(row.get(original_header, ""))
    return ""


def dedupe_records(records: Iterable[LeadRecord]) -> List[LeadRecord]:
    seen: set[Tuple[str, str, str, str]] = set()
    output: List[LeadRecord] = []
    for record in records:
        key = (
            clean_text(record.doc_num),
            clean_text(record.doc_type),
            clean_text(record.filed),
            normalize_name(record.owner),
        )
        if key in seen:
            continue
        seen.add(key)
        output.append(record)
    return output


# -----------------------------
# HTTP
# -----------------------------
@retryable
def http_get(url: str, session: Optional[requests.Session] = None, **kwargs) -> requests.Response:
    sess = session or requests.Session()
    headers = kwargs.pop("headers", {})
    headers.setdefault("User-Agent", USER_AGENT)
    response = sess.get(url, timeout=REQUEST_TIMEOUT, headers=headers, **kwargs)
    response.raise_for_status()
    return response


@retryable
def http_post(url: str, session: requests.Session, data: Dict[str, Any], **kwargs) -> requests.Response:
    headers = kwargs.pop("headers", {})
    headers.setdefault("User-Agent", USER_AGENT)
    response = session.post(url, timeout=REQUEST_TIMEOUT, headers=headers, data=data, **kwargs)
    response.raise_for_status()
    return response


# -----------------------------
# Parcel data
# -----------------------------
def build_row_lookup(row: Dict[str, Any], aliases: Sequence[str]) -> str:
    normalized = {normalize_name(k): v for k, v in row.items()}
    for alias in aliases:
        alias_norm = normalize_name(alias)
        if alias_norm in normalized:
            return clean_text(normalized[alias_norm])
    return ""


@retryable
def download_property_bulk_data(url: str) -> Optional[bytes]:
    if not url:
        logger.warning("PROPERTY_APPRAISER_BULK_DATA_URL is blank. Parcel enrichment will be skipped.")
        return None

    session = requests.Session()
    response = http_get(url, session=session)
    content_type = response.headers.get("content-type", "")
    final_url = response.url

    if any(token in content_type.lower() for token in ["application/zip", "application/octet-stream", "application/x-zip-compressed"]):
        return response.content

    if final_url.lower().endswith((".zip", ".dbf")):
        return response.content

    soup = BeautifulSoup(response.text, "lxml")

    # Direct downloadable link first.
    for anchor in soup.find_all("a", href=True):
        href = clean_text(anchor["href"])
        lower = href.lower()
        if any(ext in lower for ext in [".zip", ".dbf", ".xlsx"]):
            file_url = urljoin(final_url, href)
            logger.info("Following direct parcel download link: %s", file_url)
            return http_get(file_url, session=session).content

    # ASP.NET __doPostBack fallback.
    postback_anchor = soup.find("a", href=re.compile(r"__doPostBack\(", re.I))
    if postback_anchor:
        href = postback_anchor.get("href", "")
        match = re.search(r"__doPostBack\('([^']*)','([^']*)'\)", href)
        if match:
            event_target, event_argument = match.groups()
            form = postback_anchor.find_parent("form") or soup.find("form")
            if form:
                payload: Dict[str, str] = {}
                for inp in form.find_all(["input", "select", "textarea"]):
                    name = inp.get("name")
                    if not name:
                        continue
                    payload[name] = inp.get("value", "")
                payload["__EVENTTARGET"] = event_target
                payload["__EVENTARGUMENT"] = event_argument
                post_url = urljoin(final_url, form.get("action") or final_url)
                logger.info("Triggering ASP.NET parcel download via __doPostBack: %s", event_target)
                file_response = http_post(post_url, session=session, data=payload)
                return file_response.content

    logger.warning("Could not detect a downloadable parcel file from %s", url)
    return None


def iter_zip_members(blob: bytes) -> List[Tuple[str, bytes]]:
    try:
        with zipfile.ZipFile(BytesIO(blob)) as zf:
            members: List[Tuple[str, bytes]] = []
            for info in zf.infolist():
                if info.is_dir():
                    continue
                members.append((info.filename, zf.read(info.filename)))
            return members
    except zipfile.BadZipFile:
        return [("download.bin", blob)]



def build_parcel_index() -> Dict[str, Dict[str, str]]:
    parcel_index: Dict[str, Dict[str, str]] = {}
    blob = download_property_bulk_data(PROPERTY_APPRAISER_BULK_DATA_URL)
    if not blob:
        return parcel_index

    members = iter_zip_members(blob)
    dbf_members = [(name, data) for name, data in members if name.lower().endswith(".dbf")]

    if not dbf_members:
        logger.warning("No DBF file found in parcel download. Enrichment skipped.")
        return parcel_index

    dbf_path = TMP_DIR / Path(dbf_members[0][0]).name
    dbf_path.write_bytes(dbf_members[0][1])
    logger.info("Building parcel owner index from %s", dbf_path.name)

    for row in DBF(str(dbf_path), load=True, ignore_missing_memofile=True, char_decode_errors="ignore"):
        try:
            row_map = dict(row)
            owner = build_row_lookup(row_map, ["OWNER", "OWN1", "OWNER_NAME", "OWNNAME"])
            if not owner:
                continue

            site_addr = build_row_lookup(row_map, ["SITE_ADDR", "SITEADDR", "SITUSADDR", "PROPADDR"])
            site_city = build_row_lookup(row_map, ["SITE_CITY", "SITECITY", "CITY"])
            site_zip = build_row_lookup(row_map, ["SITE_ZIP", "SITEZIP", "ZIP"])
            mail_addr = build_row_lookup(row_map, ["ADDR_1", "MAILADR1", "MAIL_ADDR", "MAILADDR1"])
            mail_city = build_row_lookup(row_map, ["CITY", "MAILCITY", "MAIL_CITY"])
            mail_state = build_row_lookup(row_map, ["STATE", "MAILSTATE", "MAIL_STATE"])
            mail_zip = build_row_lookup(row_map, ["ZIP", "MAILZIP", "MAIL_ZIP"])

            payload = {
                "owner": owner,
                "prop_address": site_addr,
                "prop_city": site_city,
                "prop_state": "GA",
                "prop_zip": site_zip,
                "mail_address": mail_addr,
                "mail_city": mail_city,
                "mail_state": mail_state or "GA",
                "mail_zip": mail_zip,
            }

            for variant in name_variants(owner):
                parcel_index.setdefault(variant, payload)
        except Exception as exc:  # noqa: BLE001
            logger.warning("Skipping bad parcel row: %s", exc)
            continue

    logger.info("Parcel owner index contains %s keys", len(parcel_index))
    return parcel_index


# -----------------------------
# Playwright search helpers
# -----------------------------
async def safe_select_option_by_text(select_locator, option_text: str) -> bool:
    try:
        options = await select_locator.locator("option").all()
        values: List[Tuple[str, str]] = []
        for option in options:
            text = clean_text(await option.text_content())
            value = clean_text(await option.get_attribute("value"))
            values.append((text, value))
        for text, value in values:
            if text.upper() == option_text.upper() or option_text.upper() in text.upper():
                await select_locator.select_option(value=value)
                return True
    except Exception:  # noqa: BLE001
        return False
    return False


async def find_select_with_option(page: Page, option_text: str) -> Optional[Any]:
    selects = await page.locator("select").all()
    for select in selects:
        try:
            if await safe_select_option_by_text(select, option_text):
                return select
        except Exception:  # noqa: BLE001
            continue
    return None


async def set_date_range_fields(page: Page, from_date: str, to_date: str) -> None:
    inputs = await page.locator("input[type='text'], input:not([type])").all()
    date_inputs = []
    for inp in inputs:
        try:
            name = (await inp.get_attribute("name")) or ""
            value = (await inp.input_value()) or ""
            aria = (await inp.get_attribute("aria-label")) or ""
            blob = " ".join([name, value, aria]).lower()
            if "date" in blob or re.search(r"\d{1,2}/\d{1,2}/\d{2,4}", value):
                date_inputs.append(inp)
        except Exception:  # noqa: BLE001
            continue

    if len(date_inputs) >= 2:
        await date_inputs[0].fill(from_date)
        await date_inputs[1].fill(to_date)
        return

    # Fallback: just fill the first two visible text inputs.
    visible_texts = []
    for inp in inputs:
        try:
            if await inp.is_visible():
                visible_texts.append(inp)
        except Exception:  # noqa: BLE001
            continue
    if len(visible_texts) >= 2:
        await visible_texts[0].fill(from_date)
        await visible_texts[1].fill(to_date)


async def set_results_per_page(page: Page) -> None:
    selects = await page.locator("select").all()
    for select in selects:
        try:
            options = await select.locator("option").all()
            texts = [clean_text(await option.text_content()) for option in options]
            if {"5", "10", "25", "50", "75", "100"}.issubset(set(texts)) or "100" in texts:
                await safe_select_option_by_text(select, "100")
                return
        except Exception:  # noqa: BLE001
            continue


async def click_search(page: Page) -> None:
    candidates = [
        page.get_by_role("button", name=re.compile("search", re.I)),
        page.get_by_role("link", name=re.compile("search", re.I)),
        page.locator("input[type='submit']"),
        page.locator("button[type='submit']"),
    ]
    for candidate in candidates:
        try:
            if await candidate.count() > 0:
                await candidate.first.click()
                return
        except Exception:  # noqa: BLE001
            continue
    raise RuntimeError("Unable to locate search submit control")


async def next_page(page: Page) -> bool:
    locators = [
        page.get_by_role("link", name=re.compile(r"^next$", re.I)),
        page.get_by_text(re.compile(r"^next$", re.I)),
        page.locator("a", has_text="Next"),
    ]
    for locator in locators:
        try:
            if await locator.count() > 0 and await locator.first.is_visible():
                href = await locator.first.get_attribute("href")
                disabled = (await locator.first.get_attribute("class")) or ""
                if "disabled" in disabled.lower() or href in [None, "", "#"]:
                    continue
                await locator.first.click()
                await page.wait_for_load_state("networkidle")
                return True
        except Exception:  # noqa: BLE001
            continue
    return False


# -----------------------------
# Result parsing
# -----------------------------
def parse_result_tables(html: str, base_url: str, category: CategoryConfig) -> List[RawRecord]:
    soup = BeautifulSoup(html, "lxml")
    parsed: List[RawRecord] = []

    for table in soup.find_all("table"):
        rows = table.find_all("tr")
        if len(rows) < 2:
            continue

        header_cells = rows[0].find_all(["th", "td"])
        headers = [clean_text(cell.get_text(" ", strip=True)) for cell in header_cells]
        header_blob = " | ".join(headers).lower()
        if not any(token in header_blob for token in ["grantor", "grantee", "party", "instrument", "filed", "book", "page", "county"]):
            continue

        for row in rows[1:]:
            try:
                cells = row.find_all(["td", "th"])
                if not cells or len(cells) < 2:
                    continue
                values = [clean_text(cell.get_text(" ", strip=True)) for cell in cells]
                row_map = {headers[idx] if idx < len(headers) else f"col_{idx}": values[idx] for idx in range(len(values))}

                link = row.find("a", href=True)
                clerk_url = urljoin(base_url, link["href"]) if link else ""
                doc_num = extract_best(headers, row_map, ["Document Number", "Doc No", "Book/Page", "Book Page", "Instrument", "Reception"])
                doc_type = extract_best(headers, row_map, ["Instrument", "Document Type", "Type"])
                filed = extract_best(headers, row_map, ["Filed", "Date Filed", "Filed Date", "Recording Date"])
                owner = extract_best(headers, row_map, ["Grantor", "Debtor", "Direct Party", "Owner", "Party 1"])
                grantee = extract_best(headers, row_map, ["Grantee", "Claimant", "Reverse Party", "Party 2"])
                legal = extract_best(headers, row_map, ["Legal", "Description", "Property", "Subdivision", "Remarks"])
                amount = extract_best(headers, row_map, ["Amount", "Consideration", "Debt", "Lien Amount"])

                if not any([doc_num, doc_type, filed, owner, grantee, legal]):
                    continue

                if not amount:
                    row_text = " | ".join(values)
                    money_match = re.search(r"\$\s?[\d,]+(?:\.\d{2})?", row_text)
                    amount = money_match.group(0) if money_match else ""

                parsed.append(
                    RawRecord(
                        doc_num=doc_num,
                        doc_type=doc_type or category.instrument_label,
                        filed=filed,
                        cat=category.cat,
                        cat_label=category.cat_label,
                        owner=owner,
                        grantee=grantee,
                        amount=amount,
                        legal=legal,
                        clerk_url=clerk_url,
                    )
                )
            except Exception as exc:  # noqa: BLE001
                logger.warning("Skipping bad results row for %s: %s", category.cat, exc)
                continue

    return parsed


# -----------------------------
# GSCCCA scraping
# -----------------------------
@retryable_async
async def search_category(page: Page, category: CategoryConfig, from_date: str, to_date: str) -> List[RawRecord]:
    url = GSCCCA_LIEN_URL if category.source_kind == "lien" else GSCCCA_REAL_ESTATE_URL
    logger.info("Searching %s on %s", category.cat, url)

    await page.goto(url, wait_until="domcontentloaded", timeout=REQUEST_TIMEOUT * 1000)
    await page.wait_for_timeout(1500)

    county_select = await find_select_with_option(page, "GWINNETT")
    if county_select is None:
        raise RuntimeError(f"Could not locate county select for {category.cat}")

    instrument_select = await find_select_with_option(page, category.instrument_label)
    if instrument_select is None:
        raise RuntimeError(f"Could not locate instrument select for {category.cat} ({category.instrument_label})")

    await set_date_range_fields(page, from_date, to_date)
    await set_results_per_page(page)

    # Prefer all parties if the party select is available.
    for select in await page.locator("select").all():
        try:
            await safe_select_option_by_text(select, "All Parties")
        except Exception:  # noqa: BLE001
            continue

    await click_search(page)
    await page.wait_for_load_state("networkidle")
    await page.wait_for_timeout(1000)

    results: List[RawRecord] = []
    seen_pages = 0
    while True:
        html = await page.content()
        page_records = parse_result_tables(html, page.url, category)
        logger.info("%s page %s -> %s rows", category.cat, seen_pages + 1, len(page_records))
        results.extend(page_records)
        seen_pages += 1
        if seen_pages >= 20:
            logger.warning("Stopping pagination for %s after %s pages", category.cat, seen_pages)
            break
        moved = await next_page(page)
        if not moved:
            break

    return results


async def scrape_all_categories(from_date: str, to_date: str) -> List[RawRecord]:
    all_records: List[RawRecord] = []
    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=HEADLESS)
        context: BrowserContext = await browser.new_context(user_agent=USER_AGENT)
        page = await context.new_page()

        for category in CATEGORY_CONFIGS:
            try:
                records = await search_category(page, category, from_date, to_date)
                all_records.extend(records)
            except Exception as exc:  # noqa: BLE001
                logger.exception("Category %s failed and will be skipped: %s", category.cat, exc)
                continue

        await context.close()
        await browser.close()

    logger.info("Scraped %s raw records before enrichment/dedupe", len(all_records))
    return all_records


# -----------------------------
# Enrichment and scoring
# -----------------------------
def lookup_parcel(owner: str, parcel_index: Dict[str, Dict[str, str]]) -> Dict[str, str]:
    for variant in name_variants(owner):
        if variant in parcel_index:
            return parcel_index[variant]
    return {}



def flags_for_record(record: LeadRecord, lookback_cutoff: date) -> List[str]:
    flags: List[str] = []
    cat = record.cat.upper()
    owner_norm = normalize_name(record.owner)

    if cat == "LP":
        flags.append("Lis pendens")
    if cat == "NOFC":
        flags.append("Pre-foreclosure")
    if cat in {"JUD", "CCJ", "DRJUD"}:
        flags.append("Judgment lien")
    if cat in {"LNCORPTX", "LNIRS", "LNFED"}:
        flags.append("Tax lien")
    if cat == "LNMECH":
        flags.append("Mechanic lien")
    if cat == "PRO":
        flags.append("Probate / estate")

    business_markers = ["LLC", "INC", "CORP", "CORPORATION", "LLP", "LP", "TRUST", "HOLDINGS"]
    if any(marker in owner_norm for marker in business_markers):
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



def enrich_records(raw_records: List[RawRecord], parcel_index: Dict[str, Dict[str, str]], lookback_cutoff: date) -> List[LeadRecord]:
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
        except Exception as exc:  # noqa: BLE001
            logger.warning("Skipping bad enriched row: %s", exc)
            continue
    return dedupe_records(enriched)


# -----------------------------
# Exporters
# -----------------------------
def build_json_payload(records: List[LeadRecord], from_date: str, to_date: str) -> Dict[str, Any]:
    payload = {
        "fetched_at": datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "source": "Gwinnett County Clerk / GSCCCA + Property Appraiser Bulk Data",
        "date_range": {"from": from_date, "to": to_date, "lookback_days": LOOKBACK_DAYS},
        "total": len(records),
        "with_address": sum(1 for record in records if record.prop_address),
        "records": [asdict(record) for record in records],
    }
    return payload



def write_json_outputs(payload: Dict[str, Any]) -> None:
    data_path = DATA_DIR / "records.json"
    dashboard_path = DASHBOARD_DIR / "records.json"
    serialized = json.dumps(payload, indent=2, ensure_ascii=False)
    data_path.write_text(serialized, encoding="utf-8")
    dashboard_path.write_text(serialized, encoding="utf-8")
    logger.info("Wrote %s and %s", data_path, dashboard_path)



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
                    "Source": "Gwinnett County Clerk / GSCCCA",
                    "Public Records URL": record.clerk_url,
                }
            )
    logger.info("Wrote %s", export_path)



def write_initial_empty_records() -> None:
    empty_payload = {
        "fetched_at": "",
        "source": "",
        "date_range": {"from": "", "to": "", "lookback_days": LOOKBACK_DAYS},
        "total": 0,
        "with_address": 0,
        "records": [],
    }
    target = DASHBOARD_DIR / "records.json"
    if not target.exists():
        target.write_text(json.dumps(empty_payload, indent=2), encoding="utf-8")


# -----------------------------
# Main
# -----------------------------
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
    logger.info("Clerk portal   : %s", CLERK_PORTAL_URL)
    logger.info("Real estate    : %s", GSCCCA_REAL_ESTATE_URL)
    logger.info("Lien search    : %s", GSCCCA_LIEN_URL)
    logger.info("Parcel bulk url: %s", PROPERTY_APPRAISER_BULK_DATA_URL or "<not provided>")
    logger.info("Range          : %s -> %s (%s days)", from_date, to_date, LOOKBACK_DAYS)
    logger.info("Types          : %s", ", ".join(cfg.cat for cfg in CATEGORY_CONFIGS))
    logger.info("============================================================")

    parcel_index = {}
    try:
        parcel_index = build_parcel_index()
    except Exception as exc:  # noqa: BLE001
        logger.exception("Parcel enrichment setup failed. Continuing without parcel data: %s", exc)

    raw_records = await scrape_all_categories(from_date, to_date)
    lookback_cutoff = today - timedelta(days=7)
    records = enrich_records(raw_records, parcel_index, lookback_cutoff)
    records.sort(key=lambda r: (r.score, parse_date_text(r.filed) or date.min), reverse=True)

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
    except Exception as exc:  # noqa: BLE001
        logger.exception("Fatal error: %s", exc)
        # Always write a valid empty payload so the dashboard never crashes.
        ensure_dirs()
        write_initial_empty_records()
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
