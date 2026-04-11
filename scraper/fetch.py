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
from typing import Any, Dict, Iterable, Iterator, List, Optional, Sequence, Tuple
from urllib.parse import urljoin
from xml.etree import ElementTree as ET

import requests
from bs4 import BeautifulSoup
from dbfread import DBF
from playwright.async_api import BrowserContext, Locator, Page, async_playwright


# ============================================================
# CONFIG
# ============================================================
BASE_DIR = Path(__file__).resolve().parent.parent
DATA_DIR = BASE_DIR / "data"
DASHBOARD_DIR = BASE_DIR / "dashboard"
TMP_DIR = BASE_DIR / ".tmp"
LOG_DIR = BASE_DIR / ".logs"

CLERK_PORTAL_URL = os.getenv(
    "CLERK_PORTAL_URL",
    "https://www.gwinnettcourts.com/deeds-and-land-records/",
)

GSCCCA_REAL_ESTATE_URL = os.getenv(
    "GSCCCA_REAL_ESTATE_URL",
    "https://search.gsccca.org/RealEstate/namesearch.asp",
)

GSCCCA_LIEN_URL = os.getenv(
    "GSCCCA_LIEN_URL",
    "https://search.gsccca.org/Lien/namesearch.asp",
)

# Official county ownership ZIP from the Property Ownership Database page.
DEFAULT_PROPERTY_BULK_URL = (
    "https://www.gwinnettcounty.com/documents/d/gwinnett-county/"
    "tax_assessor_property_ownership_data-zip"
)

PROPERTY_APPRAISER_BULK_DATA_URL = os.getenv(
    "PROPERTY_APPRAISER_BULK_DATA_URL",
    DEFAULT_PROPERTY_BULK_URL,
).strip()

LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "7"))
REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "60"))
MAX_RETRIES = int(os.getenv("MAX_RETRIES", "3"))
HEADLESS = os.getenv("HEADLESS", "true").lower() != "false"

USER_AGENT = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)

GSCCCA_PREFIXES = list("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")


# ============================================================
# CATEGORY CONFIG
# ============================================================
@dataclass(frozen=True)
class CategoryConfig:
    cat: str
    cat_label: str
    source_kind: str  # "lien" | "realestate"
    instrument_label: str
    post_filter_terms: Tuple[str, ...] = ()
    negative_filter_terms: Tuple[str, ...] = ()


CATEGORY_CONFIGS: List[CategoryConfig] = [
    CategoryConfig("LP", "Lis Pendens", "lien", "Lis Pendens"),
    CategoryConfig("NOFC", "Notice of Foreclosure", "realestate", "DEED - FORECLOSURE"),
    CategoryConfig("TAXDEED", "Tax Deed", "realestate", "TAX SALE DEED"),
    CategoryConfig("JUD", "Judgment", "lien", "FIFA"),
    CategoryConfig("CCJ", "Certified Judgment", "lien", "ORDER"),
    CategoryConfig("DRJUD", "Domestic Judgment", "lien", "ORDER"),
    CategoryConfig("LNCORPTX", "Corporate Tax Lien", "lien", "Lien", ("TAX", "DEPARTMENT OF REVENUE", "STATE OF GEORGIA")),
    CategoryConfig("LNIRS", "IRS Lien", "lien", "Federal Tax Lien", ("IRS", "INTERNAL REVENUE", "UNITED STATES")),
    CategoryConfig("LNFED", "Federal Lien", "lien", "Federal Tax Lien", ("UNITED STATES", "FEDERAL")),
    CategoryConfig("LN", "Lien", "lien", "Lien"),
    CategoryConfig("LNMECH", "Mechanic Lien", "lien", "Mechanics and Materialmens Lien"),
    CategoryConfig("LNHOA", "HOA Lien", "lien", "Lien", ("HOMEOWNERS", "HOMEOWNER", "ASSOCIATION", "HOA", "CONDOMINIUM")),
    CategoryConfig("MEDLN", "Medicaid Lien", "lien", "Lien", ("MEDICAID", "DEPARTMENT OF COMMUNITY HEALTH", "DCH")),
    CategoryConfig("PRO", "Probate / Estate", "realestate", "ESTATE DOCUMENTATION"),
    CategoryConfig("NOC", "Notice of Commencement", "lien", "Notice"),
    CategoryConfig("RELLP", "Release Lis Pendens", "lien", "Release", ("LIS PENDENS",)),
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


# ============================================================
# MODELS
# ============================================================
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


# ============================================================
# LOGGING / FS
# ============================================================
logger = logging.getLogger("gwinnett_scraper")


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


def ensure_dirs() -> None:
    for path in [DATA_DIR, DASHBOARD_DIR, TMP_DIR, LOG_DIR]:
        path.mkdir(parents=True, exist_ok=True)


def write_initial_empty_records() -> None:
    empty_payload = {
        "fetched_at": None,
        "source": "Gwinnett County",
        "date_range": {"from": None, "to": None, "lookback_days": LOOKBACK_DAYS},
        "total": 0,
        "with_address": 0,
        "records": [],
    }
    for path in [DATA_DIR / "records.json", DASHBOARD_DIR / "records.json"]:
        if not path.exists():
            path.write_text(json.dumps(empty_payload, indent=2), encoding="utf-8")


# ============================================================
# RETRY HELPERS
# ============================================================
def retryable(fn):
    def wrapper(*args, **kwargs):
        last_exc: Optional[Exception] = None
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                return fn(*args, **kwargs)
            except Exception as exc:  # noqa: BLE001
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
                logger.warning(
                    "Attempt %s/%s failed for %s: %s",
                    attempt,
                    MAX_RETRIES,
                    fn.__name__,
                    exc,
                )
                if attempt < MAX_RETRIES:
                    await asyncio.sleep(min(attempt * 2, 6))
        assert last_exc is not None
        raise last_exc

    return wrapper


# ============================================================
# GENERIC HELPERS
# ============================================================
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
    business_markers = [
        "LLC", "INC", "CORP", "CORPORATION", "COMPANY",
        "TRUST", "ESTATE", "LP", "LLP", "LTD", "BANK", "HOLDINGS",
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
            middle = " ".join(parts[1:-1]).strip()
            variants.add(normalize_spaces(f"{last} {first}"))
            variants.add(normalize_spaces(f"{last}, {first}"))
            if middle:
                variants.add(normalize_spaces(f"{last}, {first} {middle}"))

    return sorted(v for v in variants if v)


def extract_money(text: str) -> str:
    match = re.search(r"\$\s?[\d,]+(?:\.\d{2})?", text)
    return match.group(0) if match else ""


def extract_best(headers: Sequence[str], row: Dict[str, str], candidates: Sequence[str]) -> str:
    header_map = {normalize_name(h): h for h in headers}
    for candidate in candidates:
        candidate_key = normalize_name(candidate)
        for header_norm, original_header in header_map.items():
            if candidate_key == header_norm or candidate_key in header_norm:
                return clean_text(row.get(original_header, ""))
    return ""


def dedupe_records(records: Iterable[LeadRecord]) -> List[LeadRecord]:
    seen: set[Tuple[str, str, str, str, str]] = set()
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


# ============================================================
# HTTP
# ============================================================
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


# ============================================================
# PROPERTY DATA DOWNLOAD / PARSING
# ============================================================
@retryable
def download_property_bulk_data(url: str) -> Optional[bytes]:
    if not url:
        logger.warning("PROPERTY_APPRAISER_BULK_DATA_URL is blank. Parcel enrichment will be skipped.")
        return None

    session = requests.Session()
    response = http_get(url, session=session, allow_redirects=True)
    content_type = clean_text(response.headers.get("content-type", "")).lower()

    if any(token in content_type for token in ("application/zip", "application/octet-stream", "zip")):
        return response.content

    if response.url.lower().endswith((".zip", ".dbf", ".xlsx")):
        return response.content

    soup = BeautifulSoup(response.text, "lxml")

    # direct downloadable links
    for anchor in soup.find_all("a", href=True):
        href = clean_text(anchor["href"])
        if any(href.lower().endswith(ext) for ext in (".zip", ".dbf", ".xlsx")):
            file_url = urljoin(response.url, href)
            logger.info("Following parcel download link: %s", file_url)
            return http_get(file_url, session=session, allow_redirects=True).content

    # ASP.NET fallback
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
                post_url = urljoin(response.url, form.get("action") or response.url)
                logger.info("Triggering ASP.NET parcel download via __doPostBack: %s", event_target)
                return http_post(post_url, session=session, data=payload, allow_redirects=True).content

    logger.warning("Could not detect downloadable parcel data at %s", url)
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


def read_dbf_rows(dbf_bytes: bytes, filename: str) -> Iterator[Dict[str, Any]]:
    path = TMP_DIR / Path(filename).name
    path.write_bytes(dbf_bytes)
    dbf = DBF(str(path), load=True, ignore_missing_memofile=True, char_decode_errors="ignore")
    for row in dbf:
        yield dict(row)


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
    strings: List[str] = []
    for si in root.findall("x:si", ns):
        parts: List[str] = []
        for t in si.findall(".//x:t", ns):
            parts.append(t.text or "")
        strings.append("".join(parts))
    return strings


def read_xlsx_rows(xlsx_bytes: bytes) -> Iterator[Dict[str, Any]]:
    with zipfile.ZipFile(BytesIO(xlsx_bytes)) as zf:
        shared_strings = read_xlsx_shared_strings(zf)
        workbook = ET.fromstring(zf.read("xl/workbook.xml"))
        ns = {"x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main", "r": "http://schemas.openxmlformats.org/officeDocument/2006/relationships"}

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

        sheet_path = "xl/" + target.lstrip("/")
        sheet_xml = ET.fromstring(zf.read(sheet_path))

        rows = sheet_xml.findall(".//x:sheetData/x:row", ns)
        if not rows:
            return

        def cell_value(cell: ET.Element) -> str:
            cell_type = cell.attrib.get("t", "")
            value_el = cell.find("x:v", ns)
            if value_el is None:
                is_el = cell.find("x:is", ns)
                if is_el is not None:
                    texts = [t.text or "" for t in is_el.findall(".//x:t", ns)]
                    return clean_text("".join(texts))
                return ""
            raw = value_el.text or ""
            if cell_type == "s":
                try:
                    return clean_text(shared_strings[int(raw)])
                except Exception:  # noqa: BLE001
                    return clean_text(raw)
            return clean_text(raw)

        header_map: Dict[int, str] = {}
        header_row = rows[0]
        for cell in header_row.findall("x:c", ns):
            ref = cell.attrib.get("r", "")
            col_ref = re.sub(r"\d+", "", ref)
            idx = col_letters_to_index(col_ref)
            header_map[idx] = cell_value(cell)

        for row in rows[1:]:
            row_values: Dict[str, Any] = {}
            for cell in row.findall("x:c", ns):
                ref = cell.attrib.get("r", "")
                col_ref = re.sub(r"\d+", "", ref)
                idx = col_letters_to_index(col_ref)
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


def build_parcel_index() -> Dict[str, Dict[str, str]]:
    parcel_index: Dict[str, Dict[str, str]] = {}
    blob = download_property_bulk_data(PROPERTY_APPRAISER_BULK_DATA_URL)
    if not blob:
        return parcel_index

    members = iter_zip_members(blob)

    row_iterators: List[Iterator[Dict[str, Any]]] = []
    for name, data in members:
        lower = name.lower()
        if lower.endswith(".dbf"):
            logger.info("Using parcel DBF: %s", name)
            row_iterators.append(read_dbf_rows(data, name))
        elif lower.endswith(".xlsx"):
            logger.info("Using parcel XLSX: %s", name)
            row_iterators.append(read_xlsx_rows(data))

    if not row_iterators:
        # direct non-zip xlsx/dbf fallback
        if PROPERTY_APPRAISER_BULK_DATA_URL.lower().endswith(".xlsx"):
            row_iterators.append(read_xlsx_rows(blob))
        elif PROPERTY_APPRAISER_BULK_DATA_URL.lower().endswith(".dbf"):
            row_iterators.append(read_dbf_rows(blob, "parcel.dbf"))

    if not row_iterators:
        logger.warning("No parcel DBF/XLSX found in ownership download. Enrichment skipped.")
        return parcel_index

    total_rows = 0
    for row_iter in row_iterators:
        for row_map in row_iter:
            total_rows += 1
            try:
                owner = build_row_lookup(row_map, ["OWNER", "OWN1", "OWNER_NAME", "OWNNAME"])
                if not owner:
                    continue

                site_addr = build_row_lookup(row_map, ["SITE_ADDR", "SITEADDR", "SITUSADDR", "PROPERTY_ADDRESS"])
                site_city = build_row_lookup(row_map, ["SITE_CITY", "SITECITY", "PROP_CITY", "CITY"])
                site_zip = build_row_lookup(row_map, ["SITE_ZIP", "SITEZIP", "PROP_ZIP", "ZIP"])
                mail_addr = build_row_lookup(row_map, ["ADDR_1", "MAILADR1", "MAIL_ADDR", "MAILADDR1", "OWNER_ADDRESS"])
                mail_city = build_row_lookup(row_map, ["MAILCITY", "MAIL_CITY", "CITY"])
                mail_state = build_row_lookup(row_map, ["MAILSTATE", "MAIL_STATE", "STATE"])
                mail_zip = build_row_lookup(row_map, ["MAILZIP", "MAIL_ZIP", "ZIP"])

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
                    if variant not in parcel_index:
                        parcel_index[variant] = payload
            except Exception as exc:  # noqa: BLE001
                logger.warning("Skipping bad parcel row: %s", exc)
                continue

    logger.info("Parcel rows processed: %s | owner keys indexed: %s", total_rows, len(parcel_index))
    return parcel_index


# ============================================================
# PLAYWRIGHT FORM DISCOVERY
# ============================================================
async def maybe_visible(locator: Locator) -> bool:
    try:
        return await locator.is_visible()
    except Exception:  # noqa: BLE001
        return False


async def find_first_matching_input(page: Page, patterns: Sequence[str]) -> Optional[Locator]:
    patterns = [p.lower() for p in patterns]
    candidates = await page.locator("input").all()
    for inp in candidates:
        try:
            attrs = " ".join(
                clean_text(v)
                for v in [
                    await inp.get_attribute("name"),
                    await inp.get_attribute("id"),
                    await inp.get_attribute("placeholder"),
                    await inp.get_attribute("aria-label"),
                    await inp.get_attribute("title"),
                    await inp.input_value(),
                ]
                if v
            ).lower()
            input_type = clean_text(await inp.get_attribute("type")).lower()
            if input_type in {"hidden", "submit", "button", "image", "checkbox", "radio"}:
                continue
            if any(p in attrs for p in patterns):
                return inp
        except Exception:  # noqa: BLE001
            continue
    return None


async def safe_select_option_by_text(select_locator: Locator, option_text: str) -> bool:
    try:
        options = await select_locator.locator("option").all()
        pairs: List[Tuple[str, str]] = []
        for option in options:
            text = clean_text(await option.text_content())
            value = clean_text(await option.get_attribute("value"))
            pairs.append((text, value))
        for text, value in pairs:
            if text.upper() == option_text.upper() or option_text.upper() in text.upper():
                await select_locator.select_option(value=value)
                return True
    except Exception:  # noqa: BLE001
        return False
    return False


async def find_select_with_option(page: Page, option_text: str) -> Optional[Locator]:
    selects = await page.locator("select").all()
    for select in selects:
        if await safe_select_option_by_text(select, option_text):
            return select
    return None


async def set_results_per_page(page: Page) -> None:
    selects = await page.locator("select").all()
    for select in selects:
        try:
            options = await select.locator("option").all()
            texts = [clean_text(await option.text_content()) for option in options]
            if "100" in texts:
                await safe_select_option_by_text(select, "100")
                return
        except Exception:  # noqa: BLE001
            continue


async def set_date_range_fields(page: Page, from_date: str, to_date: str) -> None:
    from_input = await find_first_matching_input(page, ["fromdate", "from date", "begin", "start date"])
    to_input = await find_first_matching_input(page, ["todate", "to date", "end date", "through date"])

    if from_input and to_input:
        await from_input.fill("")
        await from_input.type(from_date, delay=15)
        await to_input.fill("")
        await to_input.type(to_date, delay=15)
        return

    # fallback: first two visible text-like inputs that mention date
    visible_inputs = await page.locator("input").all()
    date_like: List[Locator] = []
    for inp in visible_inputs:
        try:
            if not await maybe_visible(inp):
                continue
            attrs = " ".join(
                clean_text(v)
                for v in [
                    await inp.get_attribute("name"),
                    await inp.get_attribute("id"),
                    await inp.get_attribute("placeholder"),
                    await inp.get_attribute("aria-label"),
                    await inp.get_attribute("title"),
                ]
                if v
            ).lower()
            if "date" in attrs:
                date_like.append(inp)
        except Exception:  # noqa: BLE001
            continue

    if len(date_like) >= 2:
        await date_like[0].fill(from_date)
        await date_like[1].fill(to_date)


async def set_name_prefix(page: Page, prefix: str) -> None:
    last_name_input = await find_first_matching_input(page, ["lastname", "last name", "grantor", "debtor", "party"])
    first_name_input = await find_first_matching_input(page, ["firstname", "first name"])

    if last_name_input is None:
        text_inputs = await page.locator("input[type='text'], input:not([type])").all()
        visible_text_inputs = [inp for inp in text_inputs if await maybe_visible(inp)]
        if visible_text_inputs:
            last_name_input = visible_text_inputs[0]
        if len(visible_text_inputs) >= 2 and first_name_input is None:
            first_name_input = visible_text_inputs[1]

    if last_name_input is None:
        raise RuntimeError("Could not locate name search input on GSCCCA page")

    await last_name_input.fill("")
    await last_name_input.type(prefix, delay=25)

    if first_name_input is not None:
        await first_name_input.fill("")


async def click_search(page: Page) -> None:
    candidates = [
        page.get_by_role("button", name=re.compile("search", re.I)),
        page.get_by_role("link", name=re.compile("search", re.I)),
        page.locator("input[type='submit']"),
        page.locator("button[type='submit']"),
    ]
    for locator in candidates:
        try:
            if await locator.count() > 0:
                await locator.first.click()
                return
        except Exception:  # noqa: BLE001
            continue
    raise RuntimeError("Could not locate search submit control")


async def next_page(page: Page) -> bool:
    locators = [
        page.get_by_role("link", name=re.compile(r"^next$", re.I)),
        page.get_by_text(re.compile(r"^next$", re.I)),
        page.locator("a", has_text="Next"),
    ]
    for locator in locators:
        try:
            if await locator.count() == 0:
                continue
            link = locator.first
            href = await link.get_attribute("href")
            klass = clean_text(await link.get_attribute("class")).lower()
            if "disabled" in klass or href in {"", None, "#"}:
                continue
            await link.click()
            await page.wait_for_load_state("networkidle")
            await page.wait_for_timeout(600)
            return True
        except Exception:  # noqa: BLE001
            continue
    return False


# ============================================================
# RESULT PARSING / FILTERING
# ============================================================
def parse_result_tables(html: str, base_url: str, category: CategoryConfig) -> List[RawRecord]:
    soup = BeautifulSoup(html, "lxml")
    parsed: List[RawRecord] = []

    for table in soup.find_all("table"):
        rows = table.find_all("tr")
        if len(rows) < 2:
            continue

        header_cells = rows[0].find_all(["th", "td"])
        headers = [clean_text(cell.get_text(" ", strip=True)) for cell in header_cells]
        if not headers:
            continue

        header_blob = " | ".join(headers).lower()
        if not any(
            token in header_blob
            for token in ["grantor", "grantee", "party", "instrument", "filed", "record", "book", "page"]
        ):
            continue

        for row in rows[1:]:
            try:
                cells = row.find_all(["td", "th"])
                if len(cells) < 2:
                    continue

                values = [clean_text(cell.get_text(" ", strip=True)) for cell in cells]
                row_map = {
                    headers[idx] if idx < len(headers) else f"col_{idx}": values[idx]
                    for idx in range(len(values))
                }
                row_text = " | ".join(values)

                link = row.find("a", href=True)
                clerk_url = urljoin(base_url, link["href"]) if link else ""

                doc_num = extract_best(headers, row_map, ["Document Number", "Doc No", "Book/Page", "Book Page", "Reception", "Instrument"])
                doc_type = extract_best(headers, row_map, ["Instrument", "Document Type", "Type"])
                filed = extract_best(headers, row_map, ["Filed", "Date Filed", "Filed Date", "Recording Date"])
                owner = extract_best(headers, row_map, ["Grantor", "Debtor", "Direct Party", "Owner", "Party 1"])
                grantee = extract_best(headers, row_map, ["Grantee", "Claimant", "Reverse Party", "Party 2"])
                legal = extract_best(headers, row_map, ["Legal", "Description", "Property", "Subdivision", "Remarks", "Legal Description"])
                amount = extract_best(headers, row_map, ["Amount", "Debt", "Lien Amount", "Consideration"])

                if not amount:
                    amount = extract_money(row_text)

                if not any([doc_num, doc_type, filed, owner, grantee, legal]):
                    continue

                record = RawRecord(
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

                if record_matches_category(record, category):
                    parsed.append(record)
            except Exception as exc:  # noqa: BLE001
                logger.warning("Skipping bad results row for %s: %s", category.cat, exc)
                continue

    return parsed


def record_matches_category(record: RawRecord, category: CategoryConfig) -> bool:
    blob = " | ".join([
        record.doc_type,
        record.owner,
        record.grantee,
        record.legal,
        record.amount,
        record.doc_num,
        record.cat_label,
    ]).upper()

    if category.post_filter_terms:
        if not any(term.upper() in blob for term in category.post_filter_terms):
            # keep exact instrument hits even if term is missing
            if category.instrument_label.upper() not in blob:
                return False

    if category.negative_filter_terms:
        if any(term.upper() in blob for term in category.negative_filter_terms):
            return False

    return True


# ============================================================
# GSCCCA SCRAPING
# ============================================================
async def prep_search_form(page: Page, category: CategoryConfig, from_date: str, to_date: str) -> None:
    await page.goto(
        GSCCCA_LIEN_URL if category.source_kind == "lien" else GSCCCA_REAL_ESTATE_URL,
        wait_until="domcontentloaded",
        timeout=REQUEST_TIMEOUT * 1000,
    )
    await page.wait_for_timeout(1200)

    county_select = await find_select_with_option(page, "GWINNETT")
    if county_select is None:
        raise RuntimeError(f"Could not locate county select for {category.cat}")

    instrument_select = await find_select_with_option(page, category.instrument_label)
    if instrument_select is None:
        raise RuntimeError(
            f"Could not locate instrument select for {category.cat} ({category.instrument_label})"
        )

    await set_date_range_fields(page, from_date, to_date)
    await set_results_per_page(page)

    # Prefer all parties when available
    selects = await page.locator("select").all()
    for select in selects:
        try:
            await safe_select_option_by_text(select, "All Parties")
        except Exception:  # noqa: BLE001
            continue


@retryable_async
async def search_one_prefix(
    page: Page,
    category: CategoryConfig,
    prefix: str,
    from_date: str,
    to_date: str,
) -> List[RawRecord]:
    await prep_search_form(page, category, from_date, to_date)
    await set_name_prefix(page, prefix)
    await click_search(page)
    await page.wait_for_load_state("networkidle")
    await page.wait_for_timeout(800)

    results: List[RawRecord] = []
    page_num = 1

    while True:
        html = await page.content()
        page_records = parse_result_tables(html, page.url, category)
        logger.info("%s prefix %s page %s -> %s rows", category.cat, prefix, page_num, len(page_records))
        results.extend(page_records)

        if page_num >= 15:
            logger.warning("Stopping %s prefix %s at page limit %s", category.cat, prefix, page_num)
            break

        moved = await next_page(page)
        if not moved:
            break
        page_num += 1

    return results


async def scrape_category_with_prefixes(
    page: Page,
    category: CategoryConfig,
    from_date: str,
    to_date: str,
) -> List[RawRecord]:
    all_records: List[RawRecord] = []
    seen: set[Tuple[str, str, str, str]] = set()

    for prefix in GSCCCA_PREFIXES:
        try:
            prefix_records = await search_one_prefix(page, category, prefix, from_date, to_date)
            for record in prefix_records:
                key = (
                    clean_text(record.doc_num),
                    clean_text(record.doc_type),
                    clean_text(record.filed),
                    normalize_name(record.owner),
                )
                if key in seen:
                    continue
                seen.add(key)
                all_records.append(record)
        except Exception as exc:  # noqa: BLE001
            logger.warning("Prefix %s failed for %s: %s", prefix, category.cat, exc)
            continue

    logger.info("%s total unique rows after prefix sweep -> %s", category.cat, len(all_records))
    return all_records


async def scrape_all_categories(from_date: str, to_date: str) -> List[RawRecord]:
    all_records: List[RawRecord] = []

    async with async_playwright() as p:
        browser = await p.chromium.launch(headless=HEADLESS)
        context: BrowserContext = await browser.new_context(user_agent=USER_AGENT)
        page = await context.new_page()

        for category in CATEGORY_CONFIGS:
            try:
                logger.info("Searching category %s (%s)", category.cat, category.cat_label)
                records = await scrape_category_with_prefixes(page, category, from_date, to_date)
                all_records.extend(records)
            except Exception as exc:  # noqa: BLE001
                logger.exception("Category %s failed and will be skipped: %s", category.cat, exc)
                continue

        await context.close()
        await browser.close()

    logger.info("Scraped %s raw records before enrichment/dedupe", len(all_records))
    return all_records


# ============================================================
# ENRICHMENT / SCORING
# ============================================================
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
        except Exception as exc:  # noqa: BLE001
            logger.warning("Skipping bad enriched row: %s", exc)
            continue
    return dedupe_records(enriched)


# ============================================================
# EXPORTS
# ============================================================
def build_json_payload(records: List[LeadRecord], from_date: str, to_date: str) -> Dict[str, Any]:
    return {
        "fetched_at": datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
        "source": "Gwinnett County Clerk / GSCCCA + Gwinnett Ownership Data",
        "date_range": {"from": from_date, "to": to_date, "lookback_days": LOOKBACK_DAYS},
        "total": len(records),
        "with_address": sum(1 for r in records if r.prop_address),
        "records": [asdict(r) for r in records],
    }


def write_json_outputs(payload: Dict[str, Any]) -> None:
    serialized = json.dumps(payload, indent=2, ensure_ascii=False)
    data_path = DATA_DIR / "records.json"
    dashboard_path = DASHBOARD_DIR / "records.json"
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


# ============================================================
# MAIN
# ============================================================
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
    logger.info("Prefixes       : %s", "".join(GSCCCA_PREFIXES))
    logger.info("============================================================")

    parcel_index: Dict[str, Dict[str, str]] = {}
    try:
        parcel_index = build_parcel_index()
    except Exception as exc:  # noqa: BLE001
        logger.exception("Parcel enrichment setup failed. Continuing without parcel data: %s", exc)

    raw_records = await scrape_all_categories(from_date, to_date)
    lookback_cutoff = today - timedelta(days=7)

    records = enrich_records(raw_records, parcel_index, lookback_cutoff)
    records.sort(
        key=lambda r: (
            r.score,
            parse_date_text(r.filed) or date.min,
            normalize_name(r.owner),
        ),
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
    except Exception as exc:  # noqa: BLE001
        logger.exception("Fatal error: %s", exc)
        ensure_dirs()
        write_initial_empty_records()
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
