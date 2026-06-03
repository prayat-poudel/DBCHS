from __future__ import annotations

# =========================
# EDIT THESE VALUES FIRST
# =========================
USERNAME = os.environ.get("SITE_USERNAME", "")
PASSWORD = os.environ.get("SITE_PASSWORD", "")
HEADLESS = True
CHROME_BINARY = ""  # Optional. Leave blank unless Chrome is in a non-standard location.
DOWNLOAD_DIR = "downloads"  # Folder created next to this script.
CUSTOM_REPORT_MONTHS_BACK = 4
ALLOW_AGE_REPORT_FALLBACK = True  # If the custom age report download times out, create a blank age file and keep going.

import ast
import json
import logging
import os
import re
import shutil
import sys
import time
import traceback
from pathlib import Path
from typing import Iterable

import numpy as np
import pandas as pd
from dateutil.relativedelta import relativedelta
from selenium import webdriver
from selenium.common.exceptions import TimeoutException, StaleElementReferenceException
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import Select, WebDriverWait

try:
    from webdriver_manager.chrome import ChromeDriverManager
except Exception:
    ChromeDriverManager = None


BASE_DIR = Path(__file__).resolve().parent
DOWNLOAD_PATH = (BASE_DIR / DOWNLOAD_DIR).resolve()
LOG_PATH = (BASE_DIR / "logs").resolve()

LOGIN_URL = "https://new.shelterluv.com/login"
REPORT_URL = "https://new.shelterluv.com/quick-reports/show-report?report=animal.animal-population"
CUSTOM_REPORT_URL = "https://new.shelterluv.com/reports?tab=custom_reports"
WEIGHT_CHANGE_REPORTS_URL = "https://new.shelterluv.com/reports"

REPORT_DOWNLOAD_FILENAME = "dbchs_match_quiz.xlsx"
CUSTOM_REPORT_FILENAME = "dbchs_match_age.xlsx"
WEIGHT_CHANGE_REPORT_FILENAME = "dbchs_match_weight.xlsx"
FINAL_OUTPUT_FILENAME = "dbchs_final_current.csv"
FINAL_JSON_OUTPUT_FILENAME = "dbchs_final_current.json"
PIC_LINKS_FILENAME = "pic_links.csv"
MATCH_DATASET_FILENAME = "dbchs_match_dataset.csv"
BREED_FILENAME = "dbchs_breed.csv"

WAIT_SHORT = 10
WAIT_DEFAULT = 20
WAIT_LONG = 30
DOWNLOAD_TIMEOUT = 120


logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
logger = logging.getLogger("shelterluv_scraper")

ANIMAL_ID_PATTERN = re.compile(r"\b[A-Z]+-A-\d+\b", re.IGNORECASE)



class Selectors:
    USERNAME_FIELD = "#username"
    PASSWORD_FIELD = "#password"
    LOGIN_BUTTON = "//button[@type='submit']"

    ANIMAL_ID_LINK = "a.group.link.link-green.break-words"
    ANIMAL_IMAGE = "img.rounded-md.shadow-2xl"

    REPORT_TYPE_DROPDOWNS = (
        "select[data-cy='reportType']",
        "#reportType",
        "div[data-scroll-to='reportType'] select",
    )
    REPORT_TOPIC_DROPDOWNS = (
        "select[data-cy='topic']",
        "#topic",
        "div[data-scroll-to='topic'] select",
    )
    RULE_FIELD_SELECTORS = (
        "div[data-scroll-to='rule.field'] select",
        "select[data-cy='rule.field']",
        "select[wire\\:model*='rule.field']",
    )
    RULE_OPERATOR_SELECTORS = (
        "div[data-scroll-to='rule.operator'] select",
        "select[data-cy='rule.operator']",
        "select[wire\\:model*='rule.operator']",
    )
    RULE_VALUE_SELECTORS = (
        "div[data-scroll-to='rule.value'] input[type='number']",
        "input[data-cy='rule.value']",
        "input[type='number']",
    )

    ADD_RULE_XPATHS = (
        "//button[contains(normalize-space(.), 'Add Rule')]",
        "//button[contains(normalize-space(.), 'Add rule')]",
        "//button[contains(normalize-space(.), 'Add Filter')]",
        "//button[contains(@wire:click, 'addRule')]",
        "//button[contains(@wire:click, 'addRulesetRule')]",
    )
    RUN_REPORT_XPATHS = (
        "//button[@data-cy='primary-button' and contains(normalize-space(.), 'Run Report')]",
        "//button[contains(normalize-space(.), 'Run Report')]",
        "//button[contains(@wire:click, 'saveAndOpen')]",
    )
    EXCEL_EXPORT_XPATHS = (
        "//button[contains(normalize-space(.), 'Excel')]",
        "//button[@data-cy='secondary-button' and contains(normalize-space(.), 'Excel')]",
        "//button[contains(@wire:click, 'exportToExcel')]",
    )


def ensure_directories() -> None:
    DOWNLOAD_PATH.mkdir(parents=True, exist_ok=True)
    LOG_PATH.mkdir(parents=True, exist_ok=True)


def clear_old_temp_files() -> None:
    for pattern in ["*.crdownload", "*.part", "~$*.xlsx"]:
        for path in DOWNLOAD_PATH.glob(pattern):
            try:
                path.unlink()
            except OSError:
                pass


def wait_for_download_and_rename(
    target_filename: str,
    timeout: int = DOWNLOAD_TIMEOUT,
    started_at: float | None = None,
) -> Path:
    """
    Wait for a downloaded spreadsheet and rename it to the expected filename.

    This version is intentionally more forgiving than the first version. Shelterluv
    can start the download before this function gets its first directory snapshot,
    so we look for recently modified spreadsheet files instead of only files whose
    names were absent from an initial snapshot.
    """
    logger.info("Waiting for download: %s", target_filename)
    target_path = DOWNLOAD_PATH / target_filename
    allowed_suffixes = {".xlsx", ".xls"}

    # Give ourselves a small grace window so a very fast download that begins
    # right before this function is called is still considered current.
    effective_started_at = (started_at if started_at is not None else time.time()) - 5
    end_time = time.time() + timeout

    def is_temporary_download(path: Path) -> bool:
        name = path.name.lower()
        return (
            name.startswith("~$")
            or name.endswith(".crdownload")
            or name.endswith(".part")
            or name.endswith(".tmp")
        )

    def wait_until_stable(path: Path) -> bool:
        previous_size = -1
        for _ in range(15):
            if not path.exists() or is_temporary_download(path):
                time.sleep(1)
                continue
            current_size = path.stat().st_size
            if current_size > 0 and current_size == previous_size:
                return True
            previous_size = current_size
            time.sleep(1)
        return False

    while time.time() < end_time:
        current_files = list(DOWNLOAD_PATH.iterdir())

        # If Chrome saved directly to the target name, just wait for it to finish.
        if target_path.exists() and target_path.stat().st_mtime >= effective_started_at:
            if wait_until_stable(target_path):
                logger.info("Saved download to %s", target_path)
                return target_path

        candidates: list[Path] = []
        for file_path in current_files:
            if is_temporary_download(file_path):
                continue
            if file_path.suffix.lower() not in allowed_suffixes:
                continue
            try:
                if file_path.stat().st_mtime >= effective_started_at and file_path.stat().st_size > 0:
                    candidates.append(file_path)
            except OSError:
                continue

        candidates.sort(key=lambda p: p.stat().st_mtime, reverse=True)

        for file_path in candidates:
            if wait_until_stable(file_path):
                if file_path.resolve() == target_path.resolve():
                    logger.info("Saved download to %s", target_path)
                    return target_path

                if target_path.exists():
                    target_path.unlink()
                shutil.move(str(file_path), str(target_path))
                logger.info("Saved download to %s", target_path)
                return target_path

        time.sleep(1)

    download_listing = ", ".join(
        f"{p.name} ({p.stat().st_size} bytes)"
        for p in sorted(DOWNLOAD_PATH.iterdir(), key=lambda x: x.stat().st_mtime, reverse=True)[:15]
        if p.is_file()
    )
    raise TimeoutError(
        f"Timed out waiting for {target_filename}. "
        f"Recent files in {DOWNLOAD_PATH}: {download_listing or 'none'}"
    )


def build_driver() -> webdriver.Chrome:
    ensure_directories()
    clear_old_temp_files()

    options = Options()
    if HEADLESS:
        options.add_argument("--headless=new")
    options.add_argument("--window-size=1920,1080")
    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_experimental_option(
        "prefs",
        {
            "download.default_directory": str(DOWNLOAD_PATH),
            "download.prompt_for_download": False,
            "download.directory_upgrade": True,
            "safebrowsing.enabled": True,
        },
    )

    if CHROME_BINARY.strip():
        options.binary_location = CHROME_BINARY.strip()

    try:
        driver = webdriver.Chrome(options=options)
    except Exception:
        if ChromeDriverManager is None:
            raise
        service = Service(ChromeDriverManager().install())
        driver = webdriver.Chrome(service=service, options=options)

    # Allow downloads while in headless mode.
    driver.execute_cdp_cmd(
        "Page.setDownloadBehavior",
        {"behavior": "allow", "downloadPath": str(DOWNLOAD_PATH)},
    )
    return driver


class ShelterLuvScraper:
    def __init__(self) -> None:
        self.driver = build_driver()
        self.wait = WebDriverWait(self.driver, WAIT_DEFAULT)
        self.long_wait = WebDriverWait(self.driver, WAIT_LONG)
        self.animal_image_data: list[dict[str, str]] = []

    def login(self) -> None:
        logger.info("Logging in...")
        self.driver.get(LOGIN_URL)

        username_field = self.long_wait.until(
            EC.presence_of_element_located((By.CSS_SELECTOR, Selectors.USERNAME_FIELD))
        )
        password_field = self.driver.find_element(By.CSS_SELECTOR, Selectors.PASSWORD_FIELD)

        username_field.clear()
        username_field.send_keys(USERNAME)
        password_field.clear()
        password_field.send_keys(PASSWORD)

        login_button = self.wait.until(
            EC.element_to_be_clickable((By.XPATH, Selectors.LOGIN_BUTTON))
        )
        login_button.click()

        WebDriverWait(self.driver, WAIT_SHORT).until(EC.url_changes(LOGIN_URL))
        time.sleep(3)
        logger.info("Login successful")

    def _extract_animal_id(self, value: str) -> str:
        text = re.sub(r"\s+", " ", str(value or "")).strip()
        match = ANIMAL_ID_PATTERN.search(text)
        return match.group(0).upper() if match else ""

    def _get_target_animal_ids_from_report(self, report_path: Path) -> list[str]:
        report_df = pd.read_excel(report_path).fillna("")
        animal_id_column = next(
            (col for col in ["Animal ID", "Animal_ID", "AnimalID"] if col in report_df.columns),
            None,
        )
        if animal_id_column is None:
            raise RuntimeError("Could not find an Animal ID column in the downloaded standard report.")

        target_ids: list[str] = []
        seen_ids: set[str] = set()
        for raw_value in report_df[animal_id_column].astype(str):
            animal_id = self._extract_animal_id(raw_value)
            if animal_id and animal_id not in seen_ids:
                seen_ids.add(animal_id)
                target_ids.append(animal_id)
        return target_ids

    def _get_current_page_animal_links(self, target_ids: set[str]) -> list[dict[str, str]]:
        animal_links: list[dict[str, str]] = []
        seen_on_page: set[str] = set()

        for anchor in self.driver.find_elements(By.CSS_SELECTOR, "a[href]"):
            try:
                raw_text = anchor.text or anchor.get_attribute("textContent") or ""
                animal_id = self._extract_animal_id(raw_text)
                if not animal_id or animal_id not in target_ids or animal_id in seen_on_page:
                    continue

                href = (anchor.get_attribute("href") or "").strip()
                if not href:
                    continue

                animal_links.append({"Animal ID": animal_id, "url": href})
                seen_on_page.add(animal_id)
            except StaleElementReferenceException:
                continue

        return animal_links

    def _find_next_pagination_button(self):
        xpaths = [
            "//button[contains(translate(normalize-space(.), 'NEXT', 'next'), 'next')]",
            "//a[contains(translate(normalize-space(.), 'NEXT', 'next'), 'next')]",
            "//button[contains(translate(@aria-label, 'NEXT', 'next'), 'next')]",
            "//a[contains(translate(@aria-label, 'NEXT', 'next'), 'next')]",
            "//button[contains(translate(@title, 'NEXT', 'next'), 'next')]",
            "//a[contains(translate(@title, 'NEXT', 'next'), 'next')]",
            "//button[contains(translate(@data-cy, 'NEXT', 'next'), 'next')]",
            "//a[contains(translate(@data-cy, 'NEXT', 'next'), 'next')]",
        ]

        for xpath in xpaths:
            for element in self.driver.find_elements(By.XPATH, xpath):
                try:
                    classes = (element.get_attribute("class") or "").lower()
                    aria_disabled = (element.get_attribute("aria-disabled") or "").lower()
                    if (
                        element.is_displayed()
                        and element.is_enabled()
                        and element.get_attribute("disabled") is None
                        and aria_disabled != "true"
                        and "disabled" not in classes
                    ):
                        return element
                except StaleElementReferenceException:
                    continue

        return None

    def _extract_profile_image_url(self) -> str:
        candidate_selectors = [
            "img[src*='profile-pictures']",
            "img[data-src*='profile-pictures']",
            "img.rounded-md.shadow-2xl",
            "img[src]",
        ]

        for selector in candidate_selectors:
            try:
                images = self.driver.find_elements(By.CSS_SELECTOR, selector)
            except Exception:
                images = []

            for image in images:
                for attribute_name in ["src", "data-src"]:
                    raw_url = (image.get_attribute(attribute_name) or "").strip()
                    if raw_url and not raw_url.startswith("data:image"):
                        if raw_url.startswith("//"):
                            raw_url = f"https:{raw_url}"
                        return raw_url

        try:
            raw_url = self.driver.execute_script(
                """
                const images = Array.from(document.querySelectorAll('img'));
                for (const img of images) {
                    const candidates = [img.getAttribute('src'), img.getAttribute('data-src')];
                    for (const candidate of candidates) {
                        if (candidate && !candidate.startsWith('data:image')) {
                            if (candidate.includes('profile-pictures')) {
                                return candidate;
                            }
                        }
                    }
                }
                for (const img of images) {
                    const candidates = [img.getAttribute('src'), img.getAttribute('data-src')];
                    for (const candidate of candidates) {
                        if (candidate && !candidate.startsWith('data:image')) {
                            return candidate;
                        }
                    }
                }
                return '';
                """
            ) or ""
            raw_url = raw_url.strip()
            if raw_url.startswith("//"):
                raw_url = f"https:{raw_url}"
            return raw_url
        except Exception:
            return ""

    def _extract_shelterluv_size_group(self) -> str:
        """
        Return the Size Group value exactly as it appears on the animal profile page,
        for example: Small (0-24), Medium (25-59), Large (60-99), or Extra-Large (100+).
        """
        try:
            raw_size_group = self.driver.execute_script(
                r"""
                const normalize = (value) => (value || '').replace(/\s+/g, ' ').trim();

                // Preferred path: the Sex/Weight Livewire component stores size_group
                // directly in its wire:snapshot data.
                for (const element of Array.from(document.querySelectorAll('[wire\\:snapshot]'))) {
                    let snapshot = {};
                    try {
                        snapshot = JSON.parse(element.getAttribute('wire:snapshot') || '{}');
                    } catch (error) {
                        snapshot = {};
                    }

                    const data = snapshot.data || {};
                    const sizeGroup = normalize(data.size_group || '');
                    if (sizeGroup) return sizeGroup;
                }

                // Fallback: find the visible Size Group field and read the first displayed
                // value inside the same fieldset. This handles pages where the snapshot
                // structure changes but the visible profile text remains the same.
                const legends = Array.from(document.querySelectorAll('legend'));
                for (const legend of legends) {
                    if (normalize(legend.innerText || legend.textContent).toLowerCase() !== 'size group') {
                        continue;
                    }

                    const fieldset = legend.closest('fieldset');
                    if (!fieldset) continue;

                    const buttons = Array.from(fieldset.querySelectorAll('button'));
                    for (const button of buttons) {
                        const text = normalize(button.innerText || button.textContent);
                        if (text && text.toLowerCase() !== 'size group') return text;
                    }

                    const fieldText = normalize(fieldset.innerText || fieldset.textContent);
                    const cleaned = normalize(fieldText.replace(/^Size Group\s*/i, ''));
                    if (cleaned) return cleaned;
                }

                // Last fallback: parse body text near "Size Group".
                const bodyText = document.body ? normalize(document.body.innerText || document.body.textContent || '') : '';
                const match = bodyText.match(/Size Group\s+(Small \(0-24\)|Medium \(25-59\)|Large \(60-99\)|Extra-Large \(100\+\))/i);
                return match ? match[1] : '';
                """
            ) or ""
            return re.sub(r"\s+", " ", str(raw_size_group)).strip()
        except Exception:
            return ""


    def _extract_shelterluv_age(self) -> str:
        """
        Return the visible Age value exactly as it appears on the animal profile page,
        for example: 4Y/1M/21D.

        This intentionally reads the fieldset whose legend is exactly "Age", so it
        does not accidentally return "Age Group" or "Est. Birthdate".
        """
        try:
            raw_age = self.driver.execute_script(
                r"""
                const normalize = (value) => (value || '').replace(/\s+/g, ' ').trim();

                const getFieldsetValue = (fieldset) => {
                    if (!fieldset) return '';

                    // The profile value is usually in this button:
                    // <button class="inline-editable" ...>4Y/1M/21D</button>
                    const buttons = Array.from(fieldset.querySelectorAll('button.inline-editable, button'));
                    for (const button of buttons) {
                        const text = normalize(button.innerText || button.textContent || '');
                        if (text) return text;
                    }

                    // Fallback if Shelterluv changes the button markup but keeps the fieldset text.
                    const fieldText = normalize(fieldset.innerText || fieldset.textContent || '');
                    return normalize(fieldText.replace(/^Age\s*/i, ''));
                };

                // Preferred path: the Age field is in the main profile grid.
                const mainProfileFieldsets = Array.from(
                    document.querySelectorAll('div.grid.gap-4.grid-cols-2 fieldset')
                );
                for (const fieldset of mainProfileFieldsets) {
                    const legend = fieldset.querySelector('legend');
                    const label = normalize(legend ? (legend.innerText || legend.textContent || '') : '');
                    if (label.toLowerCase() === 'age') {
                        const value = getFieldsetValue(fieldset);
                        if (value) return value;
                    }
                }

                // Fallback: search all fieldsets, still requiring exact legend text "Age".
                const allFieldsets = Array.from(document.querySelectorAll('fieldset'));
                for (const fieldset of allFieldsets) {
                    const legend = fieldset.querySelector('legend');
                    const label = normalize(legend ? (legend.innerText || legend.textContent || '') : '');
                    if (label.toLowerCase() === 'age') {
                        const value = getFieldsetValue(fieldset);
                        if (value) return value;
                    }
                }

                // Last fallback: line-by-line visible body text. This is safer than a broad
                // regex because it avoids confusing "Age Group" with "Age".
                const bodyText = document.body ? (document.body.innerText || document.body.textContent || '') : '';
                const lines = bodyText.split(/\n+/).map(normalize).filter(Boolean);
                for (let i = 0; i < lines.length - 1; i++) {
                    if (lines[i].toLowerCase() === 'age') {
                        return lines[i + 1] || '';
                    }
                }

                return '';
                """
            ) or ""
            return re.sub(r"\s+", " ", str(raw_age)).strip()
        except Exception:
            return ""


    def _extract_kennel_card_website_memo(self) -> tuple[str, str]:
        """
        Return only the actual text body of the latest Kennel Card / Website Memo.

        This intentionally excludes:
          - the date
          - "Kennel Card / Website Memo"
          - "by username"
          - the rest of the animal profile page
        """
        try:
            result = self.driver.execute_script(
                r"""
                const normalize = (value) => (value || '').replace(/\s+/g, ' ').trim();

                const parseDate = (value) => {
                    if (!value) return 0;
                    const parts = value.split('/');
                    if (parts.length !== 3) return 0;
                    return new Date(Number(parts[2]), Number(parts[0]) - 1, Number(parts[1])).getTime();
                };

                const firstIndex = (text, regex) => {
                    const match = text.match(regex);
                    return match && typeof match.index === 'number' ? match.index : -1;
                };

                const stripKennelCardHeaderAndFooter = (rawText) => {
                    let text = normalize(rawText);
                    if (!text) return '';

                    // Keep only what comes after the Kennel Card / Website Memo header.
                    // Handles both:
                    //   03/14/2026 | Kennel Card / Website Memo by dbch_kat Meet Sully...
                    //   Kennel Card / Website Memo by dbch_kat Meet Sully...
                    const headerRegex = /(?:\d{2}\/\d{2}\/\d{4}\s*\|\s*)?Kennel Card\s*\/\s*Website Memo\s*(?:by\s+\S+)?\s*/ig;
                    let lastHeader = null;
                    let headerMatch;
                    while ((headerMatch = headerRegex.exec(text)) !== null) {
                        lastHeader = headerMatch;
                    }
                    if (lastHeader) {
                        text = text.slice(lastHeader.index + lastHeader[0].length);
                    }

                    // If the username appears separately on the next line/block, remove it too.
                    text = text.replace(/^by\s+\S+\s+/i, '');

                    // Do not let the scraper accidentally keep the rest of the page.
                    const stopCandidates = [
                        firstIndex(text, /\s+Show More\b/i),
                        firstIndex(text, /\s+All Memos\b/i),
                        firstIndex(text, /\s+\d{2}\/\d{2}\/\d{4}\s*\|\s*/i),
                        firstIndex(text, /\s+Latest\s+Medical\s+Type\b/i),
                        firstIndex(text, /\s+Template\s+Add Memo\b/i),
                    ].filter((index) => index >= 0);

                    if (stopCandidates.length > 0) {
                        text = text.slice(0, Math.min(...stopCandidates));
                    }

                    return normalize(text);
                };

                const kennelCardTypeId = '46503';
                const candidates = [];

                // Preferred path: the actual Livewire memo component stores the true memo body
                // in data.content. This avoids grabbing the visible, truncated "Show More" text.
                document.querySelectorAll('[wire\\:snapshot]').forEach((element) => {
                    let snapshot = {};
                    try {
                        snapshot = JSON.parse(element.getAttribute('wire:snapshot') || '{}');
                    } catch (error) {
                        snapshot = {};
                    }

                    const data = snapshot.data || {};
                    const typeId = data.typeId === undefined || data.typeId === null ? '' : String(data.typeId);
                    if (typeId !== kennelCardTypeId) return;

                    const elementText = normalize(element.innerText || element.textContent || '');
                    const rawContent = normalize(data.content || '');

                    let memoDate = '';
                    const dateMatch = elementText.match(/(\d{2}\/\d{2}\/\d{4})\s*\|\s*Kennel Card\s*\/\s*Website Memo/i);
                    if (dateMatch) memoDate = dateMatch[1];

                    const content = rawContent || stripKennelCardHeaderAndFooter(elementText);
                    if (!content) return;

                    candidates.push({
                        date: memoDate,
                        content: stripKennelCardHeaderAndFooter(content),
                        priority: rawContent ? 2 : 1,
                    });
                });

                if (candidates.length > 0) {
                    candidates.sort((a, b) => {
                        const dateDifference = parseDate(b.date) - parseDate(a.date);
                        if (dateDifference !== 0) return dateDifference;
                        return (b.priority || 0) - (a.priority || 0);
                    });
                    return { date: candidates[0].date || '', content: candidates[0].content || '' };
                }

                // Fallback: extract from visible page text, but only the part after the
                // Kennel Card / Website Memo header and before Show More / All Memos / next memo.
                const bodyText = document.body ? normalize(document.body.innerText || document.body.textContent || '') : '';
                const headerRegex = /(\d{2}\/\d{2}\/\d{4})\s*\|\s*Kennel Card\s*\/\s*Website Memo\s*(?:by\s+\S+)?\s*/ig;
                let match;
                while ((match = headerRegex.exec(bodyText)) !== null) {
                    const date = match[1] || '';
                    const remainder = bodyText.slice(match.index + match[0].length);
                    const content = stripKennelCardHeaderAndFooter(remainder);
                    if (content) {
                        candidates.push({ date, content, priority: 0 });
                    }
                }

                if (candidates.length > 0) {
                    candidates.sort((a, b) => parseDate(b.date) - parseDate(a.date));
                    return { date: candidates[0].date || '', content: candidates[0].content || '' };
                }

                return { date: '', content: '' };
                """
            ) or {}

            memo_date = str(result.get("date", "") or "").strip() if isinstance(result, dict) else ""
            memo_content = str(result.get("content", "") or "").strip() if isinstance(result, dict) else ""
            memo_content = re.sub(r"\s+", " ", memo_content).strip()
            memo_content = re.sub(
                r"^(?:\d{2}/\d{2}/\d{4}\s*\|\s*)?Kennel Card\s*/\s*Website Memo\s*(?:by\s+\S+)?\s*",
                "",
                memo_content,
                flags=re.IGNORECASE,
            ).strip()
            memo_content = re.sub(r"^by\s+\S+\s+", "", memo_content, flags=re.IGNORECASE).strip()
            memo_content = re.split(
                r"\s+(?:Show More\b|All Memos\b|\d{2}/\d{2}/\d{4}\s*\|\s*|Latest\s+Medical\s+Type\b|Template\s+Add Memo\b)",
                memo_content,
                maxsplit=1,
                flags=re.IGNORECASE,
            )[0].strip()
            return memo_content, memo_date
        except Exception:
            return "", ""


    def _open_all_memos_modal(self) -> bool:
        """
        Open the All Memos modal when the Kennel Card / Website Memo is not visible
        in the small memo panel on the animal profile page.
        """
        logger.debug("Trying to open All Memos modal...")

        # First try normal Selenium clicks on visible buttons/links.
        xpaths = [
            "//*[self::button or self::a][contains(normalize-space(.), 'All Memos')]",
            "//*[self::button or self::a][contains(normalize-space(.), 'Memos') and contains(normalize-space(.), '(')]",
        ]
        for xpath in xpaths:
            for element in self.driver.find_elements(By.XPATH, xpath):
                try:
                    text = (element.text or element.get_attribute("textContent") or "").strip()
                    if "All Memos" not in text:
                        continue
                    if not element.is_displayed() or not element.is_enabled():
                        continue
                    self.driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", element)
                    time.sleep(0.5)
                    try:
                        element.click()
                    except Exception:
                        self.driver.execute_script("arguments[0].click();", element)
                    self._wait_for_memos_modal()
                    return True
                except StaleElementReferenceException:
                    continue
                except Exception:
                    continue

        # Fallback: use JavaScript so we can find Livewire buttons whose attribute
        # names contain a colon, such as wire:click="...view-memos...".
        try:
            clicked = bool(self.driver.execute_script(
                r"""
                const isVisible = (element) => {
                    const style = window.getComputedStyle(element);
                    const rect = element.getBoundingClientRect();
                    return style && style.display !== 'none' && style.visibility !== 'hidden' && rect.width > 0 && rect.height > 0;
                };
                const buttons = Array.from(document.querySelectorAll('button, a'));
                const allMemosButton = buttons.find((button) => {
                    const text = (button.innerText || button.textContent || '').replace(/\s+/g, ' ').trim();
                    const wireClick = button.getAttribute('wire:click') || '';
                    return isVisible(button) && (
                        text.includes('All Memos') ||
                        wireClick.includes('view-memos') ||
                        wireClick.includes('animal.modals.view-memos')
                    );
                });
                if (!allMemosButton) return false;
                allMemosButton.scrollIntoView({block: 'center'});
                allMemosButton.click();
                return true;
                """
            ))
            if clicked:
                self._wait_for_memos_modal()
                return True
        except Exception:
            pass

        return False

    def _wait_for_memos_modal(self) -> None:
        """Wait until the All Memos modal has opened enough for memo components to load."""
        try:
            WebDriverWait(self.driver, WAIT_SHORT).until(
                lambda d: bool(d.execute_script(
                    r"""
                    const bodyText = document.body ? (document.body.innerText || '') : '';
                    return bodyText.includes('Sort By') && bodyText.includes('Filter By') && bodyText.includes('Memos');
                    """
                ))
            )
            time.sleep(1)
        except TimeoutException:
            # Some pages still load the memo components even if the modal heading check is slow.
            time.sleep(2)

    def _close_memos_modal_if_open(self) -> None:
        """Close the All Memos modal if it is open, so the next animal page starts cleanly."""
        close_xpaths = [
            "//button[@aria-label='Close']",
            "//*[self::button or self::a][normalize-space(.)='×']",
            "//*[self::button or self::a][normalize-space(.)='X']",
        ]
        for xpath in close_xpaths:
            for element in self.driver.find_elements(By.XPATH, xpath):
                try:
                    if not element.is_displayed() or not element.is_enabled():
                        continue
                    try:
                        element.click()
                    except Exception:
                        self.driver.execute_script("arguments[0].click();", element)
                    time.sleep(0.5)
                    return
                except Exception:
                    continue
        try:
            self.driver.find_element(By.TAG_NAME, "body").send_keys(Keys.ESCAPE)
            time.sleep(0.5)
        except Exception:
            pass

    def scrape_images(self, report_path: Path | None = None) -> None:
        logger.info("Scraping animal images, Size Group, Age, and Kennel Card / Website Memo text...")
        if report_path is None:
            report_path = DOWNLOAD_PATH / REPORT_DOWNLOAD_FILENAME

        target_ids = self._get_target_animal_ids_from_report(report_path)
        target_id_set = set(target_ids)
        animals_to_process: list[dict[str, str]] = []
        seen_ids: set[str] = set()

        self.driver.get(REPORT_URL)
        time.sleep(5)
        WebDriverWait(self.driver, WAIT_LONG).until(
            EC.presence_of_element_located((By.TAG_NAME, "table"))
        )

        page_number = 1
        max_pages = max(10, len(target_ids))

        while True:
            current_page_links = self._get_current_page_animal_links(target_id_set)
            new_links = 0
            for animal in current_page_links:
                animal_id = animal["Animal ID"]
                if animal_id not in seen_ids:
                    animals_to_process.append(animal)
                    seen_ids.add(animal_id)
                    new_links += 1

            logger.info(
                "Profile scrape page %s: found %s new animal links (total %s/%s)",
                page_number,
                new_links,
                len(seen_ids),
                len(target_ids),
            )

            if len(seen_ids) >= len(target_ids):
                break

            next_button = self._find_next_pagination_button()
            if next_button is None or page_number >= max_pages:
                break

            current_signature = "|".join(sorted(link["Animal ID"] for link in current_page_links))

            try:
                self.driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", next_button)
                time.sleep(0.5)
                self.driver.execute_script("arguments[0].click();", next_button)
            except Exception:
                try:
                    next_button.click()
                except Exception:
                    break

            page_changed = False
            end_time = time.time() + WAIT_LONG
            while time.time() < end_time:
                time.sleep(1)
                updated_links = self._get_current_page_animal_links(target_id_set)
                updated_signature = "|".join(sorted(link["Animal ID"] for link in updated_links))
                if updated_signature != current_signature:
                    page_changed = True
                    break

            if not page_changed:
                break

            page_number += 1

        missing_link_ids = [animal_id for animal_id in target_ids if animal_id not in seen_ids]
        if missing_link_ids:
            logger.warning(
                "Could not find report-page links for %s animal IDs. Will try direct animal-page URLs for them: %s",
                len(missing_link_ids),
                ", ".join(missing_link_ids[:25]),
            )
            for animal_id in missing_link_ids:
                animals_to_process.append({
                    "Animal ID": animal_id,
                    "url": f"https://new.shelterluv.com/animal/{animal_id}",
                })

        profile_rows: list[dict[str, str]] = []
        for animal in animals_to_process:
            animal_id = animal["Animal ID"]
            image_url = ""
            kennel_card_memo = ""
            kennel_card_memo_date = ""
            shelterluv_size_group = ""
            shelterluv_age = ""
            try:
                self.driver.get(animal["url"])
                time.sleep(2)
                WebDriverWait(self.driver, WAIT_SHORT).until(
                    lambda d: d.execute_script("return document.readyState") == "complete"
                )
                try:
                    WebDriverWait(self.driver, WAIT_SHORT).until(
                        lambda d: animal_id in d.page_source or bool(d.find_elements(By.CSS_SELECTOR, r"[wire\:snapshot]"))
                    )
                except TimeoutException:
                    pass

                image_url = self._extract_profile_image_url()
                shelterluv_size_group = self._extract_shelterluv_size_group()
                shelterluv_age = self._extract_shelterluv_age()
                kennel_card_memo, kennel_card_memo_date = self._extract_kennel_card_website_memo()

                # Sometimes the Kennel Card / Website Memo is not one of the latest
                # visible memo cards. In that case, open All Memos and scrape from
                # the modal, where the full Livewire memo component is loaded.
                if not kennel_card_memo and self._open_all_memos_modal():
                    kennel_card_memo, kennel_card_memo_date = self._extract_kennel_card_website_memo()
                    self._close_memos_modal_if_open()
            except Exception:
                image_url = ""
                kennel_card_memo = ""
                kennel_card_memo_date = ""
                shelterluv_size_group = ""
                shelterluv_age = ""

            profile_rows.append(
                {
                    "Animal ID": animal_id,
                    "Image URL": image_url,
                    "Shelterluv_Size_Group": shelterluv_size_group,
                    "Shelterluv_Age": shelterluv_age,
                    "Kennel_Card_Website_Memo": kennel_card_memo,
                    "Kennel_Card_Memo_Date": kennel_card_memo_date,
                }
            )
            logger.info(
                "Collected profile data for %s: image=%s, shelterluv_size_group=%s, shelterluv_age=%s, kennel_card_memo=%s",
                animal_id,
                "yes" if image_url else "no",
                shelterluv_size_group or "no",
                shelterluv_age or "no",
                "yes" if kennel_card_memo else "no",
            )
            time.sleep(0.5)

        profile_df = pd.DataFrame(
            profile_rows,
            columns=["Animal ID", "Image URL", "Shelterluv_Size_Group", "Shelterluv_Age", "Kennel_Card_Website_Memo", "Kennel_Card_Memo_Date"],
        )
        if not profile_df.empty:
            profile_df["Animal ID"] = profile_df["Animal ID"].astype(str).str.strip().str.upper()
            for column in ["Image URL", "Shelterluv_Size_Group", "Shelterluv_Age", "Kennel_Card_Website_Memo", "Kennel_Card_Memo_Date"]:
                if column not in profile_df.columns:
                    profile_df[column] = ""
                profile_df[column] = profile_df[column].fillna("").astype(str).str.strip()
            profile_df = profile_df.drop_duplicates(subset=["Animal ID"], keep="first")

        all_target_df = pd.DataFrame({"Animal ID": target_ids})
        output_df = all_target_df.merge(profile_df, on="Animal ID", how="left").fillna("")
        output_df.to_csv(DOWNLOAD_PATH / PIC_LINKS_FILENAME, index=False)
        logger.info(
            "Saved profile links, Size Groups, Ages, and memos to %s (found %s/%s image URLs, %s/%s Size Groups, %s/%s Ages, %s/%s Kennel Card memos)",
            DOWNLOAD_PATH / PIC_LINKS_FILENAME,
            int((output_df["Image URL"] != "").sum()),
            len(output_df),
            int((output_df["Shelterluv_Size_Group"] != "").sum()),
            len(output_df),
            int((output_df["Shelterluv_Age"] != "").sum()),
            len(output_df),
            int((output_df["Kennel_Card_Website_Memo"] != "").sum()),
            len(output_df),
        )

    def download_standard_report(self) -> Path:
        logger.info("Downloading standard report...")
        self.driver.get(REPORT_URL)
        time.sleep(5)

        WebDriverWait(self.driver, WAIT_LONG).until(
            EC.presence_of_element_located((By.TAG_NAME, "table"))
        )

        button = self.wait.until(
            EC.element_to_be_clickable((By.XPATH, "//button[contains(., 'Excel')]"))
        )
        download_started_at = time.time()
        try:
            button.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", button)

        return wait_for_download_and_rename(REPORT_DOWNLOAD_FILENAME, started_at=download_started_at)


    def _wait_for_document_ready(self, timeout: int = WAIT_LONG) -> None:
        WebDriverWait(self.driver, timeout).until(
            lambda d: d.execute_script("return document.readyState") == "complete"
        )

    def _wait_for_any_css(
        self,
        selectors: Iterable[str],
        timeout: int = WAIT_LONG,
        require_displayed: bool = True,
    ):
        selectors = list(selectors)

        def finder(driver):
            for selector in selectors:
                elements = driver.find_elements(By.CSS_SELECTOR, selector)
                for element in elements:
                    try:
                        if not require_displayed or element.is_displayed():
                            return element
                    except Exception:
                        continue
            return False

        return WebDriverWait(self.driver, timeout).until(finder)

    def _wait_for_any_xpath(
        self,
        xpaths: Iterable[str],
        timeout: int = WAIT_LONG,
        require_displayed: bool = True,
    ):
        xpaths = list(xpaths)

        def finder(driver):
            for xpath in xpaths:
                elements = driver.find_elements(By.XPATH, xpath)
                for element in elements:
                    try:
                        if not require_displayed or element.is_displayed():
                            return element
                    except Exception:
                        continue
            return False

        return WebDriverWait(self.driver, timeout).until(finder)

    def _select_dropdown_by_visible_text(
        self,
        selectors: Iterable[str],
        visible_text: str,
        timeout: int = WAIT_LONG,
    ):
        dropdown = self._wait_for_any_css(selectors, timeout=timeout, require_displayed=True)
        Select(dropdown).select_by_visible_text(visible_text)
        return dropdown

    def _close_window_and_return(self, window_to_close: str, return_to: str) -> None:
        try:
            self.driver.switch_to.window(window_to_close)
            self.driver.close()
        finally:
            self.driver.switch_to.window(return_to)


    def generate_custom_report(self) -> Path:
        logger.info("Generating custom report...")
        self.driver.get(CUSTOM_REPORT_URL)
        self._wait_for_document_ready()
        time.sleep(3)

        self._select_dropdown_by_visible_text(Selectors.REPORT_TYPE_DROPDOWNS, "Events", timeout=WAIT_LONG)
        time.sleep(2)

        topic_dropdown = self._wait_for_any_css(Selectors.REPORT_TOPIC_DROPDOWNS, timeout=WAIT_LONG)
        WebDriverWait(self.driver, WAIT_LONG).until(lambda d: len(Select(topic_dropdown).options) > 1)
        Select(topic_dropdown).select_by_visible_text("Intakes")
        time.sleep(2)

        start_date = (pd.Timestamp.now() - relativedelta(months=CUSTOM_REPORT_MONTHS_BACK)).strftime("%m/%d/%Y")
        self._set_visible_start_date(start_date)

        try:
            field_select = self._wait_for_any_css(Selectors.RULE_FIELD_SELECTORS, timeout=5)
        except TimeoutException:
            add_rule = self._wait_for_any_xpath(Selectors.ADD_RULE_XPATHS, timeout=WAIT_LONG)
            self.driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", add_rule)
            time.sleep(1)
            try:
                add_rule.click()
            except Exception:
                self.driver.execute_script("arguments[0].click();", add_rule)
            time.sleep(2)
            field_select = self._wait_for_any_css(Selectors.RULE_FIELD_SELECTORS, timeout=WAIT_LONG)

        Select(field_select).select_by_visible_text("Age (Months)")
        time.sleep(1)

        operator_select = self._wait_for_any_css(Selectors.RULE_OPERATOR_SELECTORS, timeout=WAIT_LONG)
        Select(operator_select).select_by_visible_text("Greater than")
        time.sleep(1)

        value_input = self._wait_for_any_css(Selectors.RULE_VALUE_SELECTORS, timeout=WAIT_LONG)
        value_input.clear()
        value_input.send_keys("0")
        time.sleep(1)

        original_window = self.driver.current_window_handle
        before_handles = set(self.driver.window_handles)
        run_button = self._wait_for_any_xpath(Selectors.RUN_REPORT_XPATHS, timeout=WAIT_LONG)
        self.driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", run_button)
        time.sleep(1)
        try:
            run_button.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", run_button)

        WebDriverWait(self.driver, WAIT_LONG).until(
            lambda d: len(set(d.window_handles) - before_handles) > 0
        )
        new_handle = list(set(self.driver.window_handles) - before_handles)[0]
        self.driver.switch_to.window(new_handle)
        self._wait_for_document_ready()
        time.sleep(3)

        excel_button = self._wait_for_any_xpath(Selectors.EXCEL_EXPORT_XPATHS, timeout=WAIT_LONG)
        self.driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", excel_button)
        time.sleep(1)
        download_started_at = time.time()
        try:
            excel_button.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", excel_button)

        file_path = wait_for_download_and_rename(CUSTOM_REPORT_FILENAME, timeout=300, started_at=download_started_at)
        self._close_window_and_return(new_handle, original_window)
        return file_path


    def generate_weight_change_report(self) -> Path:
        logger.info("Generating weight change report...")
        original_window = self.driver.current_window_handle
        self.driver.get(WEIGHT_CHANGE_REPORTS_URL)
        self._wait_for_document_ready()
        time.sleep(5)

        weight_change_element = self.wait.until(
            EC.presence_of_element_located((By.XPATH, "//td[contains(text(), 'Weight Change')]"))
        )
        self.driver.execute_script("arguments[0].scrollIntoView(true);", weight_change_element)
        time.sleep(2)

        start_date = pd.Timestamp.now() - relativedelta(months=CUSTOM_REPORT_MONTHS_BACK)

        try:
            row = weight_change_element.find_element(By.XPATH, "./ancestor::tr")
            run_report_button = row.find_element(By.CSS_SELECTOR, 'a[data-cy="secondary-button"]')
        except Exception:
            buttons = self.driver.find_elements(
                By.CSS_SELECTOR, 'a[data-cy="secondary-button"][href*="animal-weight-change"]'
            )
            if not buttons:
                raise RuntimeError("Could not find the Weight Change Run Report button")
            run_report_button = buttons[0]

        report_url = run_report_button.get_attribute("href") or ""
        if not report_url:
            raise RuntimeError("Could not get Weight Change report URL")

        separator = "&" if "?" in report_url else "?"
        report_url = f"{report_url}{separator}startDate={start_date.strftime('%Y-%m-%d')}"

        before_handles = set(self.driver.window_handles)
        self.driver.execute_script("window.open(arguments[0], '_blank');", report_url)
        WebDriverWait(self.driver, WAIT_LONG).until(
            lambda d: len(set(d.window_handles) - before_handles) > 0
        )
        new_handle = list(set(self.driver.window_handles) - before_handles)[0]
        self.driver.switch_to.window(new_handle)
        self._wait_for_document_ready()
        time.sleep(3)

        excel_button = self._wait_for_any_xpath(Selectors.EXCEL_EXPORT_XPATHS, timeout=WAIT_LONG)
        download_started_at = time.time()
        try:
            excel_button.click()
        except Exception:
            self.driver.execute_script("arguments[0].click();", excel_button)

        file_path = wait_for_download_and_rename(WEIGHT_CHANGE_REPORT_FILENAME, started_at=download_started_at)
        self._close_window_and_return(new_handle, original_window)
        return file_path

    def _set_visible_start_date(self, visible_date: str) -> None:
        # Try visible input first.
        try:
            date_input = WebDriverWait(self.driver, WAIT_SHORT).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, 'input[data-cy="startDate"]'))
            )
            date_input.clear()
            date_input.send_keys(visible_date)
            date_input.send_keys(Keys.TAB)
            time.sleep(1)
            return
        except Exception:
            pass

        # Fallback to JavaScript for Livewire-based controls.
        script = """
        const value = arguments[0];
        const selectors = ['input[data-cy="startDate"]', '#startDate'];
        for (const selector of selectors) {
            const el = document.querySelector(selector);
            if (el) {
                el.value = value;
                el.dispatchEvent(new Event('input', { bubbles: true }));
                el.dispatchEvent(new Event('change', { bubbles: true }));
                el.dispatchEvent(new Event('blur', { bubbles: true }));
                return true;
            }
        }
        return false;
        """
        if not self.driver.execute_script(script, visible_date):
            raise RuntimeError("Could not set the custom report start date")
        time.sleep(1)

    def cleanup(self) -> None:
        try:
            self.driver.quit()
        except Exception:
            pass


# =====================
# CSV CLEANING / MERGING
# =====================

ATTRIBUTE_ALIASES = {
    "active": "Active",
    "adult-only home preferred": "Adult-Only Home Preferred",
    "adult only home preferred": "Adult-Only Home Preferred",
    "affectionate": "Affectionate",
    "cuddly": "Cuddly",
    "food aggressive": "Food Aggressive",
    "friendly": "Friendly",
    "gentle": "Gentle",
    "good on leash": "Good-on-leash",
    "good-on-leash": "Good-on-leash",
    "good with kids": "Good with Kids",
    "good with other dogs": "Good with Other Dogs",
    "housebroken": "Housebroken",
    "housetrained": "Housebroken",
    "independent": "Independent",
    "kids 13+": "Kids 13+",
    "meet and greet required": "Meet and greet required",
    "no cats": "No Cats",
    "no chickens": "No chickens",
    "obedient and well mannered": "Obedient and Well Mannered",
    "playful": "Playful",
    "quiet": "Quiet",
    "quirky": "Quirky",
    "relaxed and mellow": "Relaxed and Mellow",
    "requires fenced yard": "Requires Fenced Yard",
    "separation anxiety": "Separation Anxiety",
    "shy": "Shy",
    "single dog home": "Single Dog Home",
    "special needs": "Special Needs",
}

REQUIRED_ATTRIBUTE_COLUMNS = [
    "Active", "Affectionate", "Cuddly", "Friendly", "Gentle",
    "Good-on-leash", "Independent", "Obedient and Well Mannered",
    "Playful", "Quiet", "Quirky", "Relaxed and Mellow", "Shy",
    "Single Dog Home", "Adult-Only Home Preferred", "No Cats", "Housebroken",
]

DISPLAY_ATTRIBUTE_COLUMNS = [
    "Active", "Affectionate", "Cuddly", "Friendly", "Gentle",
    "Good-on-leash", "Independent", "Obedient and Well Mannered",
    "Playful", "Quiet", "Quirky", "Relaxed and Mellow", "Shy", "Housebroken",
]

PROTECTED_NON_ATTRIBUTE_COLUMNS = {
    "Animal_ID", "Name", "Photo", "Image_URL", "Sex", "Status", "Days_in_Custody",
    "Days In Custody", "Dog_Attributes", "Age_Months", "Size_Group", "Shelterluv_Size_Group",
    "Shelterluv_Age", "Age_Group", "Weight", "Breed",
}


def _is_missing_value(value) -> bool:
    if value is None:
        return True
    if isinstance(value, float) and pd.isna(value):
        return True
    if isinstance(value, str) and value.strip() == "":
        return True
    return False


def clean_attribute_name(value: str) -> str:
    """Convert messy attribute strings into one canonical attribute name."""
    value = str(value).strip()

    # Remove leftovers from Python-list-looking strings such as "['Active']".
    value = value.replace("[", "")
    value = value.replace("]", "")
    value = value.replace("'", "")
    value = value.replace('"', "")

    # Normalize whitespace and punctuation spacing.
    value = re.sub(r"\s+", " ", value).strip()

    if value in {"", "-"}:
        return ""

    return ATTRIBUTE_ALIASES.get(value.lower(), value)


def _split_list_string(value) -> list[str]:
    """
    Split an attribute cell into clean attribute names.

    Handles all of these forms correctly:
      Active, No Cats
      ['Active', 'No Cats']
      ['No Cats']
      Active]
      ['Active'
    """
    if isinstance(value, list):
        raw_items = value
    else:
        if _is_missing_value(value):
            return []

        raw_value = str(value).strip()
        if raw_value in {"", "[]"}:
            return []

        # If the CSV contains a Python-list-looking string, parse it safely.
        # If parsing fails, fall back to comma splitting.
        try:
            parsed_value = ast.literal_eval(raw_value)
            if isinstance(parsed_value, (list, tuple, set)):
                raw_items = list(parsed_value)
            else:
                raw_items = [parsed_value]
        except Exception:
            raw_items = raw_value.split(",")

    cleaned_items: list[str] = []
    for item in raw_items:
        clean_item = clean_attribute_name(item)
        if clean_item and clean_item != "-" and clean_item not in cleaned_items:
            cleaned_items.append(clean_item)

    return cleaned_items


def _make_indicator_series(values: pd.Series) -> pd.Series:
    """Convert possible indicator values to clean 0/1 integers."""
    normalized = values.fillna(0).astype(str).str.strip().str.lower()
    return normalized.isin({"1", "1.0", "true", "yes", "y"}).astype(int)


def merge_duplicate_indicator_columns(df: pd.DataFrame) -> pd.DataFrame:
    """
    Merge accidental duplicate indicator columns caused by messy names.

    For example, these all become one column called Active:
      Active, 'Active', 'Active'], ['Active'

    These all become one column called No Cats:
      No Cats, 'No Cats', ['No Cats']
    """
    df = df.copy()
    column_groups: dict[str, list[str]] = {}

    for column in df.columns:
        if column in PROTECTED_NON_ATTRIBUTE_COLUMNS:
            continue
        clean_column = clean_attribute_name(column)
        if not clean_column or clean_column in PROTECTED_NON_ATTRIBUTE_COLUMNS:
            continue
        column_groups.setdefault(clean_column, []).append(column)

    for clean_column, matching_columns in column_groups.items():
        if len(matching_columns) == 1 and matching_columns[0] == clean_column:
            continue

        indicator_parts = [_make_indicator_series(df[col]) for col in matching_columns if col in df.columns]
        if not indicator_parts:
            continue

        merged_indicator = pd.concat(indicator_parts, axis=1).max(axis=1).astype(int)
        first_position = min(df.columns.get_loc(col) for col in matching_columns if col in df.columns)

        df = df.drop(columns=[col for col in matching_columns if col in df.columns], errors="ignore")
        df.insert(first_position, clean_column, merged_indicator)

    return df


def shelterluv_age_to_months(value) -> str:
    """
    Convert Shelterluv visible ages into whole months.

    Examples:
      4Y/1M/21D -> 49
      3y 6 months 7 days -> 42
      8M/2D -> 8
      21D -> 0

    Days are intentionally ignored instead of converted into decimals.
    Returns an empty string when the age is missing or cannot be parsed.
    """
    if _is_missing_value(value):
        return ""

    raw_value = str(value).strip()
    if raw_value == "":
        return ""

    # If a value is already numeric, treat it as months and remove decimals.
    numeric_value = pd.to_numeric(raw_value, errors="coerce")
    if pd.notna(numeric_value):
        return str(int(numeric_value))

    normalized = raw_value.lower()
    normalized = normalized.replace("/", " ")
    normalized = normalized.replace(",", " ")
    normalized = re.sub(r"\s+", " ", normalized).strip()

    years = 0
    months = 0
    found_age_piece = False

    year_match = re.search(r"(\d+)\s*(?:years?|yrs?|yr|y)\b", normalized, flags=re.IGNORECASE)
    if year_match:
        years = int(year_match.group(1))
        found_age_piece = True

    month_match = re.search(r"(\d+)\s*(?:months?|mos?|mo|mths?|mth|m)\b", normalized, flags=re.IGNORECASE)
    if month_match:
        months = int(month_match.group(1))
        found_age_piece = True

    # A days-only age should become 0 months.
    day_match = re.search(r"(\d+)\s*(?:days?|d)\b", normalized, flags=re.IGNORECASE)
    if day_match:
        found_age_piece = True

    if not found_age_piece:
        return ""

    return str((years * 12) + months)


def clean_month_value(value) -> str:
    """Return a month value with no decimal places, preserving blanks."""
    if _is_missing_value(value):
        return ""
    numeric_value = pd.to_numeric(str(value).strip(), errors="coerce")
    if pd.notna(numeric_value):
        return str(int(numeric_value))
    return str(value).strip()


def add_age_group_from_months(df: pd.DataFrame) -> pd.DataFrame:
    """Recalculate Age_Group from the final Age_Months column."""
    df = df.copy()
    if "Age_Months" not in df.columns:
        df["Age_Months"] = ""

    age_numeric = pd.to_numeric(df["Age_Months"], errors="coerce")
    df["Age_Group"] = np.select(
        [
            age_numeric.isna(),
            age_numeric < 6,
            (age_numeric >= 6) & (age_numeric < 18),
            (age_numeric >= 18) & (age_numeric < 84),
            age_numeric >= 84,
        ],
        ["", "Baby", "Young", "Adult", "Senior"],
        default="",
    )
    return df


def getCleanAppData(main_dir: Path, files: Iterable[str]) -> Path:
    files = list(files)
    whole_df = pd.read_excel(main_dir / files[0]).fillna("")
    weight_df = pd.read_excel(main_dir / files[1]).fillna("")
    age_df = pd.read_excel(main_dir / files[2]).fillna("")

    if "Animal Name" in whole_df.columns:
        whole_df = whole_df.rename(columns={"Animal Name": "Name"})

    whole_df = whole_df[whole_df["Species"] == "Dog"].copy()
    if "Species" in whole_df.columns:
        whole_df = whole_df.drop(columns=["Species"])

    breed_descriptors = {
        "Great", "German", "Golden", "American", "Irish", "Rhodesian",
        "Miniature", "Brussels", "Australian", "Pembroke Welsh", "Redbone",
        "Border", "Standard", "Wirehaired", "Bluetick", "Yorkshire", "Mix",
    }

    def combine_breeds(row: pd.Series) -> list[str]:
        breeds: list[str] = []
        for col in ["Primary Breed", "Secondary Breed"]:
            value = row.get(col, "")
            if value:
                breeds.extend([part.strip() for part in str(value).split(", ") if part.strip()])
        clean_breeds = []
        for breed in breeds:
            if breed not in breed_descriptors and breed not in clean_breeds:
                clean_breeds.append(breed)
        return clean_breeds

    # Save Breed as clean comma-separated text, not a Python list string.
    whole_df["Breed"] = whole_df.apply(lambda row: ", ".join(combine_breeds(row)), axis=1)
    whole_df = whole_df.drop(columns=[c for c in ["Primary Breed", "Secondary Breed"] if c in whole_df.columns])

    unused_columns = [
        "Altered", "Location", "Days Onsite", "Days Available", "Days In Status",
        "Completed Physical Exams", "Completed Behavior Assessments", "Completed Behavior Plans",
    ]
    whole_df = whole_df.drop(columns=[c for c in unused_columns if c in whole_df.columns], errors="ignore")

    # These two filters are intentionally left off so the app can decide what to show.
    # if "Status" in whole_df.columns:
    #     whole_df = whole_df[whole_df["Status"] != "In Training"].copy()
    #     whole_df = whole_df.drop(columns=["Status"])

    # if "Name" in whole_df.columns:
    #     whole_df = whole_df[~whole_df["Name"].astype(str).str.lower().str.contains("manners", na=False)].copy()

    # Save Dog Attributes as clean comma-separated text, not a Python list string.
    # This prevents duplicate columns like Active, 'Active'], ['Active', etc.
    whole_df["Dog Attributes"] = whole_df["Attributes"].apply(
        lambda value: ", ".join(_split_list_string(value))
    )
    whole_df = whole_df.drop(columns=["Attributes"], errors="ignore")

    weight_map = (
        weight_df[["Animal ID", "Weight"]]
        .dropna(subset=["Animal ID"])
        .drop_duplicates(subset=["Animal ID"], keep="last")
        .set_index("Animal ID")["Weight"]
    )
    whole_df["Weight"] = whole_df["Animal ID"].map(weight_map).fillna("")
    whole_df["Weight (lbs.)"] = whole_df["Weight"].astype(str).str.replace(" lbs", "", regex=False)
    whole_df = whole_df.drop(columns=["Weight"])

    age_map = (
        age_df[["Animal ID", "Age (Months)"]]
        .dropna(subset=["Animal ID"])
        .drop_duplicates(subset=["Animal ID"], keep="last")
        .set_index("Animal ID")["Age (Months)"]
    )
    whole_df["Age (Months)"] = whole_df["Animal ID"].map(age_map).fillna("")

    whole_df = whole_df.rename(
        columns={
            "Animal ID": "Animal_ID",
            "Days in Custody": "Days_in_Custody",
            "Dog Attributes": "Dog_Attributes",
            "Weight (lbs.)": "Weight",
            "Age (Months)": "Age_Months",
        }
    )

    age_numeric = pd.to_numeric(whole_df["Age_Months"], errors="coerce")
    whole_df["Age_Group"] = np.select(
        [
            age_numeric.isna(),
            age_numeric < 6,
            (age_numeric >= 6) & (age_numeric < 18),
            (age_numeric >= 18) & (age_numeric < 84),
            age_numeric >= 84,
        ],
        ["", "Baby", "Young", "Adult", "Senior"],
        default="",
    )

    weight_numeric = pd.to_numeric(whole_df["Weight"], errors="coerce")
    whole_df["Size_Group"] = np.select(
        [
            weight_numeric.isna(),
            weight_numeric < 28,
            (weight_numeric >= 28) & (weight_numeric < 60),
            weight_numeric >= 60,
        ],
        ["", "Small", "Medium", "Large"],
        default="",
    )

    output_path = main_dir / MATCH_DATASET_FILENAME
    whole_df.to_csv(output_path, index=False)
    return output_path


def getBreedAppData(main_dir: Path, breed_files: Iterable[str]) -> Path:
    breed_files = list(breed_files)
    whole_df = pd.read_csv(main_dir / breed_files[0]).fillna("")

    def normalize_breed_tokens(raw_value: str) -> list[str]:
        value = str(raw_value)
        value = value.replace(" '", "")
        value = value.replace("[", "").replace("]", "").replace("'", "")
        value = value.replace(" Breed (Medium)", "").replace(" Breed (Small)", "").replace(" Breed (Large)", "")
        value = value.replace("Black ", "").replace("Yellow ", "").replace("American ", "")
        value = value.replace("Rat", "Rat Terrier")
        value = value.replace("Plott", "Plott Hound").replace("Basset", "Basset Hound").replace("Shetland", "Sheltie")
        tokens = [item.strip() for item in value.split(",") if item.strip()]

        clean_tokens = []
        for token in tokens:
            if token not in clean_tokens:
                clean_tokens.append(token)
        return clean_tokens

    breed_lists = whole_df["Breed"].apply(normalize_breed_tokens)
    unique_breeds = sorted({breed for items in breed_lists for breed in items})

    breed_columns = {
        breed: breed_lists.apply(lambda items, b=breed: 1 if b in items else 0)
        for breed in unique_breeds
    }

    df_result = pd.concat([whole_df.drop(columns=["Breed"]), pd.DataFrame(breed_columns)], axis=1)
    output_path = main_dir / BREED_FILENAME
    df_result.to_csv(output_path, index=False)
    return output_path


def getAttributeAppData(main_dir: Path, attribute_files: Iterable[str]) -> Path:
    attribute_files = list(attribute_files)
    whole_df = pd.read_csv(main_dir / attribute_files[0]).fillna("")

    attribute_lists = whole_df["Dog_Attributes"].apply(_split_list_string)
    unique_attributes = sorted({attribute for items in attribute_lists for attribute in items if attribute != "-"})

    attribute_columns = {
        attribute: attribute_lists.apply(lambda items, a=attribute: 1 if a in items else 0)
        for attribute in unique_attributes
    }

    # Make sure the columns used by the Shiny app always exist.
    for attribute in REQUIRED_ATTRIBUTE_COLUMNS:
        attribute_columns.setdefault(attribute, pd.Series([0] * len(whole_df)))

    age_group = whole_df["Age_Group"]
    whole_df = whole_df.drop(columns=["Age_Group"])
    df_intermediate = pd.concat([whole_df, age_group], axis=1)

    df_result = pd.concat([df_intermediate, pd.DataFrame(attribute_columns)], axis=1)

    # Safety pass: if older messy columns still exist for any reason, merge them.
    df_result = merge_duplicate_indicator_columns(df_result)

    weight_col = df_result["Weight"]
    df_result = df_result.drop(columns=["Weight"])

    for attribute in DISPLAY_ATTRIBUTE_COLUMNS:
        if attribute not in df_result.columns:
            df_result[attribute] = 0

    save_atts = df_result[DISPLAY_ATTRIBUTE_COLUMNS].copy()
    df_result = df_result.drop(columns=DISPLAY_ATTRIBUTE_COLUMNS)
    df_result = pd.concat([df_result, weight_col, save_atts], axis=1)

    photo_links = pd.read_csv(main_dir / attribute_files[1]).fillna("")
    photo_links = photo_links.rename(columns={"Animal ID": "Animal_ID", "Image URL": "Image_URL"})
    photo_links["Animal_ID"] = photo_links["Animal_ID"].astype(str).str.strip().str.upper()

    for column in ["Image_URL", "Shelterluv_Size_Group", "Shelterluv_Age", "Kennel_Card_Website_Memo", "Kennel_Card_Memo_Date"]:
        if column not in photo_links.columns:
            photo_links[column] = ""
        photo_links[column] = photo_links[column].fillna("").astype(str).str.strip()

    photo_links["Image_URL"] = photo_links["Image_URL"].replace({"Error": "", "Not Found": ""})
    photo_links = photo_links[photo_links["Animal_ID"] != ""].copy()
    photo_links = photo_links.drop_duplicates(subset=["Animal_ID"], keep="first")
    photo_links["Photo"] = photo_links["Image_URL"].apply(
        lambda url: f"<img src='{url}' height='100'></img>" if url else ""
    )

    final_df = df_result.copy()
    final_df["Animal_ID"] = final_df["Animal_ID"].astype(str).str.strip().str.upper()
    profile_columns = [
        "Animal_ID",
        "Image_URL",
        "Photo",
        "Shelterluv_Size_Group",
        "Shelterluv_Age",
        "Kennel_Card_Website_Memo",
        "Kennel_Card_Memo_Date",
    ]
    final_df = final_df.merge(
        photo_links[profile_columns],
        on="Animal_ID",
        how="left",
    )

    # Replace Age_Months with the website age converted to whole months.
    # Days are ignored, so 3Y/6M/7D becomes 42.
    if "Age_Months" not in final_df.columns:
        final_df["Age_Months"] = ""
    shelterluv_age_months = final_df["Shelterluv_Age"].apply(shelterluv_age_to_months)
    has_shelterluv_age = shelterluv_age_months.astype(str).str.strip() != ""
    final_df.loc[has_shelterluv_age, "Age_Months"] = shelterluv_age_months[has_shelterluv_age]
    final_df["Age_Months"] = final_df["Age_Months"].apply(clean_month_value)
    final_df = final_df.drop(columns=["Shelterluv_Age"], errors="ignore")

    # Replace the calculated Size_Group with the Shelterluv profile Size Group.
    # If Shelterluv is blank for an animal, keep the old calculated Size_Group value.
    if "Size_Group" not in final_df.columns:
        final_df["Size_Group"] = ""
    shelterluv_size_group = final_df["Shelterluv_Size_Group"].fillna("").astype(str).str.strip()
    has_shelterluv_size_group = shelterluv_size_group != ""
    final_df.loc[has_shelterluv_size_group, "Size_Group"] = shelterluv_size_group[has_shelterluv_size_group]
    final_df = final_df.drop(columns=["Shelterluv_Size_Group"], errors="ignore")

    # Since Age_Months has now been replaced, make Age_Group agree with the final value.
    final_df = add_age_group_from_months(final_df)

    final_df = merge_duplicate_indicator_columns(final_df)

    preferred_front = [
        "Animal_ID",
        "Name",
        "Photo",
        "Image_URL",
        "Kennel_Card_Website_Memo",
        "Kennel_Card_Memo_Date",
    ]
    ordered_cols = [col for col in preferred_front if col in final_df.columns] + [
        col for col in final_df.columns if col not in preferred_front
    ]
    final_df = final_df[ordered_cols]

    output_path = main_dir / FINAL_OUTPUT_FILENAME
    final_df.to_csv(output_path, index=False)
    return output_path




# =====================
# JSON OUTPUT FOR WIX
# =====================

def standardize_json_column_name(value: str) -> str:
    """
    Match the column-name cleanup used in the Shiny app and Wix code.

    Examples:
      "Animal ID" -> "Animal_ID"
      "Good-on-leash" -> "Good_on_leash"
      "Adult-Only Home Preferred" -> "Adult_Only_Home_Preferred"
    """
    value = str(value).strip()
    value = re.sub(r"[^A-Za-z0-9]+", "_", value)
    value = re.sub(r"_+", "_", value)
    value = re.sub(r"^_|_$", "", value)
    return value


def make_unique_column_names(columns: Iterable[str]) -> list[str]:
    """
    Ensure JSON keys are unique after standardizing column names.

    This protects against cases where two CSV columns differ only by punctuation,
    such as "Good-on-leash" and "Good_on_leash".
    """
    seen: dict[str, int] = {}
    unique_columns: list[str] = []

    for column in columns:
        base_name = standardize_json_column_name(column) or "Column"
        count = seen.get(base_name, 0)

        if count == 0:
            unique_name = base_name
        else:
            unique_name = f"{base_name}_{count + 1}"

        seen[base_name] = count + 1
        unique_columns.append(unique_name)

    return unique_columns




def create_fallback_age_report(main_dir: Path) -> Path:
    """
    Create a minimal age report when the custom Shelterluv age report download fails.

    This keeps the rest of the pipeline running. In the later merge step, Age_Months
    is replaced by Shelterluv_Age scraped from each animal profile when available,
    so this fallback usually only affects animals whose profile age could not be scraped.
    """
    main_dir = Path(main_dir)
    standard_report_path = main_dir / REPORT_DOWNLOAD_FILENAME
    fallback_path = main_dir / CUSTOM_REPORT_FILENAME

    animal_ids: list[str] = []
    try:
        standard_df = pd.read_excel(standard_report_path).fillna("")
        animal_id_column = next(
            (col for col in ["Animal ID", "Animal_ID", "AnimalID"] if col in standard_df.columns),
            None,
        )
        if animal_id_column is not None:
            animal_ids = (
                standard_df[animal_id_column]
                .astype(str)
                .str.strip()
                .replace("", pd.NA)
                .dropna()
                .drop_duplicates()
                .tolist()
            )
    except Exception as exc:
        logger.warning("Could not read standard report while making fallback age report: %s", exc)

    fallback_df = pd.DataFrame({"Animal ID": animal_ids, "Age (Months)": [""] * len(animal_ids)})
    fallback_df.to_excel(fallback_path, index=False)
    logger.warning(
        "Created fallback age report at %s with %s animals and blank Age (Months).",
        fallback_path,
        len(fallback_df),
    )
    return fallback_path

def write_wix_json(csv_path: Path, json_path: Path | None = None) -> Path:
    """
    Convert the final cleaned CSV into a Wix-friendly JSON file.

    The output is a list of records:
      [
        {"Animal_ID": "...", "Name": "...", "Image_URL": "..."},
        ...
      ]

    Wix Velo can load this directly with fetch().
    """
    csv_path = Path(csv_path)

    if json_path is None:
        json_path = csv_path.with_name(FINAL_JSON_OUTPUT_FILENAME)
    else:
        json_path = Path(json_path)

    df = pd.read_csv(csv_path).fillna("")
    df.columns = make_unique_column_names(df.columns)

    # Keep indicator columns as 0/1 where possible, while preserving ordinary text.
    for column in df.columns:
        if column in {
            "Animal_ID",
            "Name",
            "Photo",
            "Image_URL",
            "Kennel_Card_Website_Memo",
            "Kennel_Card_Memo_Date",
            "Sex",
            "Status",
            "Days_in_Custody",
            "Dog_Attributes",
            "Age_Group",
            "Size_Group",
            "Breed",
        }:
            continue

        numeric_values = pd.to_numeric(df[column], errors="coerce")
        non_blank = df[column].astype(str).str.strip() != ""

        if non_blank.any() and numeric_values[non_blank].notna().all():
            if (numeric_values.dropna() % 1 == 0).all():
                df[column] = numeric_values.fillna(0).astype(int)
            else:
                df[column] = numeric_values.where(numeric_values.notna(), "")

    records = df.to_dict(orient="records")

    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(
        json.dumps(records, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )

    return json_path


# =====================
# MAIN
# =====================

def main() -> None:
    if not USERNAME or not PASSWORD:
        raise ValueError("Set USERNAME and PASSWORD at the top of the script before running it.")

    scraper = ShelterLuvScraper()
    try:
        scraper.login()
        standard_report_path = scraper.download_standard_report()
        scraper.scrape_images(standard_report_path)
        scraper.generate_weight_change_report()
        try:
            scraper.generate_custom_report()
        except Exception as exc:
            if not ALLOW_AGE_REPORT_FALLBACK:
                raise
            logger.warning("Custom age report failed, so the scraper will use a fallback age file: %s", exc)
            logger.warning(traceback.format_exc())
            create_fallback_age_report(DOWNLOAD_PATH)

        logger.info("Cleaning and merging CSV data...")
        getCleanAppData(
            DOWNLOAD_PATH,
            [REPORT_DOWNLOAD_FILENAME, WEIGHT_CHANGE_REPORT_FILENAME, CUSTOM_REPORT_FILENAME],
        )
        getBreedAppData(DOWNLOAD_PATH, [MATCH_DATASET_FILENAME])
        final_file = getAttributeAppData(DOWNLOAD_PATH, [BREED_FILENAME, PIC_LINKS_FILENAME])
        final_json_file = write_wix_json(final_file)

        logger.info("Done. Final CSV output: %s", final_file)
        logger.info("Done. Final JSON output: %s", final_json_file)
        print(f"\nFinal CSV file created: {final_file}")
        print(f"Final JSON file created: {final_json_file}")
    except Exception as exc:
        logger.error("Scraper failed: %s", exc)
        logger.error(traceback.format_exc())
        raise
    finally:
        scraper.cleanup()


if __name__ == "__main__":
    main()
