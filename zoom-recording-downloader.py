#!/usr/bin/env python3

# Program Name: zoom-recording-downloader.py
# Description:  Zoom Recording Downloader is a cross-platform Python script
#               that uses Zoom's API (v2) to download and organize all
#               cloud recordings from a Zoom account onto local storage.
#               This Python script uses the OAuth method of accessing the Zoom API
# Created:      2020-04-26
# Author:       Ricardo Rodrigues
# Website:      https://github.com/ricardorodrigues-ca/zoom-recording-downloader
# Forked from:  https://gist.github.com/danaspiegel/c33004e52ffacb60c24215abf8301680

# System modules
import base64
import csv
import json
import os
import re as regex
import signal
import sys as system
import time
from datetime import datetime, date, timezone, timedelta
from urllib.parse import quote

# Installed modules
import dateutil.parser as parser
import pathvalidate as path_validate
import requests
import tqdm as progress_bar
from zoneinfo import ZoneInfo
from google_drive_client import GoogleDriveClient

class Color:
    PURPLE = "\033[95m"
    CYAN = "\033[96m"
    DARK_CYAN = "\033[36m"
    BLUE = "\033[94m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"
    END = "\033[0m"

CONF_PATH = "zoom-recording-downloader.conf"

# Load configuration file and check for proper JSON syntax
try:
    with open(CONF_PATH, encoding="utf-8-sig") as json_file:
        CONF = json.loads(json_file.read())
except json.JSONDecodeError as e:
    print(f"{Color.RED}### Error parsing JSON in {CONF_PATH}: {e}")
    system.exit(1)
except FileNotFoundError:
    print(f"{Color.RED}### Configuqration file {CONF_PATH} not found")
    system.exit(1)
except Exception as e:
    print(f"{Color.RED}### Unexpected error: {e}")
    system.exit(1)

def config(section, key, default=''):
    try:
        return CONF[section][key]
    except KeyError:
        if default == LookupError:
            print(f"{Color.RED}### No value provided for {section}:{key} in {CONF_PATH}")
            system.exit(1)
        else:
            return default

ACCOUNT_ID = config("OAuth", "account_id", LookupError)
CLIENT_ID = config("OAuth", "client_id", LookupError)
CLIENT_SECRET = config("OAuth", "client_secret", LookupError)

APP_VERSION = "3.1 (Google Drive Edition)"

API_ENDPOINT_USER_LIST = "https://api.zoom.us/v2/users"

RECORDING_START_YEAR = config("Recordings", "start_year", date.today().year)
RECORDING_START_MONTH = config("Recordings", "start_month", 1)
RECORDING_START_DAY = config("Recordings", "start_day", 1)
RECORDING_START_DATE = parser.parse(config("Recordings", "start_date", f"{RECORDING_START_YEAR}-{RECORDING_START_MONTH}-{RECORDING_START_DAY}")).replace(tzinfo=timezone.utc)
RECORDING_END_DATE = parser.parse(config("Recordings", "end_date", str(date.today()))).replace(tzinfo=timezone.utc)
DOWNLOAD_DIRECTORY = config("Storage", "download_dir", 'downloads')
COMPLETED_MEETING_IDS_LOG = config("Storage", "completed_log", 'completed-downloads.log')
USAGE_CACHE_FILE = config("Storage", "usage_cache", 'usage-cache.json')
ARCHIVE_SETTINGS_FILE = config("Storage", "archive_settings", 'archive-settings.json')
ZOOM_CACHE_FILE = config("Storage", "zoom_cache", 'zoom-recordings-cache.json')
DRIVE_CACHE_FILE = config("Storage", "drive_cache", 'drive-lookup-cache.json')
LOG_FILE = config("Storage", "log_file", 'zoom-downloader.log')
LOG_MAX_AGE_HOURS = int(config("Storage", "log_max_age_hours", 24))
COMPLETED_MEETING_IDS = set()

# Lookup caches (loaded by main()/configure_caches). USE_* gates whether we read
# from them; they are always *written* so later runs can reuse the answers.
ZOOM_RECORDINGS_CACHE = {}
DRIVE_LOOKUP_CACHE = {}
USE_ZOOM_CACHE = False
USE_DRIVE_CACHE = False

# Wall-clock start of the current archive/dry-run, for elapsed-time progress.
ARCHIVE_START_TS = None

# Original streams, captured before stdout/stderr are tee'd to the log file.
ORIGINAL_STDOUT = None
ORIGINAL_STDERR = None

MEETING_TIMEZONE = ZoneInfo(config("Recordings", "timezone", 'UTC'))
MEETING_STRFTIME = config("Recordings", "strftime", '%Y.%m.%d - %I.%M %p UTC')
MEETING_FILENAME = config("Recordings", "filename", '{meeting_time} - {topic} - {rec_type} - {recording_id}.{file_extension}')
MEETING_FOLDER = config("Recordings", "folder", '{topic} - {meeting_time}')

# Google Drive configuration
GDRIVE_ENABLED = False
GDRIVE_CREDENTIALS_FILE = config("GoogleDrive", "credentials_file", "service-account.json")
GDRIVE_ROOT_FOLDER = config("GoogleDrive", "root_folder_name", "zoom-recording-downloader")
GDRIVE_RETRY_DELAY = int(config("GoogleDrive", "retry_delay", "5"))
GDRIVE_MAX_RETRIES = int(config("GoogleDrive", "max_retries", "3"))
GDRIVE_FAILED_LOG = config("GoogleDrive", "failed_log", "failed-uploads.log")


_ANSI_RE = regex.compile(r"\x1b\[[0-9;]*m")


class _Tee:
    """ Write the same data to several streams (console + log file). """
    def __init__(self, *streams):
        self.streams = streams

    def write(self, data):
        for stream in self.streams:
            try:
                stream.write(data)
            except Exception:
                pass

    def flush(self):
        for stream in self.streams:
            try:
                stream.flush()
            except Exception:
                pass


class _LogFile:
    """ Wrap the log file object, stripping ANSI color codes before writing so the
        on-disk log stays plain text. """
    def __init__(self, fd):
        self.fd = fd

    def write(self, data):
        self.fd.write(_ANSI_RE.sub("", data))

    def flush(self):
        self.fd.flush()


def _log_started_at(path):
    """ Return the datetime recorded on the log's first line, or None. """
    try:
        with open(path, "r", encoding="utf-8") as fd:
            first = fd.readline().strip()
    except (FileNotFoundError, OSError):
        return None
    marker = "# log started: "
    if first.startswith(marker):
        try:
            return parser.parse(first[len(marker):])
        except (ValueError, OverflowError):
            return None
    return None


def setup_logging():
    """ Tee every stdout/stderr line to LOG_FILE so all output is captured. If the
        existing log was started more than LOG_MAX_AGE_HOURS ago, it is first
        rotated to a timestamped file and a fresh log is begun. """
    global ORIGINAL_STDOUT, ORIGINAL_STDERR
    now = datetime.now(timezone.utc)
    rotated_to = None

    if os.path.exists(LOG_FILE):
        started = _log_started_at(LOG_FILE)
        if started is None:
            # No marker (older log) — fall back to the file's modification time.
            started = datetime.fromtimestamp(os.path.getmtime(LOG_FILE), tz=timezone.utc)
        if (now - started).total_seconds() >= LOG_MAX_AGE_HOURS * 3600:
            base, ext = os.path.splitext(LOG_FILE)
            rotated_to = f"{base}-{started.strftime('%Y%m%d-%H%M%S')}{ext}"
            try:
                os.replace(LOG_FILE, rotated_to)
            except OSError:
                rotated_to = None

    new_log = not os.path.exists(LOG_FILE)
    log_fd = open(LOG_FILE, "a", encoding="utf-8", buffering=1)
    if new_log:
        log_fd.write(f"# log started: {now.isoformat()}\n")

    ORIGINAL_STDOUT = system.stdout
    ORIGINAL_STDERR = system.stderr
    system.stdout = _Tee(ORIGINAL_STDOUT, _LogFile(log_fd))
    system.stderr = _Tee(ORIGINAL_STDERR, _LogFile(log_fd))

    if rotated_to:
        print(
            f"{Color.DARK_CYAN}Previous log was older than {LOG_MAX_AGE_HOURS}h; "
            f"rotated to {rotated_to}{Color.END}"
        )
    print(f"{Color.DARK_CYAN}Logging all output to {LOG_FILE}{Color.END}")


def setup_google_drive(auto=False):
    """Initialize Google Drive client with OAuth authentication.
       In auto mode, failures return None without any interactive prompt."""
    try:
        drive_client = GoogleDriveClient(CONF.get('GoogleDrive', {}))
        if not drive_client.authenticate():
            if auto:
                return None
            choice = input("Would you like to continue with local storage instead? (y/n): ")
            if choice.lower() != 'y':
                system.exit(1)
            return None

        if not drive_client.initialize_root_folder():
            print(f"{Color.RED}### Failed to create root folder in Google Drive{Color.END}")
            if auto:
                return None
            choice = input("Would you like to continue with local storage instead? (y/n): ")
            if choice.lower() != 'y':
                system.exit(1)
            return None

        return drive_client
    except Exception as e:
        print(f"{Color.RED}### Google Drive initialization failed: {str(e)}{Color.END}")
        if auto:
            return None
        choice = input("Would you like to continue with local storage instead? (y/n): ")
        if choice.lower() != 'y':
            system.exit(1)
        return None




def load_access_token():
    """ OAuth function, thanks to https://github.com/freelimiter
    """
    url = f"https://zoom.us/oauth/token?grant_type=account_credentials&account_id={ACCOUNT_ID}"

    client_cred = f"{CLIENT_ID}:{CLIENT_SECRET}"
    client_cred_base64_string = base64.b64encode(client_cred.encode("utf-8")).decode("utf-8")

    headers = {
        "Authorization": f"Basic {client_cred_base64_string}",
        "Content-Type": "application/x-www-form-urlencoded"
    }

    response = json.loads(requests.request("POST", url, headers=headers).text)

    global ACCESS_TOKEN
    global AUTHORIZATION_HEADER

    try:
        ACCESS_TOKEN = response["access_token"]
        AUTHORIZATION_HEADER = {
            "Authorization": f"Bearer {ACCESS_TOKEN}",
            "Content-Type": "application/json"
        }

    except KeyError:
        print(f"{Color.RED}### The key 'access_token' wasn't found.{Color.END}")


def get_users():
    """ loop through pages and return all users """
    response = requests.get(url=API_ENDPOINT_USER_LIST, headers=AUTHORIZATION_HEADER)

    if not response.ok:
        print(response)
        print(
            f"{Color.RED}### Could not retrieve users. Please make sure that your access "
            f"token is still valid{Color.END}"
        )

        system.exit(1)

    page_data = response.json()
    total_pages = int(page_data["page_count"]) + 1

    all_users = []

    for page in range(1, total_pages):
        url = f"{API_ENDPOINT_USER_LIST}?page_number={str(page)}"
        user_data = requests.get(url=url, headers=AUTHORIZATION_HEADER).json()
        users = ([
            (
                user["email"],
                user["id"],
                user.get("first_name", ""),  # Use .get() with a default value
                user.get("last_name", "")    # Use .get() with a default value
            )
            for user in user_data["users"]
        ])

        all_users.extend(users)

    return all_users


def format_filename(params):
    file_extension = params["file_extension"].lower()
    recording = params["recording"]
    recording_id = params["recording_id"]
    recording_type = params["recording_type"]
    email=params["email"]	

    invalid_chars_pattern = r'[<>:"/\\|?*\x00-\x1F]'
    topic = regex.sub(invalid_chars_pattern, '', recording["topic"])
    rec_type = recording_type.replace("_", " ").title()
    meeting_time_utc = parser.parse(recording["start_time"]).replace(tzinfo=timezone.utc)
    meeting_time_local = meeting_time_utc.astimezone(MEETING_TIMEZONE)
    year = meeting_time_local.strftime("%Y")
    month = meeting_time_local.strftime("%m")
    day = meeting_time_local.strftime("%d")
    meeting_time = meeting_time_local.strftime(MEETING_STRFTIME)

    filename = MEETING_FILENAME.format(**locals())
    folder = MEETING_FOLDER.format(**locals())
    return (filename, folder)


def get_downloads(recording):
    if not recording.get("recording_files"):
        raise Exception

    downloads = []
    for download in recording["recording_files"]:
        file_type = download["file_type"]
        file_extension = download["file_extension"]
        recording_id = download["id"]

        if file_type == "":
            recording_type = "incomplete"
        elif file_type != "TIMELINE":
            recording_type = download["recording_type"]
        else:
            recording_type = download["file_type"]

        # must append access token to download_url
        download_url = f"{download['download_url']}?access_token={ACCESS_TOKEN}"
        downloads.append((file_type, file_extension, download_url, recording_type, recording_id))

    return downloads


def get_recordings(email, page_size, rec_start_date, rec_end_date):
    return {
        "userId": email,
        "page_size": page_size,
        "from": rec_start_date,
        "to": rec_end_date
    }


def per_delta(start, end, delta):
    """ Generator used to create deltas for recording start and end dates
    """
    curr = start
    while curr < end:
        yield curr, min(curr + delta, end)
        curr += delta


def list_recordings(email, rec_start_date=None, rec_end_date=None):
    """ Start date now split into YEAR, MONTH, and DAY variables (Within 6 month range)
        then get recordings within that range. Defaults to the globally configured
        range, but an explicit start/end may be passed (used by the monthly report).
    """

    rec_start_date = rec_start_date or RECORDING_START_DATE
    rec_end_date = rec_end_date or RECORDING_END_DATE

    recordings = []
    fetched_new = False

    for start, end in per_delta(rec_start_date, rec_end_date, timedelta(days=30)):
        cache_key = f"{email}|{start.isoformat()}|{end.isoformat()}"
        if USE_ZOOM_CACHE and cache_key in ZOOM_RECORDINGS_CACHE:
            print(
                f"{Color.DARK_CYAN}[zoom cache] hit — {email} "
                f"{start.date()}..{end.date()} (no Zoom API call){Color.END}"
            )
            recordings.extend(ZOOM_RECORDINGS_CACHE[cache_key])
            continue

        post_data = get_recordings(email, 300, start, end)
        response = requests.get(
            url=f"https://api.zoom.us/v2/users/{email}/recordings",
            headers=AUTHORIZATION_HEADER,
            params=post_data
        )
        recordings_data = response.json()
        if "meetings" in recordings_data:
            meetings = recordings_data["meetings"]
            recordings.extend(meetings)
            ZOOM_RECORDINGS_CACHE[cache_key] = meetings
            fetched_new = True
            reason = "miss" if USE_ZOOM_CACHE else "disabled"
            print(
                f"{Color.DARK_CYAN}[zoom cache] {reason} — {email} "
                f"{start.date()}..{end.date()}: called Zoom API, cache updated{Color.END}"
            )
        else:
            print(f"No 'meetings' key found in response for {email} from {start} to {end}")

    if fetched_new:
        save_zoom_cache()

    return recordings


def download_recording(download_url, email, filename, folder_name):
    dl_dir = os.sep.join([DOWNLOAD_DIRECTORY, folder_name])
    sanitized_download_dir = path_validate.sanitize_filepath(dl_dir)
    sanitized_filename = path_validate.sanitize_filename(filename)
    full_filename = os.sep.join([sanitized_download_dir, sanitized_filename])

    os.makedirs(sanitized_download_dir, exist_ok=True)

    response = requests.get(download_url, stream=True)

    # total size in bytes.
    total_size = int(response.headers.get("content-length", 0))
    block_size = 32 * 1024  # 32 Kibibytes

    # create TQDM progress bar (console only, so it doesn't bloat the log file)
    prog_bar = progress_bar.tqdm(
        dynamic_ncols=True, total=total_size, unit="iB", unit_scale=True,
        file=ORIGINAL_STDERR
    )
    try:
        with open(full_filename, "wb") as fd:
            for chunk in response.iter_content(block_size):
                prog_bar.update(len(chunk))
                fd.write(chunk)  # write video chunk to disk
        prog_bar.close()

        return True

    except Exception as e:
        print(
            f"{Color.RED}### The video recording with filename '{filename}' for user with email "
            f"'{email}' could not be downloaded because {Color.END}'{e}'"
        )

        return False


def format_bytes(size):
    """ Convert a number of bytes into a human readable string """
    size = float(size or 0)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if size < 1024.0 or unit == "TB":
            return f"{size:.2f} {unit}"
        size /= 1024.0


def input_date_range():
    """ Prompt for a new start/end date and update the global
        RECORDING_START_DATE / RECORDING_END_DATE. """
    global RECORDING_START_DATE, RECORDING_END_DATE

    while True:
        start_input = input("Enter start date (YYYY-MM-DD): ").strip()
        end_input = input("Enter end date (YYYY-MM-DD): ").strip()
        try:
            start = parser.parse(start_input).replace(tzinfo=timezone.utc)
            end = parser.parse(end_input).replace(tzinfo=timezone.utc)
        except (ValueError, OverflowError):
            print(f"{Color.RED}### Invalid date format. Please use YYYY-MM-DD.{Color.END}")
            continue

        if start > end:
            print(f"{Color.RED}### Start date must not be after end date.{Color.END}")
            continue

        RECORDING_START_DATE = start
        RECORDING_END_DATE = end
        return


def prompt_date_range():
    """ Show the configured date range and let the user optionally change it.
        Updates the global RECORDING_START_DATE / RECORDING_END_DATE.
    """
    print(
        f"\n{Color.BOLD}Current date range:{Color.END} "
        f"{RECORDING_START_DATE.date()} to {RECORDING_END_DATE.date()}"
    )
    if input("Would you like to change it? (y/n): ").strip().lower() != "y":
        return

    input_date_range()


def compute_usage(users, start_date, end_date, quiet=False):
    """ Sum cloud recording storage per user within the given date range.
        Returns a dict with sorted per-user rows and the overall totals.
        When quiet is set, the per-user progress lines are suppressed (useful
        when computing many ranges, e.g. the archive history build).
    """
    report = []
    total_size = 0
    total_count = 0

    for email, user_id, first_name, last_name in users:
        user_info = (
            f"{first_name} {last_name} - {email}" if first_name and last_name else f"{email}"
        )
        if not quiet:
            print(f"==> Checking {user_info}")

        recordings = list_recordings(user_id, start_date, end_date)
        user_size = sum(int(rec.get("total_size", 0) or 0) for rec in recordings)
        user_count = sum(int(rec.get("recording_count", 0) or 0) for rec in recordings)

        report.append([email, len(recordings), user_count, user_size])
        total_size += user_size
        total_count += len(recordings)

    # sort by storage used, largest first
    report.sort(key=lambda row: row[3], reverse=True)

    return {"report": report, "total_size": total_size, "total_count": total_count}


def print_usage_table(result):
    """ Print a usage report produced by compute_usage() (or read from cache). """
    print(f"\n{Color.BOLD}{'Email':<40}{'Meetings':>10}{'Files':>8}{'Storage':>14}{Color.END}")
    print("-" * 72)
    for email, meetings, files, size in result["report"]:
        print(f"{email:<40}{meetings:>10}{files:>8}{format_bytes(size):>14}")
    print("-" * 72)
    print(
        f"{Color.BOLD}{'TOTAL':<40}{result['total_count']:>10}{'':>8}"
        f"{format_bytes(result['total_size']):>14}{Color.END}"
    )


def report_cloud_usage():
    """ Loop through all users and report how much cloud recording storage
        each account is using within the configured date range.
    """
    prompt_date_range()

    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()

    print(
        f"\n{Color.BOLD}Cloud recording usage from "
        f"{RECORDING_START_DATE.date()} to {RECORDING_END_DATE.date()}{Color.END}\n"
    )

    result = compute_usage(users, RECORDING_START_DATE, RECORDING_END_DATE)
    print_usage_table(result)


def load_zoom_cache():
    try:
        with open(ZOOM_CACHE_FILE, "r", encoding="utf-8") as fd:
            return json.load(fd)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_zoom_cache():
    with open(ZOOM_CACHE_FILE, "w", encoding="utf-8") as fd:
        json.dump(ZOOM_RECORDINGS_CACHE, fd)


def load_drive_cache():
    try:
        with open(DRIVE_CACHE_FILE, "r", encoding="utf-8") as fd:
            return json.load(fd)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_drive_cache():
    with open(DRIVE_CACHE_FILE, "w", encoding="utf-8") as fd:
        json.dump(DRIVE_LOOKUP_CACHE, fd)


def configure_caches(interactive=True, use_zoom=True, use_drive=False):
    """ Load the Zoom-recordings and Google-Drive lookup caches and decide whether
        to read from them. When interactive, the operator is asked about each cache
        separately; otherwise the use_zoom/use_drive defaults apply (used by the
        unattended --auto / dry-run paths). Either way the caches are always
        *updated* with fresh answers, so the next run can reuse them. """
    global ZOOM_RECORDINGS_CACHE, DRIVE_LOOKUP_CACHE, USE_ZOOM_CACHE, USE_DRIVE_CACHE
    ZOOM_RECORDINGS_CACHE = load_zoom_cache()
    DRIVE_LOOKUP_CACHE = load_drive_cache()

    if interactive:
        USE_ZOOM_CACHE = input(
            f"Use cached Zoom recording data when available? "
            f"({len(ZOOM_RECORDINGS_CACHE)} cached) (y/n): "
        ).strip().lower() == "y"
        USE_DRIVE_CACHE = input(
            f"Use cached Google Drive lookups when available? "
            f"({len(DRIVE_LOOKUP_CACHE)} cached) (y/n): "
        ).strip().lower() == "y"
    else:
        USE_ZOOM_CACHE = use_zoom
        USE_DRIVE_CACHE = use_drive

    print(
        f"{Color.BOLD}Cache:{Color.END} Zoom recordings "
        f"{Color.GREEN if USE_ZOOM_CACHE else Color.YELLOW}"
        f"{'ON' if USE_ZOOM_CACHE else 'OFF'}{Color.END}, Drive lookups "
        f"{Color.GREEN if USE_DRIVE_CACHE else Color.YELLOW}"
        f"{'ON' if USE_DRIVE_CACHE else 'OFF'}{Color.END} "
        f"(both are refreshed when not used)"
    )


def drive_file_exists(drive_service, folder, filename):
    """ Whether a file exists in Google Drive, consulting the lookup cache first
        when caching is enabled. The result is always stored so a later check —
        this run or a future one — can skip the Drive round-trip. """
    key = f"{folder}|{filename}"
    if USE_DRIVE_CACHE and key in DRIVE_LOOKUP_CACHE:
        print(
            f"{Color.DARK_CYAN}[drive cache] hit — {filename} "
            f"(no Drive API call){Color.END}"
        )
        return DRIVE_LOOKUP_CACHE[key]
    exists = drive_service.file_exists(folder, filename)
    DRIVE_LOOKUP_CACHE[key] = exists
    reason = "miss" if USE_DRIVE_CACHE else "disabled"
    print(
        f"{Color.DARK_CYAN}[drive cache] {reason} — {filename}: "
        f"called Drive API, cache updated{Color.END}"
    )
    return exists


def note_drive_upload(folder, filename):
    """ Record that a file is now present in Drive, keeping cached lookups correct
        after an upload. Persisted immediately so an interrupted run never leaves
        an uploaded file uncached. """
    DRIVE_LOOKUP_CACHE[f"{folder}|{filename}"] = True
    save_drive_cache()
    print(
        f"{Color.DARK_CYAN}[drive cache] updated — {filename} "
        f"marked present after upload{Color.END}"
    )


def load_usage_cache():
    try:
        with open(USAGE_CACHE_FILE, "r", encoding="utf-8") as fd:
            return json.load(fd)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_usage_cache(cache):
    with open(USAGE_CACHE_FILE, "w", encoding="utf-8") as fd:
        json.dump(cache, fd, indent=2)


def month_range(year, month):
    """ Return (start, end) UTC datetimes spanning the given calendar month. """
    start = datetime(year, month, 1, tzinfo=timezone.utc)
    if month == 12:
        end = datetime(year + 1, 1, 1, tzinfo=timezone.utc) - timedelta(days=1)
    else:
        end = datetime(year, month + 1, 1, tzinfo=timezone.utc) - timedelta(days=1)
    return start, end


def get_month_usage(users_getter, year, month, cache, quiet=False):
    """ Return (result, from_cache) for a calendar month's usage.
        Completed months are served from / written to the cache; the current
        (in-progress) month is always recomputed live since it keeps changing.
        users_getter is called only on a cache miss, so cached-only runs avoid
        fetching the user list.
    """
    key = f"{year:04d}-{month:02d}"
    current_key = datetime.now(timezone.utc).strftime("%Y-%m")
    is_current = (key == current_key)

    if key in cache and not is_current:
        return cache[key], True

    start, end = month_range(year, month)
    result = compute_usage(users_getter(), start, end, quiet=quiet)
    cache[key] = result
    save_usage_cache(cache)
    return result, False


def monthly_usage_report():
    """ Report cloud recording usage one month at a time, starting with the
        current month and going backwards. Results are cached per month; a
        cached month is reported from the cache instead of re-querying Zoom.
        The current (in-progress) month is always refreshed since it changes.
    """
    today = datetime.now(timezone.utc)

    try:
        months = int(input("How many months to report (including current)? [1]: ").strip() or "1")
    except ValueError:
        months = 1
    months = max(1, months)

    cache = load_usage_cache()
    users_getter = _lazy_users()

    year, month = today.year, today.month
    for _ in range(months):
        key = f"{year:04d}-{month:02d}"
        result, from_cache = get_month_usage(users_getter, year, month, cache)
        source = "from cache" if from_cache else (
            "current month, live" if key == today.strftime("%Y-%m") else "querying Zoom"
        )
        print(f"\n{Color.BOLD}{key} usage ({source}){Color.END}")
        print_usage_table(result)

        # step back one month
        month -= 1
        if month == 0:
            month = 12
            year -= 1


def monthly_usage_cached_vs_now():
    """ For each month (starting with the current one, going back), compare the
        cached storage figure against a freshly-queried "now" figure. Useful for
        spotting drift when recordings were added or deleted since the cache was
        written. The cache is read-only here; it is not modified.
    """
    today = datetime.now(timezone.utc)

    try:
        months = int(input("How many months to compare (including current)? [1]: ").strip() or "1")
    except ValueError:
        months = 1
    months = max(1, months)

    cache = load_usage_cache()
    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()

    header = f"{'Month':<9}{'Cached':>14}{'Now':>14}{'Difference':>16}"
    print(f"\n{Color.BOLD}{header}{Color.END}")
    print("-" * len(header))

    year, month = today.year, today.month
    for _ in range(months):
        key = f"{year:04d}-{month:02d}"
        start, end = month_range(year, month)

        cached_entry = cache.get(key)
        cached_size = int(cached_entry["total_size"]) if cached_entry else None
        now_size = compute_usage(users, start, end, quiet=True)["total_size"]

        cached_str = format_bytes(cached_size) if cached_entry else "(not cached)"
        if cached_entry:
            diff = now_size - cached_size
            sign = "+" if diff > 0 else ""
            diff_str = "same" if diff == 0 else f"{sign}{format_bytes(diff)}"
        else:
            diff_str = "-"

        print(f"{key:<9}{cached_str:>14}{format_bytes(now_size):>14}{diff_str:>16}")

        # step back one month
        month -= 1
        if month == 0:
            month = 12
            year -= 1


def _lazy_users():
    """ Return a callable that fetches and memoizes the Zoom user list, so it is
        only retrieved when actually needed (e.g. on a cache miss). """
    cached = {}

    def getter():
        if "users" not in cached:
            print(f"{Color.BOLD}Getting user accounts...{Color.END}")
            cached["users"] = get_users()
        return cached["users"]

    return getter


def load_archive_settings():
    try:
        with open(ARCHIVE_SETTINGS_FILE, "r", encoding="utf-8") as fd:
            return json.load(fd)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_archive_settings(settings):
    with open(ARCHIVE_SETTINGS_FILE, "w", encoding="utf-8") as fd:
        json.dump(settings, fd, indent=2)


def load_last_check_range():
    """ Return (start, end) UTC datetimes saved from the last check run, or None. """
    saved = load_archive_settings().get("check_range")
    if not saved:
        return None
    try:
        start = parser.parse(saved["start"]).replace(tzinfo=timezone.utc)
        end = parser.parse(saved["end"]).replace(tzinfo=timezone.utc)
        return start, end
    except (KeyError, ValueError, OverflowError):
        return None


def save_last_check_range(start, end):
    """ Persist the date range used by the check option so the next run reuses it. """
    settings = load_archive_settings()
    settings["check_range"] = {"start": str(start.date()), "end": str(end.date())}
    save_archive_settings(settings)


def prompt_plan(auto=False):
    """ Show the saved cloud storage plan (if any), let the user update it, and
        return the plan size in bytes. Plan is entered/stored in GB (GiB).
        In auto mode the saved plan is used as-is (no prompts); returns None if
        no plan has been saved yet. """
    settings = load_archive_settings()
    plan_gb = settings.get("plan_size_gb")

    if auto:
        if not plan_gb:
            print(f"{Color.RED}### No saved plan found. Run option 4 once to set it.{Color.END}")
            return None
        print(
            f"{Color.BOLD}Using saved cloud storage plan:{Color.END} "
            f"{plan_gb} GB ({format_bytes(plan_gb * 1024 ** 3)})"
        )
        return plan_gb * 1024 ** 3

    if plan_gb:
        print(
            f"\n{Color.BOLD}Saved cloud storage plan:{Color.END} "
            f"{plan_gb} GB ({format_bytes(plan_gb * 1024 ** 3)})"
        )
        if input("Update it? (y/n): ").strip().lower() == "y":
            plan_gb = None

    while not plan_gb:
        raw = input("Enter your Zoom cloud storage plan size in GB: ").strip()
        try:
            plan_gb = float(raw)
            if plan_gb <= 0:
                raise ValueError
        except ValueError:
            print(f"{Color.RED}### Please enter a positive number of GB.{Color.END}")
            plan_gb = None

    settings["plan_size_gb"] = plan_gb
    save_archive_settings(settings)
    return plan_gb * 1024 ** 3


def archive_planner(auto=False):
    """ Determine which date range of cloud recordings should be archived to
        Google Drive to bring Zoom usage under 70% of the storage plan, and
        show what usage would be if everything older than 30 days were archived.
    """
    plan_bytes = prompt_plan(auto=auto)
    if plan_bytes is None:
        return None
    target_bytes = 0.7 * plan_bytes

    today = datetime.now(timezone.utc)
    users_getter = _lazy_users()
    cache = load_usage_cache()

    # Build a full month-by-month history from the configured start to this month.
    print(f"\n{Color.BOLD}Building usage history...{Color.END}")
    months = []  # (year, month, total_size), oldest first
    year, month = RECORDING_START_DATE.year, RECORDING_START_DATE.month
    while (year, month) <= (today.year, today.month):
        key = f"{year:04d}-{month:02d}"
        result, from_cache = get_month_usage(users_getter, year, month, cache, quiet=True)
        source = "cached" if from_cache else "queried"
        print(f"  {key}: {format_bytes(result['total_size']):>12}  ({source})")
        months.append((year, month, result["total_size"]))
        month += 1
        if month == 13:
            month, year = 1, year + 1

    total_usage = sum(size for _, _, size in months)
    pct = (total_usage / plan_bytes * 100) if plan_bytes else 0

    print(f"\n{Color.BOLD}=== Archive plan ==={Color.END}")
    print(f"Plan size      : {format_bytes(plan_bytes)}")
    print(f"Current usage  : {format_bytes(total_usage)} ({pct:.1f}% of plan)")
    print(f"Target (70%)   : {format_bytes(target_bytes)}")

    archive_before = None
    if total_usage <= target_bytes:
        print(
            f"\n{Color.GREEN}Usage is already under 70% of the plan. "
            f"No archiving required.{Color.END}"
        )
    else:
        archived = 0
        for (yy, mm, size) in months:  # archive oldest months first
            archived += size
            if total_usage - archived <= target_bytes:
                # keep everything from the month after this one onwards
                archive_before, _ = month_range(yy, mm)
                archive_before = archive_before.replace(day=1)
                # advance to first day of the following month
                if mm == 12:
                    archive_before = archive_before.replace(year=yy + 1, month=1)
                else:
                    archive_before = archive_before.replace(month=mm + 1)
                remaining = total_usage - archived
                break
        else:
            # even archiving the whole history would not reach the target
            archived = total_usage
            remaining = 0
            archive_before = today

        earliest, _ = month_range(months[0][0], months[0][1])
        rem_pct = (remaining / plan_bytes * 100) if plan_bytes else 0
        print(
            f"\n{Color.YELLOW}Archive recordings from {earliest.date()} "
            f"up to {archive_before.date()} (everything before that date).{Color.END}"
        )
        print(f"  Would free   : {format_bytes(archived)}")
        print(f"  Usage after  : {format_bytes(remaining)} ({rem_pct:.1f}% of plan)")

    # "Archive everything but the last 30 days" scenario
    last30_start = today - timedelta(days=30)
    print(f"\n{Color.BOLD}Computing last-30-days usage...{Color.END}")
    kept30 = compute_usage(users_getter(), last30_start, today, quiet=True)["total_size"]
    pct30 = (kept30 / plan_bytes * 100) if plan_bytes else 0
    print(
        f"\n{Color.BOLD}If you archived everything older than 30 days "
        f"(before {last30_start.date()}):{Color.END}"
    )
    print(f"  Remaining usage: {format_bytes(kept30)} ({pct30:.1f}% of plan)")

    return archive_before


def delete_cloud_recording(meeting_uuid):
    """ Move a meeting's cloud recordings to the Zoom trash (recoverable for
        ~30 days). Returns (ok, message) so callers can report the reason. """
    # Per Zoom's API, the UUID must be double URL-encoded ONLY when it begins
    # with '/' or contains '//'; otherwise it must be single-encoded. Always
    # double-encoding a normal UUID produces a wrong path and a 404.
    if meeting_uuid.startswith("/") or "//" in meeting_uuid:
        encoded = quote(quote(meeting_uuid, safe=""), safe="")
    else:
        encoded = quote(meeting_uuid, safe="")

    url = f"https://api.zoom.us/v2/meetings/{encoded}/recordings"
    response = requests.delete(url, headers=AUTHORIZATION_HEADER, params={"action": "trash"})

    if response.ok:
        return True, "moved to trash"

    try:
        message = response.json().get("message", response.text)
    except ValueError:
        message = response.text
    return False, f"HTTP {response.status_code}: {message}"


def _recording_day(recording):
    """ Return the local calendar date of a recording's start time, or None if it
        can't be parsed. Used to group archive progress by day. """
    try:
        return (
            parser.parse(recording.get("start_time", ""))
            .replace(tzinfo=timezone.utc)
            .astimezone(MEETING_TIMEZONE)
            .date()
        )
    except (ValueError, OverflowError, TypeError):
        return None


def format_elapsed(seconds):
    """ Render a duration in seconds as a compact h/m/s string. """
    seconds = int(seconds)
    hours, rem = divmod(seconds, 3600)
    minutes, secs = divmod(rem, 60)
    if hours:
        return f"{hours}h {minutes}m {secs}s"
    if minutes:
        return f"{minutes}m {secs}s"
    return f"{secs}s"


def _print_archive_progress(email, day, checked, found, missing):
    """ Emit a one-line progress marker once a user's day has been fully archived,
        naming the user, the most recent date incorporated, how long the run has
        been going, and the running totals of Zoom files checked, found already in
        Google Drive, and missing from it. """
    elapsed = ""
    if ARCHIVE_START_TS is not None:
        elapsed = f" [running {format_elapsed(time.time() - ARCHIVE_START_TS)}]"
    print(
        f"{Color.GREEN}>>> Archive progress: completed {email} "
        f"through {day}{elapsed} | Zoom files checked {checked}, "
        f"found in Drive {found}, missing {missing}{Color.END}"
    )


def download_recordings_for_users(users, drive_service, delete_after=False, recheck_drive=False, confirm_each=False):
    """ Download (and optionally upload to Google Drive) every recording for the
        given users within the globally configured date range. When delete_after
        is set, a meeting's cloud recordings are moved to the Zoom trash once all
        of its files have been uploaded successfully.

        By default a meeting listed in completed-downloads.log is skipped without
        contacting Drive. When recheck_drive is set (used by archiving), that log
        is ignored and each file's presence is verified directly against Drive,
        so genuinely-missing files are picked up even if the meeting was logged.

        When confirm_each is set, the operator is asked to approve each download
        after the file has been confirmed missing from Drive; declining skips it.
    """
    global ARCHIVE_START_TS
    ARCHIVE_START_TS = time.time()

    # Running totals across the whole run, shown on each progress line.
    checked = found = missing = 0

    for email, user_id, first_name, last_name in users:
        userInfo = (
            f"{first_name} {last_name} - {email}" if first_name and last_name else f"{email}"
        )
        print(f"\n{Color.BOLD}Getting recording list for {userInfo}{Color.END}")

        recordings = list_recordings(user_id)
        recordings.sort(key=lambda r: r.get("start_time", ""))
        total_count = len(recordings)
        print(f"==> Found {total_count} recordings")

        current_day = None

        for index, recording in enumerate(recordings):
            rec_day = _recording_day(recording)
            if rec_day is not None:
                # A change of day means the previous day is fully processed.
                if current_day is not None and rec_day != current_day:
                    _print_archive_progress(email, current_day, checked, found, missing)
                current_day = rec_day

            try:
                meeting_uuid = recording["uuid"]

                if not recheck_drive and meeting_uuid in COMPLETED_MEETING_IDS:
                    print(
                        f"\n==> Skipping already downloaded recording {index + 1} of {total_count}"
                    )
                    continue

                downloads = get_downloads(recording)

            except Exception as e:
                print(
                    f"{Color.RED}### Failed to get download URLs for recording {index + 1} "
                    f"of {total_count} due to error: {str(e)}{Color.END}"
                )
                continue

            print(f"\n==> Processing recording {index + 1} of {total_count}")

            all_uploaded = True
            for file_type, file_extension, download_url, recording_type, recording_id in downloads:
                try:
                    params = {
                        "file_extension": file_extension,
                        "recording": recording,
                        "recording_id": recording_id,
                        "recording_type": recording_type,
                        "email": email
                    }
                    filename, folder_name = format_filename(params)

                    sanitized_download_dir = path_validate.sanitize_filepath(
                        os.sep.join([DOWNLOAD_DIRECTORY, folder_name])
                    )
                    sanitized_filename = path_validate.sanitize_filename(filename)
                    full_filename = os.sep.join([sanitized_download_dir, sanitized_filename])

                    # Check if file exists
                    print(f"    > Checking if file exists...{sanitized_filename} in folder {folder_name}")
                    checked += 1
                    found_file = False
                    try:
                        found_file = drive_file_exists(drive_service, folder_name, sanitized_filename)  # Check if file exists
                    except Exception as e:
                        print(f"{Color.RED}{str(e)}{Color.END}"  )
                        print(f"FAILED: Checking if file exists...{sanitized_filename} in folder {folder_name}")
                        missing += 1  # couldn't confirm in Drive; treat as not present
                        all_uploaded = False
                        continue

                    if found_file:
                        found += 1
                        print(f"    > Skipping existing file: {sanitized_filename}")
                        continue

                    missing += 1
                    # Permission gate: only after confirming the file is missing
                    # from Drive do we ask the operator whether to download it.
                    if confirm_each:
                        if input(
                            f"    > Not on Drive. Download {sanitized_filename} from Zoom? (y/n): "
                        ).strip().lower() != "y":
                            print(f"    > {Color.YELLOW}Skipped by user:{Color.END} {sanitized_filename}")
                            all_uploaded = False
                            continue

                    print(f"    > Downloading {filename}")
                    if download_recording(download_url, email, filename, folder_name):
                        if GDRIVE_ENABLED and drive_service:
                            print(f"    > Uploading to Google Drive...")
                            print("Google Drive Folder name: %s. full file name: %s, sanitized_file_name: %s" % (folder_name, full_filename, sanitized_filename))
                            success = drive_service.upload_file(full_filename, folder_name, sanitized_filename)
                            if success:
                                note_drive_upload(folder_name, sanitized_filename)
                            if success and os.path.exists(full_filename):
                                os.remove(full_filename)
                                if not os.listdir(sanitized_download_dir):
                                    os.rmdir(sanitized_download_dir)
                            if not success:
                                all_uploaded = False
                    else:
                        all_uploaded = False

                except Exception as e:
                    all_uploaded = False
                    print(
                        f"{Color.RED}### Failed to process file {file_type} "
                        f"for recording {index + 1} of {total_count} due to error: "
                        f"{str(e)}{Color.END}"
                    )
                    continue

            with open(COMPLETED_MEETING_IDS_LOG, "a") as fd:
                fd.write(f"{meeting_uuid}\n")
                COMPLETED_MEETING_IDS.add(meeting_uuid)

            # Free Zoom storage only once every file is safely in Google Drive
            if delete_after and all_uploaded and GDRIVE_ENABLED and drive_service:
                ok, message = delete_cloud_recording(meeting_uuid)
                if ok:
                    print(f"    > {Color.YELLOW}Removed from Zoom (moved to trash){Color.END}")
                else:
                    print(f"{Color.RED}### Failed to delete recording from Zoom - {message}{Color.END}")

        # All recordings for this user processed; flush the final day's progress.
        if current_day is not None:
            _print_archive_progress(email, current_day, checked, found, missing)
        save_drive_cache()


def _archive_specific_user(drive_service, confirm_each=False):
    """ Option-4 sub-mode: archive one chosen user's recordings within an entered
        time range, rather than the plan-based cutoff across all users. Google Drive
        and the caches are already initialized by run_archive. """
    global RECORDING_START_DATE, RECORDING_END_DATE

    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()
    email, user_id, first_name, last_name = pick_user(users)

    input_date_range()

    print(
        f"\n{Color.RED}After a successful upload, recordings can be removed from Zoom to free "
        f"space.{Color.END}\nThey are moved to the Zoom trash (recoverable for ~30 days), "
        f"not permanently deleted."
    )
    delete_after = input(
        "Delete from Zoom after successful upload? Type 'DELETE' to confirm: "
    ).strip() == "DELETE"

    print(
        f"\n{Color.BOLD}Archiving {email} from {RECORDING_START_DATE.date()} "
        f"to {RECORDING_END_DATE.date()}{Color.END}"
    )
    download_recordings_for_users(
        [(email, user_id, first_name, last_name)], drive_service,
        delete_after=delete_after, recheck_drive=True, confirm_each=confirm_each
    )
    print(f"\n{Color.GREEN}Archive complete.{Color.END}")


def run_archive(auto=False):
    """ Plan and execute archiving of old cloud recordings to Google Drive so
        that Zoom usage stays under 70% of the storage plan.

        In auto mode it runs unattended: it uses the saved plan (no prompt),
        auto-confirms the archive, and deletes archived recordings from Zoom
        (trash) after a successful upload. """
    global GDRIVE_ENABLED, RECORDING_END_DATE

    if auto:
        print(f"{Color.BOLD}=== Auto archive mode ==={Color.END}")

    print("\nArchiving copies recordings to Google Drive, so it is required as the destination.")
    drive_service = setup_google_drive(auto=auto)
    if not drive_service:
        print(f"{Color.RED}### Google Drive is not available; cannot archive.{Color.END}")
        return
    GDRIVE_ENABLED = True

    # In auto mode read the Zoom cache (past data is immutable) but always verify
    # Drive fresh, since auto deletes from Zoom and must not trust a stale lookup.
    if auto:
        configure_caches(interactive=False, use_zoom=True, use_drive=False)
    else:
        configure_caches(interactive=True)

    load_completed_meeting_ids()

    # Interactive: optionally require per-file approval before downloading.
    confirm_each = False
    if not auto:
        confirm_each = input(
            "\nAsk for permission before downloading each file from Zoom? (y/n): "
        ).strip().lower() == "y"

    # Interactive: choose between the plan-based sweep and a targeted user+range.
    if not auto:
        print("\nArchive mode:")
        print("  1. Keep usage under 70% of plan (all users, computed cutoff)")
        print("  2. A specific user and time range")
        if (input("Enter choice (1-2) [1]: ").strip() or "1") == "2":
            _archive_specific_user(drive_service, confirm_each)
            return

    archive_before = archive_planner(auto=auto)
    if not archive_before:
        return

    if auto:
        print(f"\nAuto: archiving recordings before {archive_before.date()} to Google Drive.")
    else:
        proceed = input(
            f"\nArchive recordings before {archive_before.date()} to Google Drive now? (y/n): "
        ).strip().lower()
        if proceed != "y":
            print("Archive cancelled.")
            return

    if auto:
        # Auto mode frees space: trash from Zoom after a successful upload
        delete_after = True
        print(f"{Color.YELLOW}Auto: archived recordings will be moved to Zoom trash "
              f"(recoverable for ~30 days) after a successful upload.{Color.END}")
    else:
        print(
            f"\n{Color.RED}After a successful upload, recordings can be removed from Zoom to free "
            f"space.{Color.END}\nThey are moved to the Zoom trash (recoverable for ~30 days), "
            f"not permanently deleted."
        )
        delete_after = input(
            "Delete from Zoom after successful upload? Type 'DELETE' to confirm: "
        ).strip() == "DELETE"

    # Archive everything before the computed cutoff date
    RECORDING_END_DATE = archive_before

    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()
    download_recordings_for_users(
        users, drive_service, delete_after=delete_after, recheck_drive=True,
        confirm_each=confirm_each
    )
    print(f"\n{Color.GREEN}Archive complete.{Color.END}")


def _iter_recording_files(recording):
    """ Yield (file_extension, recording_id, recording_type, file_size) for each
        downloadable file of a recording, mirroring get_downloads' type logic.
        file_size is the Zoom-reported size in bytes, or None when unavailable. """
    for download in recording.get("recording_files", []) or []:
        file_type = download.get("file_type", "")
        file_extension = download.get("file_extension", "")
        recording_id = download.get("id", "")
        if file_type == "":
            recording_type = "incomplete"
        elif file_type != "TIMELINE":
            recording_type = download.get("recording_type", "")
        else:
            recording_type = file_type

        size = download.get("file_size")
        try:
            size = int(size) if size not in (None, "") else None
        except (ValueError, TypeError):
            size = None
        # Zoom occasionally reports 0 for files whose size it hasn't computed yet;
        # treat that as "unknown" so it is counted, not silently shown as 0 bytes.
        if size == 0:
            size = None

        yield file_extension, recording_id, recording_type, size


def dry_run_archive(interactive=True):
    """ Option 8: simulate the archive (option 4) without downloading, uploading,
        or deleting anything. It computes the same cutoff date as the real archive,
        then walks every recording that would be archived and tallies the files
        that are NOT yet in Google Drive (i.e. the ones that would be downloaded
        and uploaded), grouped by user account and month. Where Zoom does not
        report a file's size, the file is counted instead. The breakdown is written
        to archive-YYYY-MM-DD.run.log.csv.

        From the menu (interactive=True) the operator is asked whether to use the
        caches; the --dry-run CLI flag passes interactive=False to stay unattended.
        Either way the saved plan is used, so the plan itself is never prompted. """
    global GDRIVE_ENABLED, RECORDING_END_DATE, ARCHIVE_START_TS

    print("\nDry run: nothing is downloaded, uploaded, or deleted.")
    # Use the saved plan; never prompt for the plan itself.
    drive_service = setup_google_drive(auto=True)
    if not drive_service:
        print(f"{Color.RED}### Google Drive is not available; cannot check what is already archived.{Color.END}")
        return
    GDRIVE_ENABLED = True

    # Dry run is read-only, so both caches are safe to use. From the menu we still
    # ask; unattended (--dry-run) we default both on without prompting.
    configure_caches(interactive=interactive, use_zoom=True, use_drive=True)

    archive_before = archive_planner(auto=True)
    if not archive_before:
        return

    # Simulate archiving everything before the computed cutoff date
    RECORDING_END_DATE = archive_before

    print(f"\n{Color.BOLD}Simulating archive of everything before {archive_before.date()}...{Color.END}")
    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()
    ARCHIVE_START_TS = time.time()

    # group key: (email, "YYYY-MM") -> {"files", "bytes", "unknown"}
    groups = {}
    grand_files = 0
    grand_bytes = 0
    grand_unknown = 0
    grand_found_files = 0
    grand_found_bytes = 0
    # Running totals across the run (grand_files is the missing count).
    checked = 0
    found = 0

    for email, user_id, first_name, last_name in users:
        user_info = (
            f"{first_name} {last_name} - {email}" if first_name and last_name else f"{email}"
        )
        print(f"\n{Color.BOLD}Checking {user_info}{Color.END}")
        recordings = list_recordings(user_id)
        recordings.sort(key=lambda r: r.get("start_time", ""))
        print(
            f"==> {len(recordings)} recording(s) for {email} in range "
            f"{RECORDING_START_DATE.date()} to {RECORDING_END_DATE.date()}"
        )

        current_day = None

        for recording in recordings:
            rec_day = _recording_day(recording)
            if rec_day is not None:
                # A change of day means the previous day is fully processed.
                if current_day is not None and rec_day != current_day:
                    _print_archive_progress(email, current_day, checked, found, grand_files)
                current_day = rec_day

            month_key = rec_day.strftime("%Y-%m") if rec_day is not None else "unknown"

            for file_extension, recording_id, recording_type, size in _iter_recording_files(recording):
                params = {
                    "file_extension": file_extension,
                    "recording": recording,
                    "recording_id": recording_id,
                    "recording_type": recording_type,
                    "email": email,
                }
                filename, folder_name = format_filename(params)
                sanitized_filename = path_validate.sanitize_filename(filename)

                try:
                    exists = drive_file_exists(drive_service, folder_name, sanitized_filename)
                except Exception as e:
                    # Don't silently drop a file we couldn't verify; count it as
                    # one that would be downloaded so the estimate stays on the
                    # safe (over-) side.
                    print(f"  {Color.RED}Could not check {sanitized_filename}: {e}{Color.END}")
                    exists = False

                checked += 1
                bucket = groups.setdefault(
                    (email, month_key),
                    {"files": 0, "bytes": 0, "unknown": 0, "found_files": 0, "found_bytes": 0},
                )

                if exists:
                    found += 1
                    bucket["found_files"] += 1
                    bucket["found_bytes"] += size or 0
                    grand_found_files += 1
                    grand_found_bytes += size or 0
                    continue

                bucket["files"] += 1
                grand_files += 1
                if size is None:
                    bucket["unknown"] += 1
                    grand_unknown += 1
                else:
                    bucket["bytes"] += size
                    grand_bytes += size

        # All recordings for this user processed; flush the final day's progress.
        if current_day is not None:
            _print_archive_progress(email, current_day, checked, found, grand_files)
        save_drive_cache()

    today = datetime.now(timezone.utc).date()
    csv_path = f"archive-{today}.run.log.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as fd:
        writer = csv.writer(fd)
        writer.writerow([
            "email", "month", "files_to_download",
            "known_size_bytes", "known_size_human", "files_with_unknown_size",
            "files_on_drive", "on_drive_bytes", "on_drive_human",
        ])
        for (email, month_key) in sorted(groups):
            b = groups[(email, month_key)]
            writer.writerow([
                email, month_key, b["files"],
                b["bytes"], format_bytes(b["bytes"]), b["unknown"],
                b["found_files"], b["found_bytes"], format_bytes(b["found_bytes"]),
            ])
        writer.writerow([])
        writer.writerow([
            "TOTAL", "", grand_files,
            grand_bytes, format_bytes(grand_bytes), grand_unknown,
            grand_found_files, grand_found_bytes, format_bytes(grand_found_bytes),
        ])

    header = (
        f"{'Email':<34}{'Month':>9}{'Files':>8}{'Known size':>14}"
        f"{'Unknown':>9}{'On Drive':>14}"
    )
    print(f"\n{Color.BOLD}=== Dry run: what would be downloaded/uploaded ==={Color.END}")
    print(f"{Color.BOLD}{header}{Color.END}")
    print("-" * len(header))
    for (email, month_key) in sorted(groups):
        b = groups[(email, month_key)]
        print(
            f"{email:<34}{month_key:>9}{b['files']:>8}{format_bytes(b['bytes']):>14}"
            f"{b['unknown']:>9}{format_bytes(b['found_bytes']):>14}"
        )
    print("-" * len(header))
    print(
        f"{Color.BOLD}{'TOTAL':<34}{'':>9}{grand_files:>8}"
        f"{format_bytes(grand_bytes):>14}{grand_unknown:>9}"
        f"{format_bytes(grand_found_bytes):>14}{Color.END}"
    )

    print(f"\nFiles to download : {grand_files} ({grand_unknown} with size unknown to Zoom)")
    print(f"Estimated volume  : {format_bytes(grand_bytes)} (sum of known file sizes)")
    print(f"Already on Drive  : {grand_found_files} files, {format_bytes(grand_found_bytes)}")
    print(f"\n{Color.GREEN}Wrote per-user, per-month breakdown to {csv_path}{Color.END}")
    print(f"{Color.YELLOW}Dry run only — nothing was downloaded, uploaded, or deleted.{Color.END}")


def recording_files_in_drive(drive_service, email, recording):
    """ Return (all_present, checked) for a recording: whether every file is
        already in Google Drive, and how many files were checked. """
    downloads = get_downloads(recording)
    all_present = True
    for file_type, file_extension, download_url, recording_type, recording_id in downloads:
        params = {
            "file_extension": file_extension,
            "recording": recording,
            "recording_id": recording_id,
            "recording_type": recording_type,
            "email": email,
        }
        filename, folder_name = format_filename(params)
        sanitized_filename = path_validate.sanitize_filename(filename)
        if not drive_file_exists(drive_service, folder_name, sanitized_filename):
            print(f"  {Color.RED}Missing in Drive:{Color.END} {sanitized_filename}")
            all_present = False
    return all_present, len(downloads)


def delete_recording_by_name():
    """ Ask for a Zoom recording name (topic), find matching recordings, and for
        each one that is already fully present in Google Drive, delete it from
        Zoom (move to trash). Recordings not found in Drive are left untouched.
    """
    global GDRIVE_ENABLED

    print("\nThis verifies a recording is archived in Google Drive before deleting it from Zoom.")
    drive_service = setup_google_drive()
    if not drive_service:
        print(f"{Color.RED}### Google Drive is not available; cannot verify archives.{Color.END}")
        return
    GDRIVE_ENABLED = True

    name = input("\nEnter the Zoom recording name (topic) to delete: ").strip()
    if not name:
        print("No name entered.")
        return

    prompt_date_range()

    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()

    matches = []  # (email, recording)
    for email, user_id, first_name, last_name in users:
        for recording in list_recordings(user_id):
            if name.lower() in recording.get("topic", "").lower():
                matches.append((email, recording))

    if not matches:
        print(f"\n{Color.YELLOW}No recordings matching '{name}' found in the selected range.{Color.END}")
        return

    print(f"\n{Color.BOLD}Found {len(matches)} matching recording(s).{Color.END}")

    for email, recording in matches:
        topic = recording.get("topic", "")
        start = recording.get("start_time", "")
        meeting_uuid = recording["uuid"]
        print(f"\n=== {topic} ({start}) - {email} ===")

        try:
            all_present, checked = recording_files_in_drive(drive_service, email, recording)
        except Exception as e:
            print(f"  {Color.RED}Could not list files for this recording: {e}{Color.END}")
            continue

        if checked == 0:
            print("  No downloadable files for this recording; skipping.")
            continue

        if not all_present:
            print(
                f"  {Color.RED}Not all files are in Google Drive; "
                f"NOT deleting from Zoom.{Color.END}"
            )
            continue

        print(f"  {Color.GREEN}All {checked} file(s) present in Google Drive.{Color.END}")
        if input("  Delete this recording from Zoom? (y/n): ").strip().lower() != "y":
            print("  Skipped.")
            continue

        ok, message = delete_cloud_recording(meeting_uuid)
        if ok:
            print(f"  {Color.GREEN}Deleted from Zoom ({message}).{Color.END}")
        else:
            print(f"  {Color.RED}Failed to delete from Zoom - {message}{Color.END}")


def pick_user(users):
    """ Print a numbered list of users and return the one the operator selects
        (by number or email). """
    print(f"\n{Color.BOLD}Users:{Color.END}")
    for i, (email, user_id, first_name, last_name) in enumerate(users, 1):
        name = f"{first_name} {last_name}".strip()
        print(f"  {i}. {email}" + (f" ({name})" if name else ""))

    while True:
        raw = input("Pick a user by number or email: ").strip()
        if raw.isdigit():
            idx = int(raw)
            if 1 <= idx <= len(users):
                return users[idx - 1]
        else:
            for user in users:
                if user[0].lower() == raw.lower():
                    return user
        print(f"{Color.RED}### Invalid selection. Try again.{Color.END}")


def check_recordings_in_drive():
    """ For a chosen user and date range, list their Zoom recordings and report
        which files already exist in Google Drive, plus a final summary. The date
        range from the previous run is reused as the default. """
    global GDRIVE_ENABLED, RECORDING_START_DATE, RECORDING_END_DATE

    print("\nThis checks which of a user's Zoom recordings already exist in Google Drive.")
    drive_service = setup_google_drive()
    if not drive_service:
        print(f"{Color.RED}### Google Drive is not available.{Color.END}")
        return
    GDRIVE_ENABLED = True

    configure_caches(interactive=True)

    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()
    email, user_id, first_name, last_name = pick_user(users)

    # Default to the range used last time this option ran, if any
    last_range = load_last_check_range()
    if last_range:
        RECORDING_START_DATE, RECORDING_END_DATE = last_range
    prompt_date_range()

    while True:
        save_last_check_range(RECORDING_START_DATE, RECORDING_END_DATE)
        recordings = list_recordings(user_id)
        print(
            f"\n{Color.BOLD}Found {len(recordings)} recording(s) for {email} "
            f"from {RECORDING_START_DATE.date()} to {RECORDING_END_DATE.date()}{Color.END}"
        )

        total_files = 0
        present_files = 0

        for recording in recordings:
            topic = recording.get("topic", "")
            start = recording.get("start_time", "")
            try:
                downloads = get_downloads(recording)
            except Exception:
                continue

            print(f"\n=== {topic} ({start}) ===")
            for file_type, file_extension, download_url, recording_type, recording_id in downloads:
                params = {
                    "file_extension": file_extension,
                    "recording": recording,
                    "recording_id": recording_id,
                    "recording_type": recording_type,
                    "email": email,
                }
                filename, folder_name = format_filename(params)
                sanitized_filename = path_validate.sanitize_filename(filename)
                exists = drive_file_exists(drive_service, folder_name, sanitized_filename)

                total_files += 1
                if exists:
                    present_files += 1
                    print(f"  {Color.GREEN}[ON DRIVE]{Color.END} {sanitized_filename}")
                else:
                    print(f"  {Color.RED}[MISSING] {Color.END} {sanitized_filename}")

        print(f"\n{Color.BOLD}=== Summary for {email} "
              f"({RECORDING_START_DATE.date()} to {RECORDING_END_DATE.date()}) ==={Color.END}")
        print(f"Recordings (meetings) in Zoom : {len(recordings)}")
        print(f"Files found in Zoom           : {total_files}")
        print(f"Present in Google Drive       : {present_files}")
        print(f"Missing from Google Drive     : {total_files - present_files}")
        save_drive_cache()

        if input(
            f"\nTest {email} against a different time range? (y/n): "
        ).strip().lower() != "y":
            return
        input_date_range()


def load_completed_meeting_ids():
    try:
        with open(COMPLETED_MEETING_IDS_LOG, 'r') as fd:
            [COMPLETED_MEETING_IDS.add(line.strip()) for line in fd]

    except FileNotFoundError:
        print(
            f"{Color.DARK_CYAN}Log file not found. Creating new log file: {Color.END}"
            f"{COMPLETED_MEETING_IDS_LOG}\n"
        )


def handle_graceful_shutdown(signal_received, frame):
    print(f"\n{Color.DARK_CYAN}SIGINT or CTRL-C detected. system.exiting gracefully.{Color.END}")

    system.exit(0)


# ################################################################
# #                        MAIN                                  #
# ################################################################

def main():
    # clear the screen buffer
    os.system('cls' if os.name == 'nt' else 'clear')

    # Capture all output to a rotating log file
    setup_logging()

    # show the logo
    print(f"""
        {Color.DARK_CYAN}


                             ,*****************.
                          *************************
                        *****************************
                      *********************************
                     ******               ******* ******
                    *******                .**    ******
                    *******                       ******/
                    *******                       /******
                    ///////                 //    //////
                    ///////*              ./////.//////
                     ////////////////////////////////*
                       /////////////////////////////
                          /////////////////////////
                             ,/////////////////

                        Zoom Recording Downloader

                        V{APP_VERSION}

        {Color.END}
    """)

    # Preload lookup caches so every operation merges into (rather than clobbers)
    # the on-disk caches. Whether a cache is *read* is decided per operation by
    # configure_caches; here we just make sure existing entries aren't lost.
    global ZOOM_RECORDINGS_CACHE, DRIVE_LOOKUP_CACHE
    ZOOM_RECORDINGS_CACHE = load_zoom_cache()
    DRIVE_LOOKUP_CACHE = load_drive_cache()

    # Non-interactive dry run: simulate the archive (option 8) and write the CSV
    if "--dry-run" in system.argv:
        load_access_token()
        dry_run_archive(interactive=False)
        return

    # Non-interactive auto mode: run option 4 (archive) using the saved plan
    if "--auto" in system.argv:
        load_access_token()
        run_archive(auto=True)
        return

    # Operation choice prompt
    print("\nChoose operation:")
    print("1. Download cloud recordings")
    print("2. Report cloud recording usage by user account")
    print("3. Monthly cloud recording usage (cached)")
    print("4. Archive recordings to Google Drive (keep usage under 70% of plan)")
    print("5. Delete a recording from Zoom by name (if archived in Google Drive)")
    print("6. Check a user's recordings against Google Drive")
    print("7. Monthly cloud recording usage (cached vs. now)")
    print("8. Dry run archive (no download/upload; report volume + CSV)")
    operation = input("Enter choice (1-8): ")

    if operation == "2":
        load_access_token()
        report_cloud_usage()
        return

    if operation == "3":
        load_access_token()
        monthly_usage_report()
        return

    if operation == "4":
        load_access_token()
        run_archive()
        return

    if operation == "5":
        load_access_token()
        delete_recording_by_name()
        return

    if operation == "7":
        load_access_token()
        monthly_usage_cached_vs_now()
        return

    if operation == "6":
        load_access_token()
        check_recordings_in_drive()
        return

    if operation == "8":
        load_access_token()
        dry_run_archive()
        return

    # Storage choice prompt
    print("\nChoose download method:")
    print("1. Local Storage")
    print("2. Google Drive")
    choice = input("Enter choice (1-2): ")

    global GDRIVE_ENABLED
    GDRIVE_ENABLED = (choice == "2")

    drive_service = None
    if GDRIVE_ENABLED:
        drive_service = setup_google_drive()
        if not drive_service:
            GDRIVE_ENABLED = False

    prompt_date_range()

    configure_caches(interactive=True)

    load_access_token()
    load_completed_meeting_ids()

    print(f"{Color.BOLD}Getting user accounts...{Color.END}")
    users = get_users()

    download_recordings_for_users(users, drive_service)


if __name__ == "__main__":
    # tell Python to shutdown gracefully when SIGINT is received
    signal.signal(signal.SIGINT, handle_graceful_shutdown)

    main()
