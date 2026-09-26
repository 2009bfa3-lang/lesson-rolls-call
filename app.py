"""課堂點名系統 — Lesson Rolls Call System.

Roster, the active lesson, and attendance live under data/ because each
student phone is a different browser and does not share st.session_state.
"""

from __future__ import annotations

import html
import io
import json
import math
import os
import secrets
import smtplib
import ssl
import subprocess
import threading
import urllib.error
import urllib.request
from datetime import date, datetime, time, timedelta
from email.message import EmailMessage
from pathlib import Path
from urllib.parse import urlencode

import pandas as pd
import qrcode
import streamlit as st
from PIL import Image

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("ROLLS_DATA_DIR") or (APP_DIR / "data"))
APP_PORT = 8765

ROSTER_COLUMNS = ["student_name", "student_email", "student_number"]
ATTENDANCE_COLUMNS = [
    "student_name",
    "student_email",
    "student_number",
    "checkin_time",
    "class_date",
    "status",
    "latitude",
    "longitude",
    "accuracy_meters",
    "distance_meters",
    "location_result",
    "campus_name",
    "可能不在校園",
    "map_url",
]
SMTP_KEYS = (
    "SMTP_HOST",
    "SMTP_PORT",
    "SMTP_USER",
    "SMTP_PASSWORD",
    "SMTP_FROM",
)

INVALID_INPUT = "你所輸入的資料不正確，請再輸入"
TOO_SOON = "距離上次點名未滿4小時，不能再次輸入。"
CHECKIN_GAP = timedelta(hours=4)
THANK_YOU = "謝謝，你會收到學校電郵回覆作實"
STATUS_ON_TIME = "準時出席"
STATUS_LATE = "遲到"
STATUS_ABSENT = "缺席"
EMAIL_ON_TIME = "你準時出席"
EMAIL_LATE = "你已經遲到"
EMAIL_ABSENT = "你已經缺席"
STUDENT_EMAIL_SKIPPED = "出席已記錄，但電郵未發送：尚未設定 SMTP。"
STUDENT_EMAIL_FAILED = "出席已記錄，但電郵未發送。"
TEACHER_EMAIL_SKIPPED = "報告未發送：尚未設定 SMTP。"
QR_INVALID = "此二維碼已失效，請重新掃描老師畫面上的二維碼"
GPS_REQUIRED = "請開啟定位功能後再點名"
GPS_DENIED = "請按網址列左邊的圖示，開啟網站設定，將位置設為允許，再按一次「允許定位」。也可以到 設定 → Safari → 位置 → 允許。"
QR_TTL = timedelta(seconds=30)
LOCATION_RADIUS_M = 200
LOCATION_UNSET = "未設定課堂位置"
LOCATION_MATCH = "位置相符"
LOCATION_AWAY = "可能不在校園"
CAMPUS_BETHANIE = "1-Bethanie campus"
CAMPUS_WANCHAI = "2-Wan Chai campus"
CAMPUS_OTHERS = "3-others"
CAMPUS_OTHERS_NAME = "其他地點"
CAMPUS_OPTIONS = (CAMPUS_BETHANIE, CAMPUS_WANCHAI, CAMPUS_OTHERS)
FIXED_CAMPUSES = {
    CAMPUS_BETHANIE: (22.26229126734515, 114.13573632952154),
    CAMPUS_WANCHAI: (22.280207758952102, 114.17013747580481),
}
OTHER_GPS_REQUIRED = "請先到設定輸入其他地點的 GPS"
GPS_LOOKUP_FAILED = "查不到這個地址。請在 Google 地圖長按建築物，再把緯度和經度貼到 current GPS。"
NOMINATIM_URL = "https://nominatim.openstreetmap.org/search"
NOMINATIM_USER_AGENT = "LessonRollsCall/1.0 (classroom roll-call)"
GRANT_TTL = timedelta(hours=3)

_DATA_LOCK = threading.RLock()
_SEND_LOCK = threading.Lock()


def ensure_data_dir(data_dir: Path | None = None) -> Path:
    root = Path(data_dir) if data_dir is not None else DATA_DIR
    root.mkdir(parents=True, exist_ok=True)
    return root


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp")
    temporary.write_bytes(data)
    temporary.replace(path)


def norm_email(value: object) -> str:
    return str(value or "").strip().lower()


def norm_number(value: object) -> str:
    text = str(value or "").strip()
    if text.endswith(".0") and text[:-2].isdigit():
        return text[:-2]
    return text


def parse_hhmm(value: str | time) -> time | None:
    if isinstance(value, time):
        return value.replace(second=0, microsecond=0)
    raw = str(value or "").strip()
    for fmt in ("%H:%M", "%H:%M:%S"):
        try:
            parsed = datetime.strptime(raw, fmt).time()
            return parsed.replace(second=0, microsecond=0)
        except ValueError:
            continue
    return None


def format_hhmm(value: time) -> str:
    return f"{value.hour:02d}:{value.minute:02d}"


def parse_date(value: str | date) -> date | None:
    if isinstance(value, datetime):
        return value.date()
    if isinstance(value, date):
        return value
    try:
        return datetime.strptime(str(value).strip(), "%Y-%m-%d").date()
    except ValueError:
        return None


def classify_checkin(checkin: datetime, class_date: date, start: time) -> tuple[str, str]:
    """Compare check-in with class_date + start_time in Mac local time.

    check-in <= start → 準時出席
    start < check-in <= start + 15 minutes → 遲到
    check-in > start + 15 minutes → 缺席
    """
    if checkin.tzinfo is not None:
        checkin = checkin.astimezone().replace(tzinfo=None)
    checkin = checkin.replace(microsecond=0)
    start_dt = datetime.combine(class_date, start.replace(second=0, microsecond=0))
    late_deadline = start_dt + timedelta(minutes=15)
    if checkin <= start_dt:
        return STATUS_ON_TIME, EMAIL_ON_TIME
    if checkin <= late_deadline:
        return STATUS_LATE, EMAIL_LATE
    return STATUS_ABSENT, EMAIL_ABSENT


def suggested_times(now: datetime | None = None) -> tuple[time, time]:
    """Default a new lesson to the current local minute, for one hour."""
    current = (now or datetime.now()).replace(second=0, microsecond=0)
    start = current.time()
    end_dt = current + timedelta(hours=1)
    if end_dt.date() != current.date() or end_dt.time() <= start:
        return time(22, 0), time(23, 0)
    return start, end_dt.time()


def class_has_ended(session: dict, now: datetime | None = None) -> bool:
    class_date = parse_date(session.get("class_date", ""))
    end = parse_hhmm(session.get("end_time", ""))
    if class_date is None or end is None:
        return False
    current = now or datetime.now()
    if current.tzinfo is not None:
        current = current.astimezone().replace(tzinfo=None)
    return current > datetime.combine(class_date, end)


def end_prompt_needed(session: dict, now: datetime | None = None) -> bool:
    return not bool(session.get("report_sent")) and class_has_ended(session, now)


def _settings_path(data_dir: Path | None = None) -> Path:
    return ensure_data_dir(data_dir) / "settings.json"


def _read_settings_file(data_dir: Path | None = None) -> dict:
    path = _settings_path(data_dir)
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return {}
    return data if isinstance(data, dict) else {}


def _classroom_fields(data: dict) -> dict:
    pair = parse_gps_pair(f"{data.get('classroom_latitude', '')}, {data.get('classroom_longitude', '')}")
    gps_set = bool(data.get("classroom_gps_set")) and pair is not None
    return {
        "classroom_latitude": format_coord(pair[0]) if gps_set else "",
        "classroom_longitude": format_coord(pair[1]) if gps_set else "",
        "classroom_gps_set": gps_set,
        "classroom_place_name": str(data.get("classroom_place_name", "")).strip() if gps_set else "",
    }


def load_settings(data_dir: Path | None = None) -> dict:
    data = _read_settings_file(data_dir)
    settings = {
        "teacher_email": str(data.get("teacher_email", "")).strip(),
        "public_base_url": str(data.get("public_base_url", "")).strip(),
    }
    settings.update(_classroom_fields(data))
    return settings


def save_settings(teacher_email: str, public_base_url: str, data_dir: Path | None = None) -> None:
    with _DATA_LOCK:
        payload = _read_settings_file(data_dir)
        payload["teacher_email"] = teacher_email.strip()
        payload["public_base_url"] = public_base_url.strip()
        _atomic_write(_settings_path(data_dir), json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8"))


def load_other_gps(data_dir: Path | None = None) -> tuple[float, float] | None:
    """Custom point saved on the settings page for 3-others."""
    return parse_gps_pair(str(_read_settings_file(data_dir).get("other_gps", "")))


def other_gps_text(data_dir: Path | None = None) -> str:
    pair = load_other_gps(data_dir)
    if pair is None:
        return ""
    return f"{format_coord(pair[0])}, {format_coord(pair[1])}"


def save_other_gps(text: str, data_dir: Path | None = None) -> None:
    pair = parse_gps_pair(text)
    with _DATA_LOCK:
        payload = _read_settings_file(data_dir)
        if pair is None:
            payload["other_gps"] = ""
            payload["other_gps_set"] = False
        else:
            payload["other_gps"] = f"{format_coord(pair[0])}, {format_coord(pair[1])}"
            payload["other_gps_set"] = True
        _atomic_write(_settings_path(data_dir), json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8"))


def saved_classroom_text(data_dir: Path | None = None) -> str:
    """Last classroom point saved in settings, used to prefill the start form."""
    settings = load_settings(data_dir)
    if not settings.get("classroom_gps_set"):
        return ""
    return f"{settings['classroom_latitude']}, {settings['classroom_longitude']}"


def save_classroom_default(text: str, place_name: str = "", data_dir: Path | None = None) -> None:
    """Remember a valid classroom point. An empty box does not erase the last one."""
    pair = parse_gps_pair(text)
    if pair is None:
        return
    with _DATA_LOCK:
        payload = _read_settings_file(data_dir)
        payload["classroom_latitude"] = format_coord(pair[0])
        payload["classroom_longitude"] = format_coord(pair[1])
        payload["classroom_gps_set"] = True
        if str(place_name or "").strip():
            payload["classroom_place_name"] = str(place_name).strip()
        _atomic_write(_settings_path(data_dir), json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8"))


def _https_context() -> ssl.SSLContext:
    """Python on this Mac does not use the system certificate store by itself."""
    try:
        import certifi
    except ImportError:
        certifi = None
    if certifi is not None:
        return ssl.create_default_context(cafile=certifi.where())
    system_bundle = Path("/etc/ssl/cert.pem")
    if system_bundle.exists():
        return ssl.create_default_context(cafile=str(system_bundle))
    return ssl.create_default_context()


def lookup_campus_address(address: str) -> dict | None:
    """One Nominatim search per click. None when the address cannot be resolved."""
    query = str(address or "").strip()
    if not query:
        return None
    url = NOMINATIM_URL + "?" + urlencode({"q": query, "format": "jsonv2", "limit": "1"})
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": NOMINATIM_USER_AGENT,
            "Accept-Language": "zh-Hant,zh;q=0.9,en;q=0.8",
        },
    )
    try:
        with urllib.request.urlopen(request, timeout=12, context=_https_context()) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, OSError, ValueError):
        return None
    if not isinstance(payload, list) or not payload:
        return None
    hit = payload[0] if isinstance(payload[0], dict) else None
    if hit is None:
        return None
    pair = parse_gps_pair(f"{hit.get('lat', '')}, {hit.get('lon', '')}")
    if pair is None:
        return None
    name = str(hit.get("display_name") or "").strip()
    return {"latitude": pair[0], "longitude": pair[1], "name": name}


def load_session(data_dir: Path | None = None) -> dict | None:
    path = ensure_data_dir(data_dir) / "session.json"
    if not path.exists():
        return None
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None
    if not isinstance(data, dict) or not data.get("class_date"):
        return None
    data["report_sent"] = bool(data.get("report_sent"))
    return data


def save_session(session: dict, data_dir: Path | None = None) -> None:
    path = ensure_data_dir(data_dir) / "session.json"
    with _DATA_LOCK:
        _atomic_write(path, json.dumps(session, ensure_ascii=False, indent=2).encode("utf-8"))


def session_matches(session: dict | None, event: str, start: str, end: str) -> bool:
    if not session:
        return False
    start_t = parse_hhmm(start)
    end_t = parse_hhmm(end)
    saved_start = parse_hhmm(session.get("start_time", ""))
    saved_end = parse_hhmm(session.get("end_time", ""))
    return (
        str(session.get("class_date")) == str(event).strip()
        and start_t is not None
        and end_t is not None
        and saved_start == start_t
        and saved_end == end_t
    )


def parse_gps_pair(text: str) -> tuple[float, float] | None:
    """Parse 'latitude, longitude'. Empty or anything other than two numbers is unset."""
    raw = str(text or "").strip()
    if not raw:
        return None
    parts = [part for part in raw.replace("，", ",").replace(" ", ",").split(",") if part.strip()]
    if len(parts) != 2:
        return None
    try:
        latitude = float(parts[0])
        longitude = float(parts[1])
    except ValueError:
        return None
    if latitude != latitude or longitude != longitude:
        return None
    if latitude in (float("inf"), float("-inf")) or longitude in (float("inf"), float("-inf")):
        return None
    if not (-90 <= latitude <= 90 and -180 <= longitude <= 180):
        return None
    return latitude, longitude


def haversine_meters(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    radius = 6371000
    phi1 = math.radians(lat1)
    phi2 = math.radians(lat2)
    d_phi = math.radians(lat2 - lat1)
    d_lambda = math.radians(lon2 - lon1)
    a = math.sin(d_phi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(d_lambda / 2) ** 2
    return 2 * radius * math.asin(math.sqrt(a))


def classroom_gps(session: dict | None) -> tuple[float, float] | None:
    if not isinstance(session, dict) or not session.get("classroom_gps_set"):
        return None
    return parse_gps_pair(f"{session.get('classroom_latitude', '')}, {session.get('classroom_longitude', '')}")


def load_campuses(data_dir: Path | None = None) -> list[dict]:
    """Saved campuses. The list can hold more than one; only verified points are stored."""
    raw = _read_settings_file(data_dir).get("campuses")
    if not isinstance(raw, list):
        return []
    campuses: list[dict] = []
    for item in raw:
        if not isinstance(item, dict):
            continue
        name = str(item.get("name", "")).strip()
        pair = parse_gps_pair(f"{item.get('latitude', '')}, {item.get('longitude', '')}")
        if not name or pair is None:
            continue
        campuses.append({"name": name, "latitude": pair[0], "longitude": pair[1]})
    return campuses


def compare_to_selected_campus(session: dict | None, latitude: float, longitude: float) -> tuple[str, str, str]:
    """Compare only with the campus chosen for this lesson."""
    point = classroom_gps(session)
    name = str((session or {}).get("campus_name", "")).strip()
    if name == CAMPUS_OTHERS:
        name = CAMPUS_OTHERS_NAME
    if point is None or not name:
        return "", LOCATION_UNSET, ""
    distance = haversine_meters(point[0], point[1], latitude, longitude)
    result = LOCATION_MATCH if distance <= LOCATION_RADIUS_M else LOCATION_AWAY
    return format(distance, ".1f"), result, name


def campus_point_for_choice(label: str, data_dir: Path | None = None) -> tuple[float, float] | None:
    if label in FIXED_CAMPUSES:
        return FIXED_CAMPUSES[label]
    if label == CAMPUS_OTHERS:
        return load_other_gps(data_dir)
    return None


def start_lesson(
    class_date: date,
    start: time,
    end: time,
    remarks: str,
    campus_label: str = "",
    data_dir: Path | None = None,
) -> dict:
    """Write session.json. Existing attendance rows stay, including after a new time slot."""
    root = ensure_data_dir(data_dir)
    new_date = class_date.strftime("%Y-%m-%d")
    new_start = format_hhmm(start)
    new_end = format_hhmm(end)
    point = campus_point_for_choice(campus_label, root) if campus_label else None
    with _DATA_LOCK:
        existing = load_session(root)
        same = (
            existing is not None
            and existing.get("class_date") == new_date
            and existing.get("start_time") == new_start
            and existing.get("end_time") == new_end
        )
        if point and campus_label:
            classroom_latitude = format_coord(point[0])
            classroom_longitude = format_coord(point[1])
            classroom_gps_set = True
            campus_name = CAMPUS_OTHERS_NAME if campus_label == CAMPUS_OTHERS else campus_label
        elif isinstance(existing, dict) and existing.get("classroom_gps_set") and not campus_label:
            classroom_latitude = str(existing.get("classroom_latitude", ""))
            classroom_longitude = str(existing.get("classroom_longitude", ""))
            classroom_gps_set = True
            campus_name = str(existing.get("campus_name", ""))
        else:
            classroom_latitude = ""
            classroom_longitude = ""
            classroom_gps_set = False
            campus_name = ""
        session = {
            "class_date": new_date,
            "start_time": new_start,
            "end_time": new_end,
            "remarks": remarks.strip(),
            "campus_name": campus_name,
            "classroom_latitude": classroom_latitude,
            "classroom_longitude": classroom_longitude,
            "classroom_gps_set": classroom_gps_set,
            "started_at": (
                existing.get("started_at")
                if same and existing.get("started_at")
                else datetime.now().replace(microsecond=0).isoformat(timespec="seconds")
            ),
            "report_sent": bool(existing.get("report_sent")) if same else False,
            "report_sent_at": existing.get("report_sent_at") if same else None,
        }
        save_session(session, root)
    return {"session": session, "reset_attendance": False}


HEADER_ALIASES = {
    "student name": "student_name",
    "student_name": "student_name",
    "姓名": "student_name",
    "student email": "student_email",
    "student_email": "student_email",
    "電郵": "student_email",
    "email": "student_email",
    "student number": "student_number",
    "student_number": "student_number",
    "學號": "student_number",
    "student no": "student_number",
}


def normalize_header(column: object) -> str:
    text = str(column).replace("\ufeff", "").strip().lower()
    text = " ".join(text.split())
    return HEADER_ALIASES.get(text, text)


def _clean_roster_frame(df: pd.DataFrame) -> pd.DataFrame:
    frame = df.copy()
    frame.columns = [normalize_header(column) for column in frame.columns]
    frame = frame.loc[:, ~frame.columns.duplicated()]
    missing = [column for column in ROSTER_COLUMNS if column not in frame.columns]
    if missing:
        raise ValueError("CSV 缺少欄位：" + ", ".join(missing))
    frame = frame[ROSTER_COLUMNS].fillna("")
    for column in ROSTER_COLUMNS:
        frame[column] = frame[column].map(lambda value: str(value).strip())
    frame["student_number"] = frame["student_number"].map(norm_number)
    frame = frame[(frame["student_email"] != "") & (frame["student_number"] != "")]
    frame["_key"] = frame["student_email"].map(norm_email) + "|" + frame["student_number"]
    frame = frame.drop_duplicates("_key", keep="first").drop(columns="_key")
    return frame.reset_index(drop=True)


def read_roster_upload(raw: bytes) -> pd.DataFrame:
    last_error: Exception | None = None
    frame = None
    for encoding in ("utf-8-sig", "utf-8", "cp950"):
        try:
            frame = pd.read_csv(io.StringIO(raw.decode(encoding)), dtype=str)
            break
        except UnicodeDecodeError as exc:
            last_error = exc
    if frame is None:
        raise ValueError("無法讀取 CSV 編碼，請用 UTF-8 儲存。") from last_error
    return _clean_roster_frame(frame)


def load_roster(data_dir: Path | None = None) -> pd.DataFrame:
    path = ensure_data_dir(data_dir) / "roster.csv"
    if not path.exists():
        return pd.DataFrame(columns=ROSTER_COLUMNS)
    try:
        frame = pd.read_csv(path, dtype=str, encoding="utf-8-sig").fillna("")
        return _clean_roster_frame(frame)
    except (ValueError, OSError, pd.errors.ParserError):
        return pd.DataFrame(columns=ROSTER_COLUMNS)


def save_roster(frame: pd.DataFrame, data_dir: Path | None = None) -> int:
    cleaned = _clean_roster_frame(frame)
    path = ensure_data_dir(data_dir) / "roster.csv"
    with _DATA_LOCK:
        buffer = io.StringIO()
        cleaned.to_csv(buffer, index=False)
        # utf-8-sig so Excel opens the Chinese names.
        _atomic_write(path, buffer.getvalue().encode("utf-8-sig"))
    return len(cleaned)


def find_student(email: str, student_number: str, data_dir: Path | None = None) -> dict | None:
    wanted_email = norm_email(email)
    wanted_number = norm_number(student_number)
    if not wanted_email or not wanted_number:
        return None
    roster = load_roster(data_dir)
    for row in roster.to_dict(orient="records"):
        if norm_email(row["student_email"]) == wanted_email and norm_number(row["student_number"]) == wanted_number:
            return {
                "student_name": str(row["student_name"]).strip(),
                "student_email": str(row["student_email"]).strip(),
                "student_number": norm_number(row["student_number"]),
            }
    return None


def load_attendance(data_dir: Path | None = None) -> pd.DataFrame:
    path = ensure_data_dir(data_dir) / "attendance.xlsx"
    if not path.exists():
        return pd.DataFrame(columns=ATTENDANCE_COLUMNS)
    try:
        frame = pd.read_excel(path, dtype=str, engine="openpyxl").fillna("")
    except Exception:
        return pd.DataFrame(columns=ATTENDANCE_COLUMNS)
    for column in ATTENDANCE_COLUMNS:
        if column not in frame.columns:
            frame[column] = ""
    return frame[ATTENDANCE_COLUMNS]


def save_attendance(frame: pd.DataFrame, data_dir: Path | None = None) -> None:
    root = ensure_data_dir(data_dir)
    table = frame.copy()
    for column in ATTENDANCE_COLUMNS:
        if column not in table.columns:
            table[column] = ""
    table = table[ATTENDANCE_COLUMNS].fillna("").astype(str)
    path = root / "attendance.xlsx"
    temporary = root / ".attendance.writing.xlsx"
    with pd.ExcelWriter(temporary, engine="openpyxl") as writer:
        table.to_excel(writer, index=False, sheet_name="attendance")
        sheet = writer.sheets["attendance"]
        for column_cells in sheet.columns:
            for cell in column_cells:
                cell.number_format = "@"
    temporary.replace(path)


def parse_checkin_time(value: object) -> datetime | None:
    text = str(value or "").strip()
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
        try:
            return datetime.strptime(text, fmt)
        except ValueError:
            continue
    return None


def latest_checkin_at(email: str, student_number: str, data_dir: Path | None = None) -> datetime | None:
    """Latest check-in time for this email or this student number, on any lesson."""
    wanted_email = norm_email(email)
    wanted_number = norm_number(student_number)
    if not wanted_email and not wanted_number:
        return None
    attendance = load_attendance(data_dir)
    if attendance.empty:
        return None
    latest: datetime | None = None
    for row in attendance.to_dict(orient="records"):
        row_email = norm_email(row.get("student_email", ""))
        row_number = norm_number(row.get("student_number", ""))
        matched = (wanted_email and row_email == wanted_email) or (wanted_number and row_number == wanted_number)
        if not matched:
            continue
        when = parse_checkin_time(row.get("checkin_time", ""))
        if when is None:
            continue
        if latest is None or when > latest:
            latest = when
    return latest


def checkin_too_soon(
    email: str,
    student_number: str,
    when: datetime | None = None,
    data_dir: Path | None = None,
) -> bool:
    """True when the latest matching row is less than 4 hours before this attempt."""
    latest = latest_checkin_at(email, student_number, data_dir)
    if latest is None:
        return False
    moment = when or datetime.now()
    if moment.tzinfo is not None:
        moment = moment.astimezone().replace(tzinfo=None)
    moment = moment.replace(microsecond=0)
    return moment - latest < CHECKIN_GAP


def attendance_row_for(email: str, student_number: str, data_dir: Path | None = None) -> dict | None:
    """The saved check-in for this student, if one already exists."""
    wanted_email = norm_email(email)
    wanted_number = norm_number(student_number)
    if not wanted_email or not wanted_number:
        return None
    attendance = load_attendance(data_dir)
    if attendance.empty:
        return None
    for row in attendance.to_dict(orient="records"):
        if norm_email(row.get("student_email", "")) == wanted_email and norm_number(row.get("student_number", "")) == wanted_number:
            return row
    return None


def already_checked_in(email: str, student_number: str, data_dir: Path | None = None) -> bool:
    return attendance_row_for(email, student_number, data_dir) is not None


def validate_identity(email: str, student_number: str, data_dir: Path | None = None) -> dict:
    if not str(email or "").strip() or not str(student_number or "").strip():
        return {"ok": False, "message": "請輸入學生電郵和學生編號"}
    with _DATA_LOCK:
        student = find_student(email, student_number, data_dir)
        if student is None:
            return {"ok": False, "message": INVALID_INPUT}
    return {"ok": True, "student": student, "message": ""}


def format_coord(value: float) -> str:
    return format(float(value), ".8f").rstrip("0").rstrip(".")


def map_link(latitude: float, longitude: float) -> str:
    return f"https://maps.google.com/?q={format_coord(latitude)},{format_coord(longitude)}"


def record_checkin(
    email: str,
    student_number: str,
    session: dict,
    latitude: float,
    longitude: float,
    accuracy: float,
    data_dir: Path | None = None,
    checkin: datetime | None = None,
) -> dict:
    """Save one attendance row, then try the student email. Never claims a send that did not happen."""
    when = checkin or datetime.now()
    if when.tzinfo is not None:
        when = when.astimezone().replace(tzinfo=None)
    when = when.replace(microsecond=0)
    class_date = parse_date(session.get("class_date", ""))
    start = parse_hhmm(session.get("start_time", ""))
    if class_date is None or start is None:
        return {"ok": False, "email_sent": False, "message": "課堂時間不正確。"}

    with _DATA_LOCK:
        identity = validate_identity(email, student_number, data_dir)
        if not identity["ok"]:
            return {"ok": False, "email_sent": False, "message": identity["message"]}
        student = identity["student"]
        if checkin_too_soon(email, student_number, when, data_dir) or checkin_too_soon(
            student["student_email"], student["student_number"], when, data_dir
        ):
            return {"ok": False, "email_sent": False, "message": TOO_SOON}
        status, email_text = classify_checkin(when, class_date, start)
        lat_text = format_coord(latitude)
        lng_text = format_coord(longitude)
        distance_meters, location_result, campus_name = compare_to_selected_campus(session, latitude, longitude)
        try:
            outside = float(distance_meters) > LOCATION_RADIUS_M
        except (TypeError, ValueError):
            outside = False
        row = {
            "student_name": student["student_name"],
            "student_email": student["student_email"],
            "student_number": student["student_number"],
            "checkin_time": when.strftime("%Y-%m-%d %H:%M:%S"),
            "class_date": class_date.isoformat(),
            "status": status,
            "latitude": lat_text,
            "longitude": lng_text,
            "accuracy_meters": format(float(accuracy), ".1f"),
            "distance_meters": distance_meters,
            "location_result": location_result,
            "campus_name": campus_name,
            "可能不在校園": "是" if outside else "",
            "map_url": f"https://maps.google.com/?q={lat_text},{lng_text}",
        }
        attendance = load_attendance(data_dir)
        attendance = pd.concat([attendance, pd.DataFrame([row])], ignore_index=True)
        save_attendance(attendance, data_dir)
        email_text = student_email_body(email_text, row["可能不在校園"])

    email_sent, warning = _send_student_after_save(student["student_email"], email_text)
    return {
        "ok": True,
        "email_sent": email_sent,
        "warning": "" if email_sent else warning,
        "message": THANK_YOU if email_sent else warning,
        "status": status,
        "email_text": email_text,
        "row": row,
    }


def _secrets_file() -> Path:
    return APP_DIR / ".streamlit" / "secrets.toml"


def _from_secrets(key: str) -> str:
    if not _secrets_file().exists():
        return ""
    try:
        if key in st.secrets:
            return str(st.secrets[key]).strip()
    except Exception:
        return ""
    return ""


def _parse_env_file(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    parsed: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#") or "=" not in stripped:
            continue
        key, value = stripped.split("=", 1)
        parsed[key.strip()] = value.strip()
    return parsed


def clean_smtp_field(value: object) -> str:
    """Drop spaces, newlines, and surrounding quotes before SMTP login."""
    text = str(value or "").replace("\ufeff", "").strip()
    quotes = {'"', "'", "“", "”", "‘", "’"}
    while len(text) >= 2 and text[0] in quotes and text[-1] in quotes:
        text = text[1:-1].strip()
    return "".join(ch for ch in text if ch not in " \t\r\n")


def _smtp_is_placeholder(user: str, password: str) -> bool:
    return user.lower() in {"", "your-gmail@gmail.com"} or password in {"", "the-app-password"}


def _smtp_file_ready(parsed: dict[str, str]) -> bool:
    """A file is usable when it is not the sample and the login has one @."""
    user = clean_smtp_field(parsed.get("SMTP_USER", ""))
    password = clean_smtp_field(parsed.get("SMTP_PASSWORD", ""))
    if _smtp_is_placeholder(user, password):
        return False
    return user.count("@") == 1


def _smtp_source_values() -> tuple[str, dict[str, str]]:
    """Read the SMTP files from disk. smtp.txt wins only when it is usable."""
    from_txt = _parse_env_file(APP_DIR / "smtp.txt")
    from_env = _parse_env_file(APP_DIR / ".env")
    if _smtp_file_ready(from_txt):
        return "smtp.txt", from_txt
    if _smtp_file_ready(from_env):
        return ".env", from_env
    return "", {}


def smtp_config() -> dict | None:
    """Load SMTP from the file on every send. File values override the process environment."""
    source_name, chosen = _smtp_source_values()
    values: dict[str, str] = {}
    for key in SMTP_KEYS:
        file_value = chosen.get(key, "") if source_name else ""
        if str(file_value).strip():
            raw = file_value
        else:
            raw = _from_secrets(key) or os.getenv(key, "")
        if key in {"SMTP_USER", "SMTP_PASSWORD", "SMTP_FROM"}:
            values[key] = clean_smtp_field(raw)
        else:
            values[key] = str(raw or "").strip()
    if not all(values.values()) or not _smtp_file_ready(
        {"SMTP_USER": values["SMTP_USER"], "SMTP_PASSWORD": values["SMTP_PASSWORD"]}
    ):
        return None
    return values


def deliver(message: EmailMessage, cfg: dict) -> None:
    host = cfg["SMTP_HOST"]
    try:
        port = int(str(cfg["SMTP_PORT"]).strip())
    except ValueError as exc:
        raise RuntimeError("SMTP_PORT 必須是數字。") from exc
    if port == 465:
        server_cm = smtplib.SMTP_SSL(host, port, timeout=20)
    else:
        server_cm = smtplib.SMTP(host, port, timeout=20)
    with server_cm as server:
        server.ehlo()
        if port != 465:
            server.starttls()
            server.ehlo()
        server.login(cfg["SMTP_USER"], cfg["SMTP_PASSWORD"])
        server.send_message(message)


def student_email_body(status_line: str, outside_flag: str) -> str:
    """Status line, plus 可能不在校園 only when that attendance flag is 是."""
    line = str(status_line or "").strip()
    if str(outside_flag or "").strip() == "是":
        return f"{line}\n可能不在校園"
    return line


def send_student_email(to_email: str, body_text: str) -> None:
    cfg = smtp_config()
    if cfg is None:
        raise RuntimeError("SMTP 尚未設定")
    message = EmailMessage()
    message["Subject"] = "課堂點名確認"
    message["From"] = cfg["SMTP_FROM"]
    message["To"] = to_email
    message.set_content(body_text)
    deliver(message, cfg)


def send_teacher_report(to_email: str, xlsx_path: Path, body_text: str) -> None:
    cfg = smtp_config()
    if cfg is None:
        raise RuntimeError("SMTP 尚未設定")
    message = EmailMessage()
    message["Subject"] = "課堂出席報告"
    message["From"] = cfg["SMTP_FROM"]
    message["To"] = to_email
    message.set_content(body_text)
    payload = Path(xlsx_path).read_bytes()
    message.add_attachment(
        payload,
        maintype="application",
        subtype="vnd.openxmlformats-officedocument.spreadsheetml.sheet",
        filename="attendance.xlsx",
    )
    deliver(message, cfg)


def _send_student_after_save(to_email: str, body_text: str) -> tuple[bool, str]:
    if smtp_config() is None:
        return False, STUDENT_EMAIL_SKIPPED
    try:
        send_student_email(to_email, body_text)
    except Exception:
        return False, STUDENT_EMAIL_FAILED
    return True, ""


def teacher_report_body(session: dict, data_dir: Path | None = None) -> str:
    attendance = load_attendance(data_dir)
    counts = {STATUS_ON_TIME: 0, STATUS_LATE: 0, STATUS_ABSENT: 0}
    if not attendance.empty:
        for status in attendance["status"].tolist():
            if status in counts:
                counts[status] += 1
    remarks = session.get("remarks") or "（無）"
    return (
        "附件是這一節的出席紀錄。\n\n"
        f"日期：{session.get('class_date')}\n"
        f"時間：{session.get('start_time')}–{session.get('end_time')}\n"
        f"備註：{remarks}\n"
        f"準時出席：{counts[STATUS_ON_TIME]}\n"
        f"遲到：{counts[STATUS_LATE]}\n"
        f"缺席：{counts[STATUS_ABSENT]}\n"
    )


def ensure_attendance_file(data_dir: Path | None = None) -> Path:
    root = ensure_data_dir(data_dir)
    path = root / "attendance.xlsx"
    with _DATA_LOCK:
        if not path.exists():
            save_attendance(pd.DataFrame(columns=ATTENDANCE_COLUMNS), root)
    return path


def finish_class(data_dir: Path | None = None) -> dict:
    """Email attendance.xlsx once. A failed or unconfigured send stays unsent."""
    with _SEND_LOCK:
        return _finish_class(data_dir)


def _finish_class(data_dir: Path | None = None) -> dict:
    with _DATA_LOCK:
        session = load_session(data_dir)
        if not session:
            return {"ok": False, "email_sent": False, "message": "尚未開始課堂。"}
        if session.get("report_sent"):
            return {
                "ok": False,
                "email_sent": False,
                "already_sent": True,
                "message": "這節課的報告已經發送過，不會再寄一次。",
            }
        teacher = load_settings(data_dir).get("teacher_email", "").strip()
        if not teacher:
            return {"ok": False, "email_sent": False, "message": "尚未設定老師電郵，報告未發送。"}
        path = ensure_attendance_file(data_dir)
        body = teacher_report_body(session, data_dir)

    if smtp_config() is None:
        return {"ok": False, "email_sent": False, "message": TEACHER_EMAIL_SKIPPED}
    try:
        send_teacher_report(teacher, path, body)
    except Exception as exc:
        return {"ok": False, "email_sent": False, "message": f"報告未發送：{exc}"}

    with _DATA_LOCK:
        session = load_session(data_dir) or session
        session["report_sent"] = True
        session["report_sent_at"] = datetime.now().replace(microsecond=0).isoformat(timespec="seconds")
        save_session(session, data_dir)
    return {"ok": True, "email_sent": True, "message": "已把出席報告寄給老師。"}


def normalize_base(base: str) -> str:
    text = str(base or "").strip().rstrip("/")
    if not text:
        return ""
    if not text.startswith(("http://", "https://")):
        text = "http://" + text
    return text


def build_student_url(base: str, class_date: str, start: str, end: str, token: str) -> str:
    root = normalize_base(base).rstrip("/")
    return f"{root}?event={class_date}&start={start}&end={end}&token={token}"


def https_origin_path(data_dir: Path | None = None) -> Path:
    return ensure_data_dir(data_dir) / "https_origin.txt"


def load_https_origin(data_dir: Path | None = None) -> str:
    path = https_origin_path(data_dir)
    if not path.exists():
        return ""
    text = path.read_text(encoding="utf-8").strip().rstrip("/")
    if text.startswith("https://"):
        return text
    return ""


def save_https_origin(url: str, data_dir: Path | None = None) -> None:
    text = str(url or "").strip().rstrip("/")
    if not text.startswith("https://"):
        raise ValueError("學生網址必須是 https。")
    _atomic_write(https_origin_path(data_dir), (text + "\n").encode("utf-8"))
    settings = load_settings(data_dir)
    save_settings(settings.get("teacher_email", ""), text, data_dir)


def space_https_origin() -> str:
    """The Space's own https URL. Empty when this process is not running on Hugging Face."""
    host = str(os.environ.get("SPACE_HOST", "")).strip().rstrip("/")
    if host:
        if "://" in host:
            host = host.split("://", 1)[1]
        return "https://" + host.split("/")[0]
    space_id = str(os.environ.get("SPACE_ID", "")).strip().strip("/")
    if space_id.count("/") != 1:
        return ""
    owner, name = space_id.split("/", 1)
    owner = owner.strip().lower().replace("_", "-")
    name = name.strip().lower().replace("_", "-")
    if not owner or not name:
        return ""
    return f"https://{owner}-{name}.hf.space"


def student_origin(data_dir: Path | None = None) -> str:
    """HTTPS origin used for the teacher QR. Plain http cannot read iPhone GPS."""
    hosted = space_https_origin()
    if hosted:
        return hosted
    https = load_https_origin(data_dir)
    if https:
        return https
    configured = normalize_base(load_settings(data_dir).get("public_base_url", ""))
    if configured.startswith("https://"):
        return configured.rstrip("/")
    return ""


def _tokens_path(data_dir: Path | None = None) -> Path:
    return ensure_data_dir(data_dir) / "qr_tokens.json"


def _load_tokens(data_dir: Path | None = None) -> dict:
    path = _tokens_path(data_dir)
    if not path.exists():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return {}
    return data if isinstance(data, dict) else {}


def _save_tokens(tokens: dict, data_dir: Path | None = None) -> None:
    _atomic_write(_tokens_path(data_dir), json.dumps(tokens, ensure_ascii=False, indent=2).encode("utf-8"))


def _grant_is_open(entry: dict, now: datetime) -> bool:
    """A claimed code stays valid for the rest of check-in, past the 30-second QR."""
    raw = entry.get("grant_expires_at")
    if not raw:
        return False
    try:
        return now < datetime.fromisoformat(str(raw))
    except ValueError:
        return False


def _prune_tokens(tokens: dict, now: datetime) -> dict:
    kept: dict = {}
    current = tokens.get("_current")
    if isinstance(current, str):
        kept["_current"] = current
    cutoff = now - timedelta(minutes=30)
    for key, entry in tokens.items():
        if key == "_current" or not isinstance(entry, dict):
            continue
        if _grant_is_open(entry, now):
            kept[key] = entry
            continue
        try:
            expires = datetime.fromisoformat(str(entry.get("expires_at")))
        except ValueError:
            continue
        if expires >= cutoff:
            kept[key] = entry
    return kept


def current_qr_token(class_date: str, start: str, end: str, data_dir: Path | None = None) -> dict:
    """Keep one token for 30 seconds, then replace it."""
    now = datetime.now().replace(microsecond=0)
    with _DATA_LOCK:
        tokens = _prune_tokens(_load_tokens(data_dir), now)
        current = tokens.get("_current")
        entry = tokens.get(current) if isinstance(current, str) else None
        if isinstance(entry, dict):
            try:
                expires = datetime.fromisoformat(str(entry.get("expires_at")))
            except ValueError:
                expires = now
            same_class = (
                entry.get("class_date") == class_date
                and entry.get("start_time") == start
                and entry.get("end_time") == end
            )
            if same_class and now < expires:
                _save_tokens(tokens, data_dir)
                return {"token": current, "expires_at": entry["expires_at"]}
        token = secrets.token_urlsafe(16)
        expires = now + QR_TTL
        tokens[token] = {
            "expires_at": expires.isoformat(timespec="seconds"),
            "used": False,
            "class_date": class_date,
            "start_time": start,
            "end_time": end,
        }
        tokens["_current"] = token
        _save_tokens(tokens, data_dir)
        return {"token": token, "expires_at": tokens[token]["expires_at"]}


def claim_qr_token(token: str, class_date: str, start: str, end: str, data_dir: Path | None = None) -> str:
    """Mark a QR token used and return a check-in grant. Empty if the code is no longer valid."""
    now = datetime.now()
    with _DATA_LOCK:
        tokens = _load_tokens(data_dir)
        entry = tokens.get(token)
        if not isinstance(entry, dict) or entry.get("used"):
            return ""
        if entry.get("class_date") != class_date or entry.get("start_time") != start or entry.get("end_time") != end:
            return ""
        try:
            expires = datetime.fromisoformat(str(entry.get("expires_at")))
        except ValueError:
            return ""
        if now >= expires:
            return ""
        grant = secrets.token_urlsafe(16)
        entry["used"] = True
        entry["grant"] = grant
        entry["grant_expires_at"] = (now + GRANT_TTL).isoformat(timespec="seconds")
        tokens[token] = entry
        _save_tokens(tokens, data_dir)
        return grant


def resume_qr_grant(token: str, grant: str, class_date: str, start: str, end: str, data_dir: Path | None = None) -> bool:
    """Accept the same claimed code after the GPS page redirects back."""
    if not token or not grant:
        return False
    now = datetime.now()
    with _DATA_LOCK:
        entry = _load_tokens(data_dir).get(token)
        if not isinstance(entry, dict) or not entry.get("used"):
            return False
        if entry.get("grant") != grant:
            return False
        if entry.get("class_date") != class_date or entry.get("start_time") != start or entry.get("end_time") != end:
            return False
        return _grant_is_open(entry, now)


def remember_student_on_grant(token: str, grant: str, student: dict, data_dir: Path | None = None) -> None:
    """Keep the verified student on the grant so the GPS redirect can restore them."""
    if not token or not grant or not isinstance(student, dict):
        return
    record = {
        "student_name": str(student.get("student_name", "")).strip(),
        "student_email": str(student.get("student_email", "")).strip(),
        "student_number": str(student.get("student_number", "")).strip(),
    }
    if not record["student_email"] or not record["student_number"]:
        return
    with _DATA_LOCK:
        tokens = _load_tokens(data_dir)
        entry = tokens.get(token)
        if not isinstance(entry, dict) or entry.get("grant") != grant:
            return
        if entry.get("student") == record:
            return
        entry["student"] = record
        tokens[token] = entry
        _save_tokens(tokens, data_dir)


def student_on_grant(token: str, grant: str, data_dir: Path | None = None) -> dict | None:
    if not token or not grant:
        return None
    entry = _load_tokens(data_dir).get(token)
    if not isinstance(entry, dict) or entry.get("grant") != grant:
        return None
    student = entry.get("student")
    if not isinstance(student, dict):
        return None
    name = str(student.get("student_name", "")).strip()
    email = str(student.get("student_email", "")).strip()
    number = str(student.get("student_number", "")).strip()
    if not email or not number:
        return None
    return {"student_name": name, "student_email": email, "student_number": number}


def locate_page_url(event: str, start: str, end: str, token: str, grant: str) -> str:
    query = urlencode(
        {
            "event": event,
            "start": start,
            "end": end,
            "token": token,
            "grant": grant,
        }
    )
    return f"/app/static/locate.html?{query}"


def _finite_float(raw: str) -> float | None:
    if not raw:
        return None
    try:
        value = float(raw)
    except ValueError:
        return None
    if value != value or value in (float("inf"), float("-inf")):
        return None
    return value


def location_from_query() -> dict | None:
    """Read lat, lng, and accuracy added by the top-level locate page."""
    raws = (_qp("lat"), _qp("lng"), _qp("accuracy"))
    if not any(raws):
        return None
    latitude = _finite_float(raws[0])
    longitude = _finite_float(raws[1])
    accuracy = _finite_float(raws[2])
    if latitude is None or longitude is None or accuracy is None:
        return {"ok": False}
    if not (-90 <= latitude <= 90 and -180 <= longitude <= 180) or accuracy < 0:
        return {"ok": False}
    return {"ok": True, "latitude": latitude, "longitude": longitude, "accuracy": accuracy}


def lan_ip() -> str:
    for interface in ("en0", "en1"):
        try:
            output = subprocess.check_output(
                ["ipconfig", "getifaddr", interface],
                text=True,
                stderr=subprocess.DEVNULL,
            ).strip()
        except (OSError, subprocess.CalledProcessError):
            continue
        if output:
            return output
    return "127.0.0.1"


def lan_base_url() -> str:
    return f"http://{lan_ip()}:{APP_PORT}"


def make_qr_image(url: str) -> Image.Image:
    code = qrcode.QRCode(
        error_correction=qrcode.constants.ERROR_CORRECT_M,
        box_size=8,
        border=2,
    )
    code.add_data(url)
    code.make(fit=True)
    return code.make_image(fill_color="#1a2332", back_color="white").convert("RGB")


def inject_css() -> None:
    st.markdown(
        """
        <style>
        html, body, .stApp,
        [data-testid="stAppViewContainer"],
        [data-testid="stMain"] {
            overflow-x: hidden;
            max-width: 100%;
        }
        .stApp {
            background: #f4f1ea;
            color: #1a2332;
        }
        [data-testid="stSidebar"],
        [data-testid="stSidebarCollapsedControl"] { display: none; }
        [data-testid="stMainBlockContainer"],
        .block-container {
            max-width: 760px;
            padding-top: 1.4rem;
            padding-left: 1.5rem !important;
            padding-right: 1.5rem !important;
            box-sizing: border-box;
        }
        @media (max-width: 480px) {
            [data-testid="stMainBlockContainer"],
            .block-container {
                padding-left: 1.75rem !important;
                padding-right: 1.25rem !important;
            }
        }
        div.stButton > button {
            width: 100%;
            border-radius: 10px;
            padding: 0.65rem 1rem;
        }
        [data-testid="stDialog"],
        [role="dialog"] {
            font-size: 1.2rem;
        }
        [data-testid="stDialog"] h1,
        [data-testid="stDialog"] h2,
        [role="dialog"] h1,
        [role="dialog"] h2 {
            font-size: 1.55rem !important;
            line-height: 1.35 !important;
        }
        [data-testid="stDialog"] div.stButton > button,
        [role="dialog"] div.stButton > button {
            min-height: 3.6rem;
            font-size: 1.3rem;
            font-weight: 700;
        }
        a.gps-fill {
            display: flex;
            align-items: center;
            justify-content: center;
            width: 100%;
            min-height: 3.2rem;
            margin: 0.4rem 0 0.8rem;
            padding: 0.7rem 1rem;
            box-sizing: border-box;
            border-radius: 10px;
            background: #1f6b4a;
            color: #fffdf8 !important;
            font-size: 1.15rem;
            font-weight: 700;
            text-align: center;
            text-decoration: none;
        }
        a.locate-launch {
            display: flex;
            align-items: center;
            justify-content: center;
            width: 100%;
            min-height: 4.5rem;
            margin: 0.8rem 0 1rem;
            padding: 1rem 1.1rem;
            box-sizing: border-box;
            border-radius: 14px;
            background: #1f6b4a;
            color: #fffdf8 !important;
            font-size: 1.45rem;
            font-weight: 700;
            line-height: 1.2;
            text-align: center;
            text-decoration: none;
        }
        [data-testid="stMain"] h1,
        [data-testid="stMain"] p,
        [data-testid="stCaptionContainer"] {
            overflow-wrap: anywhere;
        }
        [data-testid="stHeading"],
        [data-testid="stHeading"] h1,
        [data-testid="stHeading"] h2,
        [data-testid="stHeading"] h3,
        [data-testid="stHeading"] span,
        [data-testid="stMarkdownContainer"],
        [data-testid="stMarkdownContainer"] p,
        [data-testid="stMarkdownContainer"] span,
        [data-testid="stMarkdownContainer"] li,
        [data-testid="stCaptionContainer"],
        [data-testid="stCaptionContainer"] p {
            color: #1a2332 !important;
        }
        </style>
        """,
        unsafe_allow_html=True,
    )


def _qp(name: str) -> str:
    value = st.query_params.get(name, "")
    if isinstance(value, (list, tuple)):
        value = value[0] if value else ""
    return str(value).strip()


def student_query() -> tuple[str, str, str, str] | None:
    event, start, end, token = _qp("event"), _qp("start"), _qp("end"), _qp("token")
    if not event and not start and not end and not token:
        return None
    return event, start, end, token


def render_landing() -> None:
    st.title("課堂點名系統")
    st.write(
        "老師開一節課，學生用手機掃 QR，核對學籍並開啟一次定位。"
        "名冊、課堂和出席都寫在這部電腦的 data 資料夾，"
        "所以另一部手機開啟連結也會讀到同一班。"
    )
    roster = load_roster()
    session = load_session()
    if roster.empty:
        st.info("尚未上傳名冊。請先到「設定」。")
    else:
        st.caption(f"名冊已有 {len(roster)} 人。")
    if session:
        st.caption(
            f"進行中的課堂：{session['class_date']} {session['start_time']}–{session['end_time']}"
        )
    if st.button("開始使用", type="primary"):
        st.session_state.page = "teacher"
        st.rerun()
    if st.button("設定"):
        st.session_state.page = "settings"
        st.rerun()


def render_settings() -> None:
    st.title("設定")
    st.caption("名冊存在 data/roster.csv，老師電郵和公開網址存在 data/settings.json。")
    if st.button("返回主頁"):
        st.session_state.page = "landing"
        st.rerun()

    template_path = APP_DIR / "data" / "roster_template.csv"
    if not template_path.exists():
        template_path = ensure_data_dir() / "roster_template.csv"
    st.download_button(
        "下載名冊範本",
        data=template_path.read_bytes() if template_path.exists() else b"",
        file_name="roster_template.csv",
        mime="text/csv",
    )
    st.caption("欄位可以是 Student name、Student Email、Student Number，或 student_name、student_email、student_number，也接受姓名、電郵、學號。")

    upload = st.file_uploader("上傳名冊 CSV", type=["csv"])
    if st.button("儲存名冊"):
        if upload is None:
            st.error("請先選擇 CSV 檔。")
        else:
            try:
                frame = read_roster_upload(upload.getvalue())
                count = save_roster(frame)
            except Exception as exc:
                st.error(f"讀取 CSV 失敗：{exc}")
            else:
                st.success(f"已儲存 {count} 位學生到 data/roster.csv。")

    roster = load_roster()
    if roster.empty:
        st.info("尚未有名冊。")
    else:
        st.dataframe(roster, width="stretch", hide_index=True)

    st.divider()
    settings = load_settings()
    if "teacher_email_input" not in st.session_state:
        st.session_state.teacher_email_input = settings.get("teacher_email", "")
    if "public_base_url_input" not in st.session_state:
        st.session_state.public_base_url_input = settings.get("public_base_url", "")
    if "other_gps_input" not in st.session_state:
        st.session_state.other_gps_input = other_gps_text()

    st.text_input("老師電郵", key="teacher_email_input")
    st.text_input(
        "公開網址",
        key="public_base_url_input",
        help="學生手機用來開啟 QR 的網址。不要填 localhost。",
    )
    st.caption("學生 QR 使用 HTTPS 網址（data/https_origin.txt）。iPhone 在下面這個 http 區網網址不會提供定位。")
    st.code(lan_base_url(), language=None)
    https_origin = load_https_origin()
    if https_origin:
        st.caption(f"目前學生網址：{https_origin}")

    def fill_lan() -> None:
        st.session_state.public_base_url_input = lan_base_url()

    st.button("填入這個區網網址", on_click=fill_lan)

    st.text_input(
        "其他地點 GPS",
        key="other_gps_input",
        placeholder="22.28000, 114.17000",
        help="緯度, 經度。開始課堂選 3-others 時使用。",
    )

    if st.button("儲存設定", type="primary"):
        teacher_email = st.session_state.teacher_email_input.strip()
        public_base = st.session_state.public_base_url_input.strip()
        other_gps = str(st.session_state.get("other_gps_input", "")).strip()
        if teacher_email and "@" not in teacher_email:
            st.error("老師電郵格式不正確。")
        elif other_gps and parse_gps_pair(other_gps) is None:
            st.error("其他地點 GPS 必須是緯度, 經度兩個數字。")
        else:
            save_settings(teacher_email, public_base)
            save_other_gps(other_gps)
            if public_base and ("localhost" in public_base or "127.0.0.1" in public_base):
                st.warning("已儲存，但這個公開網址是 localhost，手機打不開。請改用上面的區網網址。")
            else:
                st.success("已儲存老師電郵和公開網址。")


def render_attendance_board() -> None:
    try:
        attendance = load_attendance()
    except Exception:
        st.warning("出席表正在更新，請稍候。")
        return
    on_time = late = absent = 0
    if not attendance.empty:
        for status in attendance["status"].tolist():
            if status == STATUS_ON_TIME:
                on_time += 1
            elif status == STATUS_LATE:
                late += 1
            elif status == STATUS_ABSENT:
                absent += 1
    left, middle, right = st.columns(3)
    left.metric("準時出席", on_time)
    middle.metric("遲到", late)
    right.metric("缺席", absent)
    if attendance.empty:
        st.info("這一節還沒有人點名。")
        return
    st.dataframe(
        attendance,
        width="stretch",
        hide_index=True,
        column_config={
            "distance_meters": st.column_config.TextColumn("距離（米）"),
            "location_result": st.column_config.TextColumn("位置結果"),
            "campus_name": st.column_config.TextColumn("校園"),
            "可能不在校園": st.column_config.TextColumn("可能不在校園"),
            "map_url": st.column_config.LinkColumn("地圖", display_text="開啟地圖"),
        },
    )
    for row in attendance.to_dict(orient="records"):
        lat = str(row.get("latitude", "")).strip()
        lng = str(row.get("longitude", "")).strip()
        link = str(row.get("map_url", "")).strip()
        if not lat or not lng or not link:
            continue
        accuracy = str(row.get("accuracy_meters", "")).strip()
        accuracy_text = f"，約 {accuracy} 米" if accuracy else ""
        distance = str(row.get("distance_meters", "")).strip()
        location_result = str(row.get("location_result", "")).strip()
        campus_name = str(row.get("campus_name", "")).strip()
        outside = str(row.get("可能不在校園", "")).strip()
        distance_text = f"，距離 {distance} 米" if distance else ""
        result_text = f"，{location_result}" if location_result else ""
        campus_text = f"，{campus_name}" if campus_name else ""
        outside_text = "，可能不在校園" if outside == "是" else ""
        st.markdown(
            f"{row.get('student_name', '')}　{lat}, {lng}{accuracy_text}{distance_text}{result_text}{campus_text}{outside_text}　[地圖]({link})"
        )


def _consume_browser_gps() -> None:
    """Copy a top-level geolocation redirect into the current GPS box."""
    pair = parse_gps_pair(f"{_qp('current_lat')}, {_qp('current_lng')}")
    if pair is None:
        return
    st.session_state.current_gps = f"{format_coord(pair[0])}, {format_coord(pair[1])}"
    st.session_state.page = "teacher"
    for key in ("current_lat", "current_lng"):
        if key in st.query_params:
            del st.query_params[key]
    st.rerun()


def render_teacher() -> None:
    st.title("開始課堂")
    if st.button("返回主頁"):
        st.session_state.page = "landing"
        st.rerun()

    flash = st.session_state.pop("flash", "")
    if flash:
        st.success(flash)
    flash_level = st.session_state.pop("flash_level", "")
    flash_text = st.session_state.pop("flash_text", "")
    if flash_text:
        if flash_level == "warning":
            st.warning(flash_text)
        elif flash_level == "error":
            st.error(flash_text)
        else:
            st.success(flash_text)

    roster = load_roster()
    if roster.empty:
        st.warning("尚未上傳名冊，學生將無法完成點名。")
    else:
        st.caption(f"名冊 {len(roster)} 人，讀自 data/roster.csv。")

    session = load_session() or {}
    default_date = date.today()
    parsed_date = parse_date(session.get("class_date", "")) if session else None
    if parsed_date is not None:
        default_date = parsed_date
    suggested_start, suggested_end = suggested_times()
    default_start = parse_hhmm(session.get("start_time", "")) if session else suggested_start
    default_end = parse_hhmm(session.get("end_time", "")) if session else suggested_end
    if default_start is None:
        default_start = suggested_start
    if default_end is None:
        default_end = suggested_end

    with st.form("lesson"):
        class_date = st.date_input("課堂日期 *", value=default_date)
        start_col, end_col = st.columns(2)
        with start_col:
            start_time = st.time_input("上課時間 *", value=default_start, step=60)
        with end_col:
            end_time = st.time_input("下課時間 *", value=default_end, step=60)
        remarks = st.text_area("備註", value=session.get("remarks", ""))
        saved_campus = str(session.get("campus_choice") or session.get("campus_name") or "").strip()
        if saved_campus == CAMPUS_OTHERS_NAME:
            saved_campus = CAMPUS_OTHERS
        campus_index = CAMPUS_OPTIONS.index(saved_campus) if saved_campus in CAMPUS_OPTIONS else 0
        campus_label = st.radio("上課地點", CAMPUS_OPTIONS, index=campus_index)
        start_clicked = st.form_submit_button("開始", type="primary")

    if start_clicked:
        if end_time <= start_time:
            st.error("下課時間必須晚於上課時間。")
        elif campus_label == CAMPUS_OTHERS and load_other_gps() is None:
            st.error(OTHER_GPS_REQUIRED)
        else:
            start_lesson(class_date, start_time, end_time, remarks, campus_label)
            st.session_state.flash = "已開始課堂。已有的點名紀錄會保留。"
            st.rerun()

    saved = load_session()
    if not saved:
        st.info("按「開始」後會顯示學生用的 QR code。")
        return

    st.subheader("學生點名 QR")
    form_start = format_hhmm(start_time)
    form_end = format_hhmm(end_time)
    if (
        class_date.strftime("%Y-%m-%d") != saved["class_date"]
        or form_start != saved["start_time"]
        or form_end != saved["end_time"]
    ):
        st.warning("上面的時間已改，按「開始」後 QR 才會更新。")
    render_live_qr(saved["class_date"], saved["start_time"], saved["end_time"])
    if saved.get("campus_name"):
        st.caption(f"本節地點：{saved['campus_name']}")
    st.caption("上課時間或之前是準時出席，15 分鐘內是遲到，超過 15 分鐘是缺席。點名要開啟一次定位，不需拍照。")
    if saved.get("remarks"):
        st.caption(f"備註：{saved['remarks']}")

    st.subheader("出席")
    render_attendance_board()
    st.button("重新整理出席")

    st.subheader("結束課堂")
    if saved.get("report_sent"):
        sent_at = saved.get("report_sent_at") or ""
        st.success(f"報告已於 {sent_at} 發送，不會再寄一次。")
        return
    if end_prompt_needed(saved):
        st.warning("已過下課時間，請按「結束課堂並發送報告」寄出出席報告。")
    if st.button("結束課堂並發送報告"):
        with st.spinner("正在發送報告…"):
            result = finish_class()
        if result.get("email_sent"):
            st.session_state.flash_level = "success"
            st.session_state.flash_text = result["message"]
        else:
            st.session_state.flash_level = "warning"
            st.session_state.flash_text = result["message"]
        st.rerun()


def render_checkin_result(result: dict) -> None:
    if not result.get("ok"):
        st.error(result.get("message") or INVALID_INPUT)
        return
    if result.get("status"):
        st.write(f"出席狀態：{result['status']}")
    row = result.get("row") or {}
    if row.get("checkin_time"):
        st.caption(f"點名時間：{row['checkin_time']}")
    if str(row.get("可能不在校園", "")).strip() == "是":
        st.warning("可能不在校園")
    if "email_sent" not in result:
        return
    if result.get("email_sent"):
        st.success(THANK_YOU)
        return
    notice = result.get("warning") or STUDENT_EMAIL_FAILED
    if notice not in {STUDENT_EMAIL_FAILED, STUDENT_EMAIL_SKIPPED}:
        notice = STUDENT_EMAIL_FAILED
    st.warning(notice)


@st.fragment(run_every=timedelta(seconds=30))
def render_live_qr(class_date: str, start: str, end: str) -> None:
    origin = student_origin()
    if not origin.startswith("https://"):
        st.error("學生 QR 需要 HTTPS 網址。iPhone 在 http 區網不會提供定位。")
        return
    ticket = current_qr_token(class_date, start, end)
    url = build_student_url(origin, class_date, start, end, ticket["token"])
    st.image(make_qr_image(url))
    st.code(url, language=None)
    st.caption(f"學生網址：{origin}")


def _accept_student_entry(event: str, token: str, formatted_start: str, formatted_end: str) -> str:
    """Return the check-in grant, or an empty string when the QR is no longer valid."""
    class_date = parse_date(event)
    if class_date is None:
        return ""
    iso_date = class_date.isoformat()
    grant = str(st.session_state.get("qr_grant") or "")
    if st.session_state.get("claimed_token") == token and grant:
        return grant
    query_grant = _qp("grant")
    if query_grant and resume_qr_grant(token, query_grant, iso_date, formatted_start, formatted_end):
        st.session_state.claimed_token = token
        st.session_state.qr_grant = query_grant
        if st.session_state.get("verified_student") is None:
            saved = student_on_grant(token, query_grant)
            if saved is not None:
                st.session_state.verified_student = saved
        return query_grant
    granted = claim_qr_token(token, iso_date, formatted_start, formatted_end)
    if not granted:
        return ""
    st.session_state.claimed_token = token
    st.session_state.qr_grant = granted
    if _qp("grant") != granted:
        st.query_params["grant"] = granted
        st.rerun()
    return granted


def _show_locate_button(event: str, start: str, end: str, token: str, grant: str) -> None:
    href = html.escape(locate_page_url(event, start, end, token, grant), quote=True)
    st.markdown(f'<a class="locate-launch" href="{href}">允許定位</a>', unsafe_allow_html=True)


def _dismiss_location_dialog() -> None:
    if st.session_state.get("location_choice") != "open":
        st.session_state.location_choice = "cancel"


@st.dialog("現在開啟定位功能？", width="large", on_dismiss=_dismiss_location_dialog)
def _location_dialog() -> None:
    st.write("開啟後才會讀取一次定位。取消則停留在此頁，不會記錄出席。")
    if st.button("開啟", type="primary", key="location-open"):
        st.session_state.location_choice = "open"
        st.rerun()
    if st.button("取消", key="location-cancel"):
        st.session_state.location_choice = "cancel"
        st.rerun()


def _ask_before_location(event: str, start: str, end: str, token: str, grant: str) -> bool:
    """Ask before any location read. True when the student may continue to locate.html."""
    choice = st.session_state.get("location_choice")
    if choice == "open":
        _show_locate_button(event, start, end, token, grant)
        return True
    if choice != "cancel":
        _location_dialog()
        return False
    st.info("未開啟定位，出席尚未記錄。")
    if st.button("再開啟定位", type="primary"):
        st.session_state.location_choice = None
        st.rerun()
    return False


def render_student(event: str, start: str, end: str, token: str) -> None:
    st.title("課堂點名")
    class_date = parse_date(event)
    start_t = parse_hhmm(start)
    end_t = parse_hhmm(end)
    if class_date is None or start_t is None or end_t is None or not token:
        st.error(QR_INVALID)
        return
    formatted_start = format_hhmm(start_t)
    formatted_end = format_hhmm(end_t)
    grant = _accept_student_entry(event, token, formatted_start, formatted_end)
    if not grant:
        st.error(QR_INVALID)
        return
    session = load_session()
    if not session_matches(session, event, formatted_start, formatted_end):
        st.error("此課堂尚未開始，或連結與目前課堂不符。")
        return

    st.caption(f"{class_date.isoformat()}　{formatted_start}–{formatted_end}")
    if session and session.get("remarks"):
        st.caption(session["remarks"])

    if st.session_state.get("checkin_done"):
        render_checkin_result(st.session_state.get("checkin_result") or {"ok": True, "message": THANK_YOU})
        return

    if st.session_state.get("verified_student") is None:
        if st.session_state.get("identity_error"):
            st.error(st.session_state.identity_error)
        with st.form("identity"):
            email = st.text_input("學生電郵")
            number = st.text_input("學生編號")
            submitted = st.form_submit_button("確認")
        if submitted:
            identity = validate_identity(email, number)
            if not identity["ok"]:
                st.session_state.identity_error = identity["message"]
                st.session_state.verified_student = None
            elif checkin_too_soon(email, number) or checkin_too_soon(
                identity["student"]["student_email"], identity["student"]["student_number"]
            ):
                st.session_state.identity_error = TOO_SOON
                st.session_state.verified_student = None
            else:
                st.session_state.identity_error = ""
                st.session_state.verified_student = identity["student"]
                remember_student_on_grant(token, grant, identity["student"])
            st.rerun()
        return

    student = st.session_state.verified_student
    remember_student_on_grant(token, grant, student)
    if checkin_too_soon(student["student_email"], student["student_number"]):
        st.error(TOO_SOON)
        return
    st.write(f"{student['student_name']}　{student['student_number']}")
    if _qp("geo") == "denied":
        st.error(GPS_DENIED)
    fix = location_from_query()
    if isinstance(fix, dict) and fix.get("ok"):
        pass
    elif isinstance(fix, dict):
        st.error(GPS_REQUIRED)
        _show_locate_button(event, formatted_start, formatted_end, token, grant)
        return
    elif not _ask_before_location(event, formatted_start, formatted_end, token, grant):
        return
    else:
        return
    latitude = float(fix["latitude"])
    longitude = float(fix["longitude"])
    accuracy = float(fix["accuracy"])
    st.caption(f"已取得定位：{format_coord(latitude)}, {format_coord(longitude)}")
    if st.button("完成點名", type="primary"):
        result = record_checkin(
            student["student_email"],
            student["student_number"],
            session,
            latitude,
            longitude,
            accuracy,
        )
        st.session_state.checkin_result = result
        if result.get("ok"):
            st.session_state.checkin_done = True
            st.rerun()
        st.error(result.get("message") or INVALID_INPUT)


def main() -> None:
    st.set_page_config(page_title="課堂點名系統", page_icon="📋", layout="centered")
    inject_css()
    ensure_data_dir()
    if "page" not in st.session_state:
        st.session_state.page = "landing"
    _consume_browser_gps()
    query = student_query()
    if query is not None:
        render_student(*query)
        return
    page = st.session_state.page
    if page == "settings":
        render_settings()
    elif page == "teacher":
        render_teacher()
    else:
        render_landing()


if os.environ.get("ROLLS_CALL_SKIP_UI") != "1":
    main()
