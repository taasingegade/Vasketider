from flask import Flask, render_template, request, redirect, session, jsonify, Response, url_for, g, flash, send_from_directory
try:
    import psycopg  # psycopg v3
    from psycopg.errors import Error as PGError
    HAS_PG3 = True
except ImportError:
    import psycopg2 as psycopg  # fallback til v2 hvis lokalt
    from psycopg2 import Error as PGError
    HAS_PG3 = False
from datetime import datetime, timedelta, date
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from fpdf import FPDF
from pytz import timezone
from flask import make_response
from user_agents import parse as ua_parse
try:
    from psycopg.errors import UniqueViolation  # psycopg v3
except Exception:
    try:
        from psycopg2.errors import UniqueViolation  # psycopg2
    except Exception:
        UniqueViolation = None  # fallback
from flask import current_app
from functools import wraps
from flask import abort
import os
import secrets
import pytz
import smtplib, socket
import hashlib
import threading
import time
from email.mime.text import MIMEText
from twilio.rest import Client
from werkzeug.utils import secure_filename, safe_join

UPLOAD_FOLDER = 'static'
# disse køre systemet og styrer essentielle sikkerheder
app = Flask(__name__)
app.secret_key = 'hemmelig_nøgle'
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=int(os.getenv('REMEMBER_DAYS', '30')))
app.config.setdefault('SESSION_COOKIE_SAMESITE', 'Lax')
app.config.setdefault('SESSION_COOKIE_SECURE', True)  # Render kører HTTPS
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER

HA_WEBHOOK_SECRET = os.environ.get("VASKETID_WEBHOOK_SECRET", "")
SLOT_TO_START = {0: 7, 1: 11, 2: 15, 3: 19}
SLOTS = [(7,11),(11,15),(15,19),(19,23)]  # 4 blokke á 4 timer
#SLOTS = [(7,9),(9,11),(11,13),(13,15),(15,17),(17,19)(19,21),(21,23)] 8 blokke á 2 timer
LAZY_CLEANUP_MIN_INTERVAL = 300  # 5 min throttle for on-demand oprydning
_last_cleanup = {"ts": None}
IP_SALT = os.getenv("IP_SALT", "please-change-me")
def _first_existing(paths):
    for p in paths:
        if os.path.exists(p):
            return p 
    return None

ALLOWED_EXTENSIONS = {'pdf'}
CPH = timezone("Europe/Copenhagen")
UGEDAGE_DK = ['Mandag', 'Tirsdag', 'Onsdag', 'Torsdag', 'Fredag', 'Lørdag', 'Søndag']
DATABASE_URL = os.environ.get("DATABASE_URL") or "din_default_postgres_url"
DEBUG_NOTIF = True  # sæt til False for mindre logstøj
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DOCS_DIR = os.path.join(BASE_DIR, "static", "docs")
os.makedirs(DOCS_DIR, exist_ok=True)
limiter = Limiter(
    key_func=get_remote_address,
    default_limits=[]
)
limiter.init_app(app)

def _dump_slot_state(cur, dato, slot_txt):
    """Printer alle rækker for dato/slot, så vi kan se præcis hvad der blokerer."""
    cur.execute("""
        SELECT id, dato_rigtig, slot_index::text AS slot, COALESCE(sub_slot,'full') AS del,
               brugernavn, status, created_at
        FROM bookinger
        WHERE dato_rigtig=%s AND slot_index::text=%s
        ORDER BY COALESCE(sub_slot,'full'), id
    """, (dato, slot_txt))
    rows = cur.fetchall()
    print("🧾 SLOT-STATE:", {"dato": str(dato), "slot": slot_txt, "rows": rows})

def _friendly_half_conflict_reason(cur, dato, slot_txt, sub):
    """Returnér en menneskelig forklaring til UI efter en UniqueViolation."""
    # fuld blokkerer?
    cur.execute("""
        SELECT 1 FROM bookinger
        WHERE dato_rigtig=%s AND slot_index::text=%s
          AND COALESCE(sub_slot,'full')='full'
          AND brugernavn IS NOT NULL
        LIMIT 1
    """, (dato, slot_txt))
    if cur.fetchone():
        return "Slot er fuldt booket."

    # min halvdel taget?
    cur.execute("""
        SELECT brugernavn FROM bookinger
        WHERE dato_rigtig=%s AND slot_index::text=%s
          AND sub_slot=%s AND brugernavn IS NOT NULL
        LIMIT 1
    """, (dato, slot_txt, sub))
    r = cur.fetchone()
    if r:
        return f"Den valgte halvdel er allerede taget (af {r[0]})."

    # ellers ukendt
    return "Kunne ikke booke halvtid (DB-konflikt)."

# ====================================
# Definer starter en funktion i python
# ====================================

def get_db_connection():
    return psycopg.connect(DATABASE_URL, sslmode='require')

def init_db():
    def run(cur, conn, sql, params=None, label=""):
        try:
            cur.execute(sql, params or ())
            conn.commit()
        except Exception as e:
            conn.rollback()
            print(f"⚠️ {label or 'SQL'} fejlede:", e)

    try:
        conn = get_db_connection()
        cur  = conn.cursor()

        # ===== Miele-aktivitet =====
        run(cur, conn, """
            CREATE TABLE IF NOT EXISTS miele_activity (
                id SERIAL PRIMARY KEY,
                ts TIMESTAMP NOT NULL,
                status TEXT NOT NULL
            );
        """, label="create miele_activity")
        run(cur, conn, "CREATE INDEX IF NOT EXISTS idx_miele_activity_ts ON miele_activity(ts)",
            label="index miele_activity.ts")

        # ===== booking_log =====
        run(cur, conn, """
            CREATE TABLE IF NOT EXISTS booking_log (
                id SERIAL PRIMARY KEY,
                brugernavn  TEXT,
                handling    TEXT,     -- 'create','auto_remove','complete','fejl:max2', ...
                dato        DATE,
                slot_index  INT,
                booking_type TEXT,
                resultat    TEXT,
                tidspunkt   TIMESTAMP DEFAULT NOW()
            );
        """, label="create booking_log")
        run(cur, conn, """
            CREATE INDEX IF NOT EXISTS ix_booking_log_time
            ON booking_log(tidspunkt DESC);
        """, label="index booking_log.tidspunkt")

        # ===== booking_attempts =====
        run(cur, conn, """
            CREATE TABLE IF NOT EXISTS booking_attempts (
                id SERIAL PRIMARY KEY,
                ts TIMESTAMP DEFAULT NOW(),
                brugernavn TEXT,
                dato DATE,
                slot INT,
                status TEXT
            );
        """, label="create booking_attempts")

        # ===== login_log =====
        run(cur, conn, """
            CREATE TABLE IF NOT EXISTS login_log (
                id SERIAL PRIMARY KEY,
                brugernavn   TEXT,
                tidspunkt    TIMESTAMP DEFAULT NOW(),
                status       TEXT,
                ip           TEXT,
                enhed        TEXT,
                ua_browser   TEXT,
                ua_os        TEXT,
                ua_device    TEXT,
                ip_hash      TEXT,
                ip_country   TEXT,
                ip_region    TEXT,
                ip_city      TEXT,
                ip_org       TEXT,
                ip_is_datacenter BOOLEAN DEFAULT FALSE
            );
        """, label="create login_log")

        # ===== SCHEMA PATCHES: bookinger =====
        # NB: korrekt syntaks er "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS ..."
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS status TEXT DEFAULT 'booked'",
            label="bookinger.status")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS booking_type TEXT",
            label="bookinger.booking_type")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS sub_slot TEXT",
            label="bookinger.sub_slot")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS created_at TIMESTAMP DEFAULT NOW()",
            label="bookinger.created_at")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS start_ts TIMESTAMP",
            label="bookinger.start_ts")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS end_ts TIMESTAMP",
            label="bookinger.end_ts")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS activation_required BOOLEAN DEFAULT FALSE",
            label="bookinger.activation_required")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS activation_deadline TIMESTAMP",
            label="bookinger.activation_deadline")
        run(cur, conn, "ALTER TABLE bookinger ADD COLUMN IF NOT EXISTS activated_at TIMESTAMP",
            label="bookinger.activated_at")

        # ===== NYT: notificeringsfelter på brugere =====
        run(cur, conn, "ALTER TABLE brugere ADD COLUMN IF NOT EXISTS notif_email TEXT DEFAULT 'nej'",
            label="brugere.notif_email")
        run(cur, conn, "ALTER TABLE brugere ADD COLUMN IF NOT EXISTS notif_sms   TEXT DEFAULT 'nej'",
            label="brugere.notif_sms")

        # Migration fra gammel kolonne 'notifikation' -> sæt begge til 'ja' hvor den var 'ja'
        run(cur, conn, """
            DO $$
            BEGIN
                IF EXISTS (
                    SELECT 1
                    FROM information_schema.columns
                    WHERE table_name='brugere' AND column_name='notifikation'
                ) THEN
                    UPDATE brugere
                       SET notif_email = 'ja',
                           notif_sms   = 'ja'
                     WHERE COALESCE(notifikation,'nej') = 'ja';
                END IF;
            END $$;
        """, label="migrer notifikation -> notif_email/notif_sms")

        # ===== Ryd gamle brede constraints/indeks på (dato_rigtig, slot_index) =====
        # Drop constraints (hvis de eksisterer)
        run(cur, conn, "ALTER TABLE bookinger DROP CONSTRAINT IF EXISTS ux_bookinger_dato_slot",
            label="drop constraint ux_bookinger_dato_slot")
        run(cur, conn, "ALTER TABLE bookinger DROP CONSTRAINT IF EXISTS unique_booking",
            label="drop constraint unique_booking")
        run(cur, conn, "ALTER TABLE bookinger DROP CONSTRAINT IF EXISTS uniq_bookinger_dato_slot",
            label="drop constraint uniq_bookinger_dato_slot")
        # Drop indexes med samme navne (hvis de var oprettet som indeks)
        run(cur, conn, "DROP INDEX IF EXISTS ux_bookinger_dato_slot",
            label="drop index ux_bookinger_dato_slot")
        run(cur, conn, "DROP INDEX IF EXISTS unique_booking",
            label="drop index unique_booking")
        run(cur, conn, "DROP INDEX IF EXISTS uniq_bookinger_dato_slot",
            label="drop index uniq_bookinger_dato_slot")

        # ===== Partial unique indexes (full / early / late) =====
        run(cur, conn, """
            CREATE UNIQUE INDEX IF NOT EXISTS ux_bookinger_full
              ON bookinger (dato_rigtig, slot_index)
              WHERE COALESCE(sub_slot,'full') = 'full';
        """, label="create ux_bookinger_full")

        run(cur, conn, """
            CREATE UNIQUE INDEX IF NOT EXISTS ux_bookinger_early
              ON bookinger (dato_rigtig, slot_index)
              WHERE sub_slot = 'early';
        """, label="create ux_bookinger_early")

        run(cur, conn, """
            CREATE UNIQUE INDEX IF NOT EXISTS ux_bookinger_late
              ON bookinger (dato_rigtig, slot_index)
              WHERE sub_slot = 'late';
        """, label="create ux_bookinger_late")

        cur.close()
        conn.close()
        print("✅ DB-init færdig (schema + partial indexes OK)")
    except Exception as e:
        try:
            cur.close()
        except Exception:
            pass
        try:
            conn.close()
        except Exception:
            pass
        print("❌ DB-init fatalt:", e)

init_db()

# ==== BEGIN ADD: booking helpers ====

def get_client_ip(req):
    xff = req.headers.get("X-Forwarded-For", "")
    if xff:
        return xff.split(",")[0].strip()
    return req.remote_addr or "0.0.0.0"

def _hent_start_hours(conn):
    """
    Returnér dict {start_hour: slot_index}. Falder tilbage til standard 07/11/15/19,
    hvis vasketider-tabellen ikke findes/er tom.
    """
    mapping = {}
    try:
        with conn.cursor() as cur:
            cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
            rows = cur.fetchall()
            for idx, tekst in rows or []:
                # forventer tekst som "07–11" eller "07-11"
                t = (tekst or "").replace("–","-")
                sh = t.split("-")[0].strip()
                if sh.isdigit():
                    mapping[int(sh)] = int(idx)
    except Exception:
        pass
    if not mapping:
        mapping = {7:0, 11:1, 15:2, 19:3}
    return mapping

def hash_ip(ip: str) -> str:
    import hashlib
    return hashlib.sha256((ip or "").encode("utf-8")).hexdigest()

def parse_ua(user_agent: str):
    ua = ua_parse(user_agent or "")
    return {
        "browser": ua.browser.family or "",
        "os": ua.os.family or "",
        "device": "mobile" if ua.is_mobile else "tablet" if ua.is_tablet else "bot" if ua.is_bot else "desktop"
    }

def get_indstilling(cur, navn: str, default: str=""):
    cur.execute("SELECT vaerdi FROM indstillinger WHERE navn=%s", (navn,))
    row = cur.fetchone()
    return row[0] if row and row[0] is not None else default

SLOT_WINDOWS = {0:(7,11), 1:(11,15), 2:(15,19), 3:(19,23)}

def slot_interval(dato_any, slot_index: int):
    """
    Returnér (start_dt, end_dt) i DK-tid for dato + slot (4 timer).
    Accepterer både datetime.date/datetime og 'YYYY-MM-DD' string.
    """
    if isinstance(dato_any, (date, datetime)):
        y, m, d = dato_any.year, dato_any.month, dato_any.day
    else:
        y, m, d = map(int, str(dato_any).split("-"))

    sh, eh = SLOT_WINDOWS[int(slot_index)]
    start_dt = CPH.localize(datetime(y, m, d, sh, 0, 0))
    end_dt   = CPH.localize(datetime(y, m, d, eh, 0, 0))
    return start_dt, end_dt

def miele_var_aktiv_omkring(cur, t0, t1) -> bool:
    cur.execute("SELECT 1 FROM miele_activity WHERE ts BETWEEN %s AND %s LIMIT 1", (t0, t1))
    return cur.fetchone() is not None

def registrer_kæde_hvis_nødvendigt(conn, dato_any, bruger_slot: int, brugernavn: str):
    """
    Accepterer både datetime.date og 'YYYY-MM-DD' string som dato.
    """
    if brugernavn.lower() in ("direkte", "service"):
        return

    # Sikr at vi altid har et date-objekt til SQL
    if isinstance(dato_any, (date, datetime)):
        dato_db = dato_any if isinstance(dato_any, date) else dato_any.date()
    else:
        dato_db = datetime.strptime(str(dato_any), "%Y-%m-%d").date()

    cur = conn.cursor()
    try:
        # indstillinger med defaults
        cur.execute("SELECT COALESCE((SELECT vaerdi FROM indstillinger WHERE navn='kæde_vindue_min'),'30')")
        vindue_min = int(cur.fetchone()[0])
        cur.execute("SELECT COALESCE((SELECT vaerdi FROM indstillinger WHERE navn='kæde_kræv_miele'),'nej')")
        kræv_miele = cur.fetchone()[0].lower() == 'ja'
        cur.execute("SELECT COALESCE((SELECT vaerdi FROM indstillinger WHERE navn='kæde_miele_margin_min'),'15')")
        miele_margin = int(cur.fetchone()[0])

        prev_slot = bruger_slot - 1
        if prev_slot < 0:
            return

        cur.execute("""
          SELECT 1 FROM bookinger
          WHERE dato_rigtig = %s AND slot_index = %s AND LOWER(brugernavn)='direkte'
          LIMIT 1
        """, (dato_db, prev_slot))
        if not cur.fetchone():
            return

        # beregn slut af direkte-slot
        _, direkte_slut = slot_start_end(dato_db, prev_slot)
        nu = datetime.now(CPH)
        if nu > direkte_slut + timedelta(minutes=vindue_min):
            return

        miele_note = "miele ikke krævet"
        miele_score = 0
        if kræv_miele:
            t0 = direkte_slut - timedelta(minutes=miele_margin)
            t1 = direkte_slut + timedelta(minutes=miele_margin)
            if not miele_var_aktiv_omkring(cur, t0, t1):
                return
            miele_note = f"miele aktiv ±{miele_margin}m"
            miele_score = 30

        diff_min = max(0, int((nu - direkte_slut).total_seconds() // 60))
        base = max(0, 70 - diff_min*2)  # 0..70
        score = min(100, base + miele_score)
        note = f"t+{diff_min}m; {miele_note}"

        cur.execute("""
          INSERT INTO direkte_kæder (dato, direkte_slot, bruger_slot, bruger, score, note)
          VALUES (%s,%s,%s,%s,%s,%s)
        """, (dato_db, prev_slot, bruger_slot, brugernavn, score, note))
        conn.commit()
    finally:
        cur.close()

def log_booking_attempt(cur, bruger, dato, slot, status):
    cur.execute(
        "INSERT INTO booking_attempts (brugernavn, dato, slot, status) VALUES (%s,%s,%s,%s)",
        (bruger, dato, slot, status)
    )

def _parse_dato_any(dato_str: str):
    """
    Robust dato-parser: prøver 'DD-MM-YYYY' og 'YYYY-MM-DD'.
    Returnerer naive UTC datetime (kl 00:00) – bruges kun til at bygge start_ts/end_ts.
    """
    for fmt in ("%d-%m-%Y", "%Y-%m-%d"):
        try:
            d = datetime.strptime(dato_str, fmt)
            return d
        except ValueError:
            continue
    raise ValueError(f"Ukendt datoformat: {dato_str}")

def _to_utc_naive(local_dt: datetime):
    """Local (Europe/Copenhagen) -> UTC naive (no tzinfo)."""
    return CPH.localize(local_dt).astimezone(pytz.UTC).replace(tzinfo=None)

def dt_from_dato(dato_str, h, m=0):
    d = _parse_dato_any(dato_str)
    local_dt = datetime(d.year, d.month, d.day, h, m)
    return _to_utc_naive(local_dt)

def compute_interval(dato, slot, booking_type, now_utc=None):
    sh, eh = SLOTS[slot]
    if booking_type == 'split_before':
        start, end = dt_from_dato(dato, sh, 0), dt_from_dato(dato, sh+2, 0)
    elif booking_type == 'split_after':
        start, end = dt_from_dato(dato, sh+2, 0), dt_from_dato(dato, eh, 0)
    else:  # 'full' eller 'direkte'
        start, end = dt_from_dato(dato, sh, 0), dt_from_dato(dato, eh, 0)
        if booking_type == 'direkte' and now_utc and start < now_utc < end:
            start = now_utc  # kiosk oprettes midt i slot => start = nu
    return start, end

def can_book(conn, dato, slot, bruger, booking_type):
    cur = conn.cursor()
    # 1) Loft: max 2 bookinger pr. dag (booked/active)
    cur.execute("""
      SELECT COUNT(*)
        FROM bookinger
       WHERE brugernavn=%s
         AND dato_rigtig=%s
         AND status IN ('booked','active')
    """, (bruger, dato))
    if cur.fetchone()[0] >= 2:
        return False, 'fejl:max2'

    # 2) Eksisterende i samme slot
    cur.execute("""
      SELECT booking_type
        FROM bookinger
       WHERE dato_rigtig=%s AND slot_index=%s
         AND status IN ('booked','active')
    """, (dato, slot))
    types = [r[0] for r in cur.fetchall()]

    if booking_type == 'direkte':
        if types:
            return False, 'fejl:optaget'
        return True, 'ok'

    # web-typer blokeres af direkte/full
    if any(t in ('direkte','full') for t in types):
        return False, 'fejl:optaget'
    if booking_type == 'split_before' and 'split_before' in types:
        return False, 'fejl:overlap'
    if booking_type == 'split_after' and 'split_after' in types:
        return False, 'fejl:overlap'

    # 3) Anti-seriebooking (valgfri – simple check, samme dag >=2 i forvejen)
    cur.execute("""
      SELECT COUNT(*)
        FROM bookinger
       WHERE brugernavn=%s AND dato_rigtig=%s
         AND status IN ('booked','active')
    """, (bruger, dato))
    if cur.fetchone()[0] >= 2:
        return False, 'fejl:seriebooking'

    return True, 'ok'

def create_booking(conn, bruger, dato, slot, booking_type, now_utc=None):
    ok, why = can_book(conn, dato, slot, bruger, booking_type)
    if not ok:
        return None, why
    start_ts, end_ts = compute_interval(dato, slot, booking_type, now_utc=now_utc or datetime.utcnow())
    cur = conn.cursor()
    cur.execute("""
        INSERT INTO bookinger (brugernavn, dato_rigtig, slot_index, booking_type, start_ts, end_ts, status)
        VALUES (%s,%s,%s,%s,%s,%s,'booked')
        RETURNING id
    """, (bruger, dato, slot, booking_type, start_ts, end_ts))
    bid = cur.fetchone()[0]
    cur.execute("""
        INSERT INTO booking_log (brugernavn, handling, dato, slot_index, booking_type, resultat)
        VALUES (%s,'create',%s,%s,%s,'ok')
    """, (bruger, dato, slot, booking_type))
    conn.commit()
    return bid, 'ok'

def find_current_booking(conn, now_utc):
    cur = conn.cursor()
    cur.execute("""
      SELECT id, booking_type, status
        FROM bookinger
       WHERE start_ts <= %s AND end_ts >= %s
         AND status IN ('booked','active')
       ORDER BY (booking_type='direkte') DESC, id ASC
       LIMIT 1
    """, (now_utc, now_utc))
    return cur.fetchone()  # (id, booking_type, status) or None

def lazy_cleanup(conn, now_utc=None):
    """
    On-demand oprydning (ingen cron):
      1) Auto-fjern web-bookinger (status='booked') der ikke er aktiveret 30 min efter start_ts (gælder ikke 'direkte').
      2) Markér bookinger som 'completed' når end_ts er passeret.
    """
    cur = conn.cursor()
    now = now_utc or datetime.utcnow()

    # 1) no-activation -> auto_removed (ikke direkte)
    cur.execute("""
        UPDATE bookinger
           SET status = 'auto_removed'
         WHERE status = 'booked'
           AND booking_type <> 'direkte'
           AND start_ts IS NOT NULL
           AND start_ts + INTERVAL '30 minutes' <= %s
           AND activated_at IS NULL
        RETURNING id
    """, (now,))
    removed_ids = [r[0] for r in cur.fetchall()] if cur.rowcount else []

    # 2) afslut efter end_ts
    cur.execute("""
        UPDATE bookinger
           SET status = 'completed'
         WHERE status IN ('booked','active')
           AND end_ts IS NOT NULL
           AND end_ts <= %s
        RETURNING id
    """, (now,))
    completed_ids = [r[0] for r in cur.fetchall()] if cur.rowcount else []

    # log
    if removed_ids:
        cur.executemany(
            "INSERT INTO booking_log (brugernavn, handling, dato, slot, booking_type, resultat) "
            "SELECT brugernavn, 'auto_remove', dato_rigtig, slot_index, booking_type, 'ok' FROM bookinger WHERE id=%s",
            [(bid,) for bid in removed_ids]
        )
    if completed_ids:
        cur.executemany(
            "INSERT INTO booking_log (brugernavn, handling, dato, slot, booking_type, resultat) "
            "SELECT brugernavn, 'complete', dato_rigtig, slot_index, booking_type, 'ok' FROM bookinger WHERE id=%s",
            [(bid,) for bid in completed_ids]
        )
    conn.commit()

# ==== END ADD ====

def log_login_privacy(cur, request, brugernavn: str, status: str):
    ip_raw = request.headers.get("X-Forwarded-For", request.remote_addr or "")
    ua_raw = request.headers.get("User-Agent", "")
    ua = ua_parse(ua_raw or "")

    _ua = {
        "browser": f"{ua.browser.family} {ua.browser.version_string}".strip(),
        "os": f"{ua.os.family} {ua.os.version_string}".strip(),
        "device": (ua.device.family or "Unknown").strip(),
    }

    # GEO ER FJERNET → vi sætter tomme defaults
    ip_country = ""
    ip_region = ""
    ip_city = ""
    ip_org = ""
    ip_is_dc = False

    # Vær sikker på at SQL og værdier matcher 1:1 (ingen geo-lookup!)
    cur.execute("""
        INSERT INTO login_log (
            brugernavn, tidspunkt, status,
            ip, enhed,
            ua_browser, ua_os, ua_device,
            ip_hash, ip_country, ip_region, ip_city, ip_org, ip_is_datacenter
        )
        VALUES (%s, NOW(), %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
    """, (
        brugernavn, status,
        ip_raw, ua_raw,
        _ua["browser"], _ua["os"], _ua["device"],
        hash_ip(ip_raw), ip_country, ip_region, ip_city, ip_org, ip_is_dc
    ))

def tilladt_fil(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

def generer_token(brugernavn):
    hemmelig_nøgle = "min_vasketid_nøgle"
    return hashlib.sha256((brugernavn + hemmelig_nøgle).encode()).hexdigest()

def latin1_sikker_tekst(tekst):
    if tekst is None:
        return ""
    return (
        tekst
        .replace("–", "-")
        .replace("✓", "JA")
        .replace("✗", "NEJ")
        .replace("æ", "ae")
        .replace("ø", "oe")
        .replace("å", "aa")
    )

def is_admin() -> bool:
    return session.get('brugernavn', '').lower() == 'admin'

def kræv_direkte_login(f):
    @wraps(f)
    def wrapper(*args, **kwargs):
        if session.get("brugernavn") != "direkte":
            return abort(403)
        return f(*args, **kwargs)
    return wrapper

def set_miele_status(status):
    """Oversæt Miele status fra HA til korte danske ord (ingen DB-skrivning her)."""
    s = (status or "").strip().lower().replace("_", " ")
    mapping = {
        "off":"Slukket","idle":"Klar","power off":"Strøm Slukket","standby":"afventer","not running":"ikke Klar","not connected":"Ikke forbundet",
        "in use":"I brug","running":"kørende","washing":"vask","main wash":"hovedvask","autocleaning":"Selvrens",
        "finished":"Færdig","finish":"Færdig","end":"Slut","program ended":"Program Færdig",
        "pause":"Pause","program interrupted":"Program Afbrudt",
        "programmed":"Klar til start","on":"Tændt","waiting to start":"Venter på start",
        "unavailable":"Ikke tilgænglig","failure":"Fejl","error":"Fejl","fejl":"Fejl",
        "rinse hold":"Skyl stop","service":"Service","supercooling":"Superkøling","superheating":"Superopvarmning",
        "superfreezing":"Superfrysning","supercooling superfreezing":"Superkøling/frysning"
    }
    return mapping.get(s, "Ukendt")

def _current_slot_index(now_dt):
    """Returnér slot_index (0..3) for nu, baseret på faste tidsrum DK-tid."""
    h = now_dt.hour
    # 07–11 = 0, 11–15 = 1, 15–19 = 2, 19–23 = 3
    if 7 <= h < 11:  return 0
    if 11 <= h < 15: return 1
    if 15 <= h < 19: return 2
    if 19 <= h < 23: return 3
    return None  # Uden for vasketider → ikke tilladt

def slot_start_end(dato_any, slot_index: int):
    """
    Returnér (start_dt, end_dt) i DK-tid for dato + slot (4 timer).
    Accepterer både datetime.date/datetime og 'YYYY-MM-DD' string.
    """
    if isinstance(dato_any, (date, datetime)):
        y, m, d = dato_any.year, dato_any.month, dato_any.day
    else:
        y, m, d = map(int, str(dato_any).split("-"))

    start_hour = SLOT_TO_START.get(int(slot_index))
    if start_hour is None:
        return None, None

    start_dt = CPH.localize(datetime(y, m, d, start_hour, 0, 0))
    end_dt   = start_dt + timedelta(hours=4)
    return start_dt, end_dt

def uge_for(dato_iso, valgt_uge):
    if valgt_uge and str(valgt_uge).isdigit():
        return int(valgt_uge)
    try:
        return datetime.strptime(dato_iso, "%Y-%m-%d").isocalendar().week
    except Exception:
        return datetime.today().isocalendar().week

def _dbg(msg: str):
    if DEBUG_NOTIF:
        print(msg, flush=True)

def send_email(modtager: str, emne: str, besked: str) -> bool:
    """
    Bruger Gmail SMTP.
    Kræver ENV:
      SMTP_USER = din Gmail (fx "vasketider.dk@gmail.com")
      SMTP_PASS = Gmail App Password (16 tegn) – ikke din normale kode.
    'From' SKAL være den samme som SMTP_USER.
    """
    afsender = (os.environ.get("SMTP_USER") or "").strip()
    adgangskode = (os.environ.get("SMTP_PASS") or "").strip()

    _dbg(f"🧩 send_email(): SMTP_USER set={bool(afsender)} | SMTP_PASS set={bool(adgangskode)} | to='{modtager}' | subject='{emne}'")

    if not afsender or not adgangskode:
        print("❌ send_email: Mangler SMTP_USER/SMTP_PASS i environment.", flush=True)
        return False

    # Byg mail
    msg = MIMEText(besked or "", "plain", "utf-8")
    msg["Subject"] = emne or ""
    msg["From"] = f"NO-REPLY Vasketider<{afsender}>"   # SKAL matche SMTP_USER
    msg["To"] = modtager
    msg.add_header("Reply-To", "noreply@vasketider.dk")

    # DNS-check
    try:
        socket.gethostbyname("smtp.gmail.com")
    except Exception as e:
        print("❌ DNS lookup fejlede for smtp.gmail.com:", e, flush=True)
        return False

    # 1) SSL/465
    try:
        _dbg("… prøver SMTP_SSL(465)")
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=20) as server:
            if DEBUG_NOTIF: server.set_debuglevel(1)
            server.login(afsender, adgangskode)
            server.sendmail(afsender, [modtager], msg.as_string())
        print(f"📧 (SSL) sendt til {modtager} – {emne}", flush=True)
        return True
    except smtplib.SMTPAuthenticationError as e:
        print("❌ Auth-fejl (SSL). Tjek App Password/2FA:", e, flush=True)
        return False
    except Exception as e:
        print("⚠️ SSL fejlede, prøver STARTTLS…", repr(e), flush=True)

    # 2) STARTTLS/587
    try:
        _dbg("… prøver SMTP(587)+STARTTLS")
        with smtplib.SMTP("smtp.gmail.com", 587, timeout=20) as server:
            if DEBUG_NOTIF: server.set_debuglevel(1)
            server.ehlo(); server.starttls(); server.ehlo()
            server.login(afsender, adgangskode)
            server.sendmail(afsender, [modtager], msg.as_string())
        print(f"📧 (TLS) sendt til {modtager} – {emne}", flush=True)
        return True
    except smtplib.SMTPAuthenticationError as e:
        print("❌ Auth-fejl (TLS). Tjek App Password:", e, flush=True)
    except Exception as e:
        print("❌ Fejl ved afsendelse (TLS):", repr(e), flush=True)
    return False

def send_sms_twilio(modtager, besked):
    account_sid = os.environ.get("Twilio_SID")
    auth_token = os.environ.get("Twilio_token")
    afsender_nummer = "+16209822117"

    if not all([account_sid, auth_token, afsender_nummer]):
        print("Twilio mangler data.")
        return

    try:
        client = Client(account_sid, auth_token)
        message = client.messages.create(
            body=besked,
            from_=afsender_nummer,
            to=modtager
        )
        print("SMS sendt:", message.sid)
    except Exception as e:
        print("Twilio fejl:", e)

def _truthy(v):
    if v is None:
        return False
    return str(v).strip().lower() in ("1","true","on","yes","ja","t","y","checked")

def ensure_stat_support_tables(cur):
    # Kun små hjælpe-tabeller; vi ændrer ikke dine primære tabeller.
    cur.execute("""
        CREATE TABLE IF NOT EXISTS statistik (
            dato DATE NOT NULL,
            type TEXT NOT NULL,
            antal INT DEFAULT 0,
            PRIMARY KEY (dato, type)
        )
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS booking_attempts (
            id SERIAL PRIMARY KEY,
            ts TIMESTAMP DEFAULT NOW(),
            brugernavn TEXT,
            dato DATE,
            slot INT,
            status TEXT
        )
    """)
    cur.execute("""
        CREATE TABLE IF NOT EXISTS direkte_kæder (
            id SERIAL PRIMARY KEY,
            dato DATE NOT NULL,
            direkte_slot INT NOT NULL,
            bruger_slot INT NOT NULL,
            bruger TEXT NOT NULL,
            score INT DEFAULT 0,
            note TEXT,
            created_at TIMESTAMP DEFAULT NOW()
        )
    """)

def ensure_user_columns(cur):
    # Safe at køre – opretter manglende felter i brugere
    cur.execute("""
    DO $$
    BEGIN
      IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='brugere' AND column_name='email') THEN
        ALTER TABLE brugere ADD COLUMN email TEXT;
      END IF;
      IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='brugere' AND column_name='sms') THEN
        ALTER TABLE brugere ADD COLUMN sms TEXT;
      END IF;
      IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='brugere' AND column_name='godkendt') THEN
        ALTER TABLE brugere ADD COLUMN godkendt BOOLEAN DEFAULT TRUE;
      END IF;
      -- bevar dit gamle 'notifikation' samlet felt
      IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='brugere' AND column_name='notifikation') THEN
        ALTER TABLE brugere ADD COLUMN notifikation TEXT DEFAULT 'ja';
      END IF;
      -- kanal flags lagres som 'ja'/'nej' (bagudskompatibelt)
      IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='brugere' AND column_name='notif_email') THEN
        ALTER TABLE brugere ADD COLUMN notif_email TEXT DEFAULT 'ja';
      END IF;
      IF NOT EXISTS (SELECT 1 FROM information_schema.columns WHERE table_name='brugere' AND column_name='notif_sms') THEN
        ALTER TABLE brugere ADD COLUMN notif_sms TEXT DEFAULT 'nej';
      END IF;
    END$$;
    """)

def _ja_nej(b):
    return 'ja' if bool(b) else 'nej'

def _normalize_dk_sms(s: str) -> str:
    s = (s or "").strip()
    # tillad "12 34 56 78" -> +4512345678
    only_digits = "".join(ch for ch in s if ch.isdigit() or ch == '+')
    if not only_digits:
        return ""
    if only_digits.startswith('+'):
        return only_digits
    # Hvis 8-cifret DK-nummer, prepender vi +45
    if len(only_digits) == 8:
        return "+45" + only_digits
    # fallback: returnér som er
    return only_digits

def get_kontaktinfo(cur, brugernavn: str):
    """
    Returnerer: (email, sms, allow_email_bool, allow_sms_bool)
    - virker både med ny og gammel skema
    """
    try:
        # ny model med notif_email/notif_sms
        cur.execute("""
            SELECT
                COALESCE(email,''), COALESCE(sms,''),
                COALESCE(notifikation,'ja'),
                COALESCE(notif_email,'ja'), COALESCE(notif_sms,'nej')
            FROM brugere
            WHERE LOWER(brugernavn)=LOWER(%s)
            LIMIT 1
        """, (brugernavn,))
        row = cur.fetchone()
        if not row:
            return "", "", False, False
        email, sms, notifikation, notif_email, notif_sms = row
        allow_email = (notifikation == 'ja') and (notif_email == 'ja')
        allow_sms   = (notifikation == 'ja') and (notif_sms   == 'ja')
        print(f"[get_kontaktinfo] {brugernavn} -> email='{email}', sms='{sms}', allow_email={allow_email}, allow_sms={allow_sms} (NY)")
        return email, sms, allow_email, allow_sms
    except Exception as e:
        # fallback til gammel model (kun 'notifikation')
        cur.execute("""
            SELECT COALESCE(email,''), COALESCE(sms,''), COALESCE(notifikation,'ja')
            FROM brugere
            WHERE LOWER(brugernavn)=LOWER(%s)
            LIMIT 1
        """, (brugernavn,))
        row = cur.fetchone()
        if not row:
            return "", "", False, False
        email, sms, notifikation = row
        allow = (notifikation == 'ja')
        print(f"[get_kontaktinfo] {brugernavn} -> email='{email}', sms='{sms}', allow_email={allow}, allow_sms={allow} (GAMMEL)")
        return email, sms, allow, allow

def get_slot_text(cur, slot_index: int) -> str:
    """Returner human tekst for et slot (falder tilbage til 07–11 ..)."""
    try:
        cur.execute("SELECT tekst FROM vasketider WHERE slot_index=%s", (int(slot_index),))
        r = cur.fetchone()
        if r and r[0]:
            return r[0]
    except Exception:
        pass
    defaults = {0:"07–11", 1:"11–15", 2:"15–19", 3:"19–23"}
    return defaults.get(int(slot_index), f"Slot {slot_index}")

def send_booking_notice(brugernavn: str, dato, slot_index: int, sub_slot: str | None, action: str):
    """
    Slår selv kontaktinfo op i DB og sender mail/SMS ud fra hvad brugeren har afkrydset.
    - Hvis kolonnerne 'notif_email' / 'notif_sms' findes, bruges de.
    - Ellers falder den tilbage til kolonnen 'notifikation' (ja/nej).
    action = 'booked' eller 'cancelled'
    """
    conn = None
    try:
        conn = get_db_connection()
        with conn.cursor() as c:
            # Hent kontaktindstillinger
            c.execute("""
                SELECT
                  email,
                  sms,
                  -- Brug specifikke flags hvis de findes, ellers fallback til 'notifikation'
                  COALESCE( (SELECT CASE WHEN EXISTS (
                      SELECT 1 FROM information_schema.columns
                      WHERE table_name='brugere' AND column_name='notif_email'
                  ) THEN CASE WHEN notif_email='ja' THEN 'ja' ELSE 'nej' END END),
                  CASE WHEN notifikation='ja' THEN 'ja' ELSE 'nej' END
                  ) AS use_email,
                  COALESCE( (SELECT CASE WHEN EXISTS (
                      SELECT 1 FROM information_schema.columns
                      WHERE table_name='brugere' AND column_name='notif_sms'
                  ) THEN CASE WHEN notif_sms='ja' THEN 'ja' ELSE 'nej' END END),
                  CASE WHEN notifikation='ja' THEN 'ja' ELSE 'nej' END
                  ) AS use_sms
                FROM brugere
                WHERE LOWER(brugernavn)=LOWER(%s)
                LIMIT 1
            """, (brugernavn,))
            row = c.fetchone()
            if not row:
                print(f"ℹ️ send_booking_notice: bruger ikke fundet: {brugernavn}", flush=True)
                return
            email, sms, use_email, use_sms = row

            # Slot-tekst (fallback hvis tabellen ikke findes eller der ikke er match)
            slot_txt = None
            try:
                c.execute("SELECT tekst FROM vasketider WHERE slot_index=%s", (int(slot_index),))
                r2 = c.fetchone()
                slot_txt = (r2[0] if r2 and r2[0] else None)
            except Exception:
                pass
            if not slot_txt:
                # fallback: vis tid i format "07–11" baseret på din slot_start_end helper
                try:
                    start_dt, end_dt = slot_start_end(dato, int(slot_index))
                    slot_txt = f"{start_dt.strftime('%H')}-{end_dt.strftime('%H')}"
                except Exception:
                    slot_txt = f"Slot {slot_index}"

    except Exception as e:
        print("❌ send_booking_notice: DB-fejl:", e, flush=True)
        try:
            if conn: conn.close()
        except Exception:
            pass
        return
    finally:
        try:
            if conn: conn.close()
        except Exception:
            pass

    # Nu bygger vi beskederne
    dato_dk = dato.strftime('%d-%m-%Y')
    del_txt = " (tidlig halvdel)" if sub_slot == "early" else " (sen halvdel)" if sub_slot == "late" else ""

    if action == "booked":
        subject = "Bekræftelse: vasketid booket"
        body    = f"Hej {brugernavn}\nDin vasketid er booket {dato_dk} {slot_txt}{del_txt}.\n— Hilsen Vasketidssystemet"
        sms_txt = f"Vasketid bekræftet {dato_dk} {slot_txt}{del_txt}"
    elif action == "cancelled":
        subject = "Aflysning: vasketid"
        body    = f"Hej {brugernavn}\nDin vasketid er aflyst {dato_dk} {slot_txt}{del_txt}.\n— Hilsen Vasketidssystemet"
        sms_txt = f"Vasketid aflyst {dato_dk} {slot_txt}{del_txt}"
    else:
        print(f"⚠️ send_booking_notice: ukendt action='{action}'", flush=True)
        return

    _dbg(f"🧩 DEBUG send_booking_notice: user='{brugernavn}' | date={dato_dk} | slot={slot_index} | sub={sub_slot} | action={action} | email='{email}' | sms='{sms}' | use_email={use_email} | use_sms={use_sms} | slot_txt='{slot_txt}'")

    sent_any = False

    # E-MAIL
    if (use_email or "").lower() == "ja":
        if email:
            try:
                ok = send_email(email, subject, body)
                if ok:
                    print(f"📧 Mail sendt til {email} – {subject}", flush=True)
                    sent_any = True
                else:
                    print(f"❌ send_email returnerede False for {email} – {subject}", flush=True)
            except Exception as e:
                print(f"❌ Exception ved send_email til {email}: {e}", flush=True)
        else:
            print(f"ℹ️ Ingen e-mail registreret for '{brugernavn}' (skulle sende).", flush=True)
    else:
        _dbg(f"… e-mail er fravalgt for '{brugernavn}' (use_email!=ja)")

    # SMS
    if (use_sms or "").lower() == "ja":
        if sms:
            try:
                send_sms_twilio(sms, sms_txt)
                print(f"📱 SMS sendt til {sms}", flush=True)
                sent_any = True
            except Exception as e:
                print(f"⚠️ SMS-fejl til {sms}: {e}", flush=True)
        else:
            print(f"ℹ️ Ingen SMS registreret for '{brugernavn}' (skulle sende).", flush=True)
    else:
        _dbg(f"… SMS er fravalgt for '{brugernavn}' (use_sms!=ja)")

    if not sent_any:
        print(f"⚠️ Intet blev sendt for '{brugernavn}' – ingen gyldige/valgte kontaktmetoder.", flush=True)

def hent_slot_status_for_dag(cur, dato):
    """
    Returnerer dict {slot_index: {
        "fulls": int, "early_taken": bool, "late_taken": bool,
        "available_full": bool, "available_early": bool, "available_late": bool,
        "slot_tekst": str
    }}
    """
    # Hent optællinger pr. slot
    cur.execute("""
        SELECT
          CAST(slot_index AS INT) AS sidx,
          SUM(CASE WHEN COALESCE(sub_slot,'full')='full' AND brugernavn IS NOT NULL THEN 1 ELSE 0 END) AS fulls,
          BOOL_OR(sub_slot='early' AND brugernavn IS NOT NULL) AS early_taken,
          BOOL_OR(sub_slot='late'  AND brugernavn IS NOT NULL) AS late_taken
        FROM bookinger
        WHERE dato_rigtig = %s
        GROUP BY CAST(slot_index AS INT)
        ORDER BY CAST(slot_index AS INT)
    """, (dato,))

    rows = cur.fetchall()
    status = {i: {"fulls":0,"early_taken":False,"late_taken":False} for i in (0,1,2,3)}
    for sidx, fulls, early_taken, late_taken in rows:
        status[sidx] = {
            "fulls": fulls or 0,
            "early_taken": bool(early_taken),
            "late_taken":  bool(late_taken),
        }

    # Hent visningstekster for alle slots
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    labels = {int(s): t for (s, t) in cur.fetchall() or []}

    # Afled tilgængelighed + tekst
    for i, st in status.items():
        st["slot_tekst"] = labels.get(i, f"Slot {i}")
        fully_booked = (st["fulls"] > 0) or (st["early_taken"] and st["late_taken"])
        st["available_full"]  = not fully_booked
        st["available_early"] = (not fully_booked) and (not st["early_taken"])
        st["available_late"]  = (not fully_booked) and (not st["late_taken"])
    return status

def hash_kode(plain: str) -> str:
    return hashlib.sha256(plain.encode('utf-8')).hexdigest()  # brug samme hash som resten af systemet

def ryd_gamle_bookinger_job():
    from pytz import timezone
    TZ = timezone("Europe/Copenhagen")
    while True:
        nu = datetime.now(TZ)
        # næste kørsel 03:00 i morgen (lokal tid)
        næste = (nu + timedelta(days=1)).replace(hour=3, minute=0, second=0, microsecond=0)
        time.sleep(max(1, int((næste - nu).total_seconds())))

        try:
            start_af_uge = datetime.now(TZ).date() - timedelta(days=datetime.now(TZ).weekday())
            conn = get_db_connection()
            cur = conn.cursor()
            cur.execute("DELETE FROM bookinger WHERE dato_rigtig < %s", (start_af_uge,))
            conn.commit()
            conn.close()
            print("✅ Ryddede gamle bookinger (før uge-start)")
        except Exception as e:
            print("❌ Fejl i ryd_gamle_bookinger_job:", e)
            time.sleep(60)

def db_exec(cur, sql, params=None, label=""):
    """Kør SQL og log præcist hvor det fejler, hvis noget går galt."""
    try:
        cur.execute(sql, params or ())
    except psycopg2.Error as e:
        current_app.logger.error(
            "DB-fejl ved %s: %s | %s | params=%r",
            label or "SQL",
            getattr(e, 'pgcode', ''), getattr(e, 'pgerror', ''), params
        )
        raise

def _naeste_tick_2t_window(now_local):
    hours = [6, 8, 10, 12, 14, 16, 18]
    base = now_local.replace(minute=0, second=0, microsecond=0)
    for h in hours:
        cand = base.replace(hour=h)
        if cand > now_local:
            return cand
    return (base + timedelta(days=1)).replace(hour=hours[0])

def require_admin():
    return 'brugernavn' in session and session['brugernavn'].lower() == 'admin'

def user_row_to_dict(row, cols):
    d = {}
    for i, c in enumerate(cols):
        d[c] = row[i]
    return d

def reminder_loop():
    """
    Kører kun i tidsvinduet 06–18 hver 2. time (06,08,10,12,14,16,18).
    Ved hvert tick sender vi varsling for starttid = (tick + 1 time), så 06→07, 10→11, 14→15, 18→19.
    Undgår dubletter via reminders_sent (dato, slot_index).
    """
    tz = timezone("Europe/Copenhagen")

    # Sikr markeringstabel
    try:
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS reminders_sent (
                id SERIAL PRIMARY KEY,
                dato DATE NOT NULL,
                slot_index INT NOT NULL,
                sendt TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                UNIQUE (dato, slot_index)
            )
        """)
        conn.commit()
        conn.close()
    except Exception as e:
        print("⚠️ Kunne ikke sikre reminders_sent-tabellen:", e)

    while True:
        try:
            now = datetime.now(tz)
            naeste = _naeste_tick_2t_window(now)  # næste 2-timers tick i 06–18 vinduet
            vent = max(1, int((naeste - now).total_seconds()))
            print(f"⏳ Venter til {naeste.strftime('%Y-%m-%d %H:%M')} (DK-tid)")
            time.sleep(vent)

            # Når vi rammer tick → varsling for start om 1 time
            tick = naeste  # allerede lokal DK
            target = tick + timedelta(hours=1)
            target_date = target.date()
            target_hour = target.hour

            conn = get_db_connection()
            start_hours = _hent_start_hours(conn)  # fx {7:0, 11:1, 15:2, 19:3}
            if target_hour not in start_hours:
                conn.close()
                # gå direkte videre til næste tick
                continue

            target_slot = start_hours[target_hour]

            # Har vi allerede sendt for (dato, slot)?
            with conn.cursor() as cur:
                cur.execute("SELECT 1 FROM reminders_sent WHERE dato=%s AND slot_index=%s",
                            (target_date, target_slot))
                already = cur.fetchone() is not None
            if already:
                conn.close()
                continue

            # Hent modtagere og slot-tekst
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT b.brugernavn, u.email, u.sms
                    FROM bookinger b
                    JOIN brugere u ON u.brugernavn = b.brugernavn
                    WHERE b.dato_rigtig = %s AND b.slot_index = %s
                """, (target_date, target_slot))
                modtagere = cur.fetchall()

                cur.execute("SELECT tekst FROM vasketider WHERE slot_index = %s", (target_slot,))
                row = cur.fetchone()
                slot_tekst = (row[0] if row else f"Slot {target_slot}")

            # Send besked (eller markér 'sendt' hvis ingen modtagere så vi ikke spammer næste gang)
            if not modtagere:
                with conn.cursor() as cur:
                    cur.execute("""
                        INSERT INTO reminders_sent (dato, slot_index)
                        VALUES (%s, %s) ON CONFLICT DO NOTHING
                    """, (target_date, target_slot))
                conn.commit()
                conn.close()
                continue

            besked = f"Din vasketid starter om 1 time ({slot_tekst})."
            for navn, email, sms in modtagere:
                try:
                    if email: send_email(email, "Vasketid påmindelse", besked)
                    if sms:   send_sms_twilio(sms, besked)
                    print(f"📣 Varslet {navn} for {target_date} {slot_tekst}")
                except Exception as e:
                    print("⚠️ Fejl ved varsling:", e)

            # Markér som sendt
            with conn.cursor() as cur:
                cur.execute("""
                    INSERT INTO reminders_sent (dato, slot_index)
                    VALUES (%s, %s) ON CONFLICT DO NOTHING
                """, (target_date, target_slot))
            conn.commit()
            conn.close()

        except Exception as e:
            print("❌ Fejl i reminder_loop:", e)
            time.sleep(60)

_jobs_started = False
def start_background_jobs():
    global _jobs_started
    if _jobs_started:
        return
    _jobs_started = True
    threading.Thread(target=reminder_loop, daemon=True).start()
    threading.Thread(target=ryd_gamle_bookinger_job, daemon=True).start()

start_background_jobs()

# funktionerne @app bliver registreret i programmet og starter ved at blive aktiveret af brugeren

@app.get("/_ping")
def _ping():
    return "ok", 200

@app.get("/_geo_debug")
def _geo_debug():
    ip = get_client_ip(request)
    ua = request.headers.get("User-Agent","")
    out = {
        "client_ip": ip,
        "ua": ua,
        "ua_parsed": parse_ua(ua),
        "geo": local_geo(ip),
        "city_mmdb_loaded": bool(_city_reader),
        "asn_mmdb_loaded": bool(_asn_reader),
    }
    return jsonify(out), 200

# ===============
# Miele UI
# ===============

@app.route('/ha_webhook', methods=['POST'])
def ha_webhook():
    try:
        data = request.get_json(force=True)

        # --- Input parsing ---
        raw_status = str(data.get("status", "Ukendt")).strip()
        remaining_time = str(data.get("remaining_time", "")).strip()  # "0:45:00" eller ""
        opdateret = data.get("opdateret", datetime.now())

        # Konverter streng til datetime hvis nødvendigt
        if isinstance(opdateret, str):
            try:
                opdateret = datetime.fromisoformat(opdateret)
            except ValueError:
                opdateret = datetime.now()

        # Normaliser/oversæt status til dansk (din eksisterende helper)
        norm_status = set_miele_status(raw_status)  # f.eks. "kørende", "færdig", "standby", ...

        # Resttid → "xx min"
        if remaining_time:
            try:
                h, m, s = map(int, remaining_time.split(":"))
                total_min = h * 60 + m
                remaining_time = f"{total_min} min"
            except ValueError:
                pass  # bevar original hvis parsning fejler

        # --- Gem seneste status (overstyrer single-row tabel) ---
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("""
            CREATE TABLE IF NOT EXISTS miele_status (
                id SERIAL PRIMARY KEY,
                status TEXT,
                remaining_time TEXT,
                opdateret TIMESTAMP
            )
        """)
        cur.execute("DELETE FROM miele_status")
        cur.execute("""
            INSERT INTO miele_status (status, remaining_time, opdateret)
            VALUES (%s, %s, %s)
        """, (norm_status, remaining_time, opdateret))
        conn.commit()
        cur.close()
        conn.close()

        # --- Log aktivitet i historik (append) ---
        try:
            conn2 = get_db_connection()
            cur2 = conn2.cursor()
            cur2.execute("""
                CREATE TABLE IF NOT EXISTS miele_activity (
                    id SERIAL PRIMARY KEY,
                    ts TIMESTAMP NOT NULL,
                    status TEXT NOT NULL
                )
            """)
            cur2.execute("CREATE INDEX IF NOT EXISTS idx_miele_activity_ts ON miele_activity(ts)")
            cur2.execute("INSERT INTO miele_activity (ts, status) VALUES (%s, %s)", (opdateret, norm_status))
            conn2.commit()
            cur2.close()
            conn2.close()
        except Exception:
            # historik må ikke vælte webhook – fortsæt stille
            try:
                cur2.close(); conn2.close()
            except Exception:
                pass

        # ===================== NYT: Knyt HA-status til booking ======================
        # Definér slots som i din app: 0:(07-11), 1:(11-15), 2:(15-19), 3:(19-23)
        def _current_slot_index(dt):
            h = dt.hour
            if   7 <= h < 11:  return 0
            elif 11 <= h < 15: return 1
            elif 15 <= h < 19: return 2
            elif 19 <= h < 23: return 3
            return None

        # Normaliseret status-sæt (lowercase for robust matching)
        s = (norm_status or "").strip().lower()
        RUNNING_STATES  = {"kørende", "i brug", "vask", "washing", "running", "main wash", "hovedvask"}
        FINISHED_STATES = {"færdig", "finish", "end", "slut", "program ended", "done"}

        slot_idx = _current_slot_index(opdateret)
        if slot_idx is not None:
            conn3 = get_db_connection()
            cur3 = conn3.cursor()
            try:
                # 1) START/KØRER → pending_activation -> active
                if s in RUNNING_STATES:
                    cur3.execute("""
                        UPDATE bookinger
                           SET status='active',
                               activated_at = NOW(),
                               activation_required = FALSE
                         WHERE dato_rigtig = CURRENT_DATE
                           AND slot_index   = %s
                           AND status       = 'pending_activation'
                    """, (slot_idx,))
                    activated_rows = cur3.rowcount

                    # (Valgfrit) hvis ingen pending, men der findes en "booked" i den aktuelle slot,
                    # kan du vælge at aktivere den også. Slå til hvis det giver mening i din model:
                    if activated_rows == 0:
                        cur3.execute("""
                            UPDATE bookinger
                               SET status='active',
                                   activated_at = NOW(),
                                   activation_required = FALSE
                             WHERE dato_rigtig = CURRENT_DATE
                               AND slot_index   = %s
                               AND status       = 'booked'
                        """, (slot_idx,))

                    conn3.commit()

                # 2) FÆRDIG → active -> completed
                elif s in FINISHED_STATES:
                    cur3.execute("""
                        UPDATE bookinger
                           SET status='completed'
                         WHERE dato_rigtig = CURRENT_DATE
                           AND slot_index   = %s
                           AND status       = 'active'
                    """, (slot_idx,))
                    conn3.commit()
            finally:
                cur3.close()
                conn3.close()
        # ===========================================================================

        print(f"✅ Miele-status gemt: {norm_status} – Resttid: {remaining_time} (Opdateret: {opdateret})")
        return jsonify({
            "status": "ok",
            "received": norm_status,
            "remaining_time": remaining_time,
            "opdateret": opdateret
        }), 200

    except Exception as e:
        print("❌ Fejl i ha_webhook:", e)
        return jsonify({"error": str(e)}), 500

# ================
# Login og Logud
# ================

@app.route('/')
def home():
    return redirect('/login')

@limiter.limit("5 per 10 minutes")
@app.route('/login', methods=['GET', 'POST'])
def login():
    fejl = request.args.get("fejl", "")
    besked = request.args.get("besked", "")

    # Allerede logget ind? Send til index
    if request.method == 'GET' and 'brugernavn' in session:
        return redirect('/index')

    if request.method == 'POST':
        brugernavn = request.form['brugernavn'].lower()
        kode = request.form['kode']

        ip = request.remote_addr
        enhed = request.headers.get('User-Agent', 'Ukendt')
        tidspunkt = datetime.now().strftime('%Y-%m-%d %H:%M:%S')

        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("SELECT kode, godkendt, email, sms FROM brugere WHERE brugernavn = %s", (brugernavn,))
        result = cur.fetchone()

        if not result:
            cur.execute("INSERT INTO login_forsøg (brugernavn, ip, succes) VALUES (%s, %s, %s)", (brugernavn, ip, False))
            conn.commit()
            cur.close()
            conn.close()

            status = "Fejl i login"
            conn = get_db_connection()
            cur = conn.cursor()
            log_login_privacy(cur, request, brugernavn, "Fejl i login")   # ved ukendt bruger ELLER forkert kode
            conn.commit()
            conn.close()
            return redirect('/login?fejl=Forkert+brugernavn')

        kode_rigtig, godkendt, email, sms = result

        if kode != kode_rigtig:
            cur.execute("INSERT INTO login_forsøg (brugernavn, ip, succes) VALUES (%s, %s, %s)", (brugernavn, ip, False))
            conn.commit()
            cur.close()
            conn.close()

            status = "Fejl i login"
            conn = get_db_connection()
            cur = conn.cursor()
            log_login_privacy(cur, request, brugernavn, "Fejl i login")
            conn.commit()

            cur.execute("SELECT COUNT(*) FROM login_log WHERE ip = %s AND status = 'Fejl i login' AND tidspunkt::date = CURRENT_DATE", (ip,))
            antal = cur.fetchone()[0]
            conn.close()

            if antal >= 5:
                send_email("hornsbergmorten@gmail.com", "Advarsel: Fejllogin", f"{antal} fejllogin fra IP {ip} – Enhed:\n{enhed}")

            return redirect('/login?fejl=Forkert+adgangskode')

        if not godkendt:
            cur.execute("INSERT INTO login_forsøg (brugernavn, ip, succes) VALUES (%s, %s, %s)", (brugernavn, ip, False))
            conn.commit()
            cur.close()
            conn.close()

            status = "Fejl i login"
            conn = get_db_connection()
            cur = conn.cursor()
            log_login_privacy(cur, request, brugernavn, "Ikke godkendt")
            conn.commit()
            conn.close()

            besked_admin = f"""Brugeren '{brugernavn}' forsøgte at logge ind {tidspunkt}
IP: {ip}
Status: Brugeren er endnu ikke godkendt."""
            send_email("hornsbergmorten@gmail.com", "Bruger venter godkendelse", besked_admin)

            return redirect('/login?fejl=Bruger+ikke+endnu+godkendt.+Admin+er+informeret.')

        cur.execute("INSERT INTO login_forsøg (brugernavn, ip, succes) VALUES (%s, %s, %s)", (brugernavn, ip, True))
        conn.commit()
        cur.close()
        conn.close()

        status = "OK"
        conn = get_db_connection()
        cur = conn.cursor()
        log_login_privacy(cur, request, brugernavn, "OK")
        conn.commit()
        conn.close()

        session['brugernavn'] = brugernavn
        
        remember = request.form.get('remember') == '1'
        session.permanent = remember

        next_url = '/admin' if brugernavn == 'admin' else '/index'
        resp = redirect(next_url)

        if remember:
            resp.set_cookie('remember_me', '1', max_age=60*60*24*30, samesite='Lax', secure=True)
        else:
            resp.delete_cookie('remember_me')

        return resp

    # GET (vis login.html)
    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("SELECT adresse, aktiv FROM adresse_visning WHERE vis_paa_login = TRUE")
    adresser = cur.fetchall()
    conn.close()

    return render_template('login.html', fejl=fejl, besked=besked, adresser=adresser)

@app.route('/logout', methods=['GET', 'POST'])
def logout():
    session.clear()
    return redirect('/login')

# ==============
# Admin
# ==============

@app.get("/_testmail")
def _testmail():
    # Kun admin må teste mail
    if session.get('brugernavn', '').lower() != 'admin':
        return redirect('/login')

    try:
        send_email(
            "hornsbergmorten@gmail.com",
            "Test fra Vasketider",
            "Denne mail kommer direkte fra Flask send_email(). Hvis du ser den, virker mail."
        )
        return "OK – testmail sendt. Tjek din indbakke (og evt. spam)."
    except Exception as e:
        # Log og vis kort fejl
        print("❌ _testmail fejl:", e, flush=True)
        return f"FEJL – kunne ikke sende testmail: {e}", 500

@app.route("/admin/ryd_logs", methods=["POST"])
def admin_ryd_logs():
    if session.get('brugernavn','').lower() != 'admin':
        return redirect(url_for('login'))

    slet_login      = truthy(request.form.get("slet_login"))
    slet_booking    = truthy(request.form.get("slet_booking"))
    slet_attempts   = truthy(request.form.get("slet_attempts"))
    slet_kaeder     = truthy(request.form.get("slet_kaeder"))
    slet_miele_act  = truthy(request.form.get("slet_miele_act"))
    slet_miele_stat = truthy(request.form.get("slet_miele_stat"))
    slet_statistik  = truthy(request.form.get("slet_statistik"))
    slet_alt        = truthy(request.form.get("slet_alt"))

    fra = (request.form.get("fra_dato") or "").strip()
    til = (request.form.get("til_dato") or "").strip()

    if not any([slet_login, slet_booking, slet_attempts, slet_kaeder,
                slet_miele_act, slet_miele_stat, slet_statistik, slet_alt]):
        flash("Vælg mindst én logtype.", "fejl")
        return redirect(url_for("statistik"))

    # Helper til WHERE for timestamp/date kolonner
    def build_where(colname: str):
        parts, params = [], []
        if fra:
            parts.append(f'{colname}::date >= %s'); params.append(fra)
        if til:
            parts.append(f'{colname}::date <= %s'); params.append(til)
        return (" WHERE " + " AND ".join(parts), tuple(params)) if parts else ("", tuple())

    # Map: tabel + kolonne for datofilter
    targets = {
        "login_log":        ('login_log',            'tidspunkt'),
        "booking_log":      ('booking_log',          'tidspunkt'),
        "booking_attempts": ('booking_attempts',     'ts'),
        "direkte_kæder":    ('\"direkte_kæder\"',    'created_at'),  # bemærk citat
        "miele_activity":   ('miele_activity',       'ts'),
        "miele_status":     ('miele_status',         'opdateret'),
        "statistik":        ('statistik',            'dato'),
    }

    conn = get_db_connection(); cur = conn.cursor()
    slettet_info = []

    try:
        if slet_alt:
            for t, _ in [(v[0], v[1]) for v in targets.values()]:
                cur.execute(f"TRUNCATE TABLE {t} RESTART IDENTITY")
            conn.commit()
            flash("Alle log-tabeller er nulstillet.", "ok")
            return redirect(url_for("statistik"))

        # Hjælpefunktion til sletning med faldbak uden filter,
        # hvis en kolonne ikke findes i et miljø.
        def delete_with_optional_filter(table, col):
            where, params = build_where(col)
            try:
                cur.execute(f"DELETE FROM {table}{where} RETURNING 1", params)
            except Exception as e:
                print(f"⚠️ {table} delete med filter fejlede → prøver uden filter:", e, flush=True)
                cur.execute(f"DELETE FROM {table} RETURNING 1")
            return cur.rowcount

        if slet_login:
            t, col = targets["login_log"];       rc = delete_with_optional_filter(t, col); slettet_info.append(f"login_log: {rc}")
        if slet_booking:
            t, col = targets["booking_log"];     rc = delete_with_optional_filter(t, col); slettet_info.append(f"booking_log: {rc}")
        if slet_attempts:
            t, col = targets["booking_attempts"];rc = delete_with_optional_filter(t, col); slettet_info.append(f"booking_attempts: {rc}")
        if slet_kaeder:
            t, col = targets["direkte_kæder"];   rc = delete_with_optional_filter(t, col); slettet_info.append(f"direkte_kæder: {rc}")
        if slet_miele_act:
            t, col = targets["miele_activity"];  rc = delete_with_optional_filter(t, col); slettet_info.append(f"miele_activity: {rc}")
        if slet_miele_stat:
            t, col = targets["miele_status"];    rc = delete_with_optional_filter(t, col); slettet_info.append(f"miele_status: {rc}")
        if slet_statistik:
            t, col = targets["statistik"];       rc = delete_with_optional_filter(t, col); slettet_info.append(f"statistik: {rc}")

        conn.commit()
    except Exception as e:
        conn.rollback()
        print("❌ Fejl ved rydning af logs:", e, flush=True)
        flash("Fejl under sletning.", "fejl")
    finally:
        try:
            cur.close(); conn.close()
        except Exception:
            pass

    flash("Slettede: " + (", ".join(slettet_info) if slettet_info else "ingen ændringer"), "ok")
    return redirect(url_for("statistik", besked="Slettede logninger"))

@app.route('/admin')
def admin():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    conn = get_db_connection()
    cur = conn.cursor()

    # Hent brugere
    cur.execute("SELECT * FROM brugere")
    brugere = [
        dict(
            brugernavn=row[0],
            adgangskode=row[1],
            email=row[2],
            sms=row[3]
        ) for row in cur.fetchall()
    ]

    # Hent bookinger
    cur.execute("SELECT id, brugernavn, dato_rigtig, slot_index FROM bookinger")
    bookinger = [
        dict(
            id=row[0],
            brugernavn=row[1],
            dato=row[2].strftime('%d-%m-%Y'),
            tid=row[3]
        ) for row in cur.fetchall()
    ]

    # Hent kommentar
    cur.execute("SELECT * FROM kommentar")
    kommentar = [
        dict(id=row[0], brugernavn=row[1], tekst=row[2]) for row in cur.fetchall()
    ]

    # Hent booking log
    cur.execute("SELECT brugernavn, handling, dato, slot_index, tidspunkt FROM booking_log ORDER BY tidspunkt DESC LIMIT 100")
    booking_log = cur.fetchall()

    # ✅ Hent vasketider
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider = [r[1] for r in cur.fetchall()]

    cur.execute("SELECT adresse, vis_paa_login FROM adresse_visning ORDER BY adresse")
    adresser = cur.fetchall()

    cur.execute("SELECT vaerdi FROM indstillinger WHERE navn = 'vis_adresse_dropdown'")
    row = cur.fetchone()
    vis_dropdown = row and row[0] == 'true'

    conn.close()

    return render_template(
        "admin.html",
        brugere=brugere,
        bookinger=bookinger,
        kommentar=kommentar,
        booking_log=booking_log,
        tider=tider,  # ✅ Send med til admin.html
        adresser=adresser,
        vis_dropdown=vis_dropdown,
    )

@app.route("/opdater_dropdownvisning", methods=["POST"])
def opdater_dropdownvisning():
    if 'brugernavn' not in session or session['brugernavn'] != 'admin':
        return redirect('/login')

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("SELECT adresse FROM adresse_visning")
    adresser = cur.fetchall()

    for (adresse,) in adresser:
        felt = f"vis_{adresse}"
        vis = felt in request.form
        cur.execute("UPDATE adresse_visning SET vis_paa_login = %s WHERE adresse = %s", (vis, adresse))

    conn.commit()
    conn.close()
    return redirect("/admin")

@app.route("/admin/skiftkode", methods=["GET", "POST"])
def admin_skiftkode():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    fejl = ""
    if request.method == "POST":
        ny_kode = request.form.get("ny_kode")
        if not ny_kode:
            fejl = "Kode kan ikke være tom"
        else:
            conn = get_db_connection()
            cur = conn.cursor()
            cur.execute("UPDATE brugere SET kode = %s WHERE LOWER(brugernavn) = 'admin'", (ny_kode,))
            conn.commit()
            conn.close()
            return redirect("/admin")

    return render_template("admin_skiftkode.html", fejl=fejl)

@app.route("/admin/book_service", methods=["POST"])
def admin_book_service():
    dato = request.form.get("dato")
    tid = request.form.get("tid")  # f.eks. "07–11"

    if not dato or not tid:
        return "Ugyldig dato eller tidspunkt", 400

    try:
        dato_iso = datetime.strptime(dato, '%Y-%m-%d').strftime('%Y-%m-%d')
    except:
        dato_iso = dato

    # Map tekst → slot_index
    tidsmap = {
        "07–11": 0,
        "11–15": 1,
        "15–19": 2,
        "19–23": 3
    }

    if tid not in tidsmap:
        return "Ukendt tidsrum", 400

    slot_index = tidsmap[tid]

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute(
        "INSERT INTO bookinger (brugernavn, dato_rigtig, slot_index) VALUES (%s, %s, %s)",
        ("service", dato_iso, slot_index)
    )
    conn.commit()
    conn.close()

    return redirect("/admin")

@app.route("/admin/opdater_tider", methods=["POST"])
def admin_opdater_tider():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    conn = get_db_connection()
    cur = conn.cursor()
    for i in range(4):
        ny_tekst = request.form.get(f"slot_{i}", "").strip()
        if ny_tekst:
            cur.execute("UPDATE vasketider SET tekst = %s WHERE slot_index = %s", (ny_tekst, i))
    conn.commit()
    conn.close()
    return redirect("/admin")

@app.route("/admin/delete_booking", methods=["POST"])
def admin_delete_booking():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    booking_id = request.form.get("booking_id")
    if not booking_id:
        return redirect("/admin")

    conn = get_db_connection()
    cur = conn.cursor()
    try:
        cur.execute("DELETE FROM bookinger WHERE id = %s", (booking_id,))
        conn.commit()
    finally:
        cur.close()
        conn.close()
    return redirect("/admin")

@app.route("/admin/delete_comment", methods=["POST"])
def admin_delete_comment():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    kommentar_id = request.form.get("kommentar_id")
    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("DELETE FROM kommentar WHERE id = %s", (kommentar_id,))
    conn.commit()
    conn.close()
    return redirect("/admin")

@app.route('/admin/reset_direkte', methods=['POST'])
def reset_direkte():
    if session.get('brugernavn','').lower() != 'admin':
        abort(403)
    nyt_pw = secrets.token_urlsafe(12)  # Admin ser dette én gang
    conn = get_db_connection(); cur = conn.cursor()
    cur.execute("UPDATE brugere SET kode=%s WHERE brugernavn='direkte'", (hash_kode(nyt_pw),))
    conn.commit(); conn.close()
    # Vis password til admin via flash/besked (eller redirect med querystring)
    return redirect(f"/vis_brugere?direkte_pw={nyt_pw}")

@app.route("/admin/brugere")
def admin_vis_brugere():
    if not require_admin():
        return redirect("/login")

    conn = get_db_connection()
    cur = conn.cursor()
    try:
        # Sikr kolonnerne findes (nød-fallback hvis migrering ikke er kørt)
        cur.execute("""
            DO $$
            BEGIN
              IF NOT EXISTS (SELECT 1 FROM information_schema.columns
                             WHERE table_name='brugere' AND column_name='godkendt') THEN
                ALTER TABLE brugere ADD COLUMN godkendt BOOLEAN DEFAULT TRUE;
              END IF;
              IF NOT EXISTS (SELECT 1 FROM information_schema.columns
                             WHERE table_name='brugere' AND column_name='notif_mail') THEN
                ALTER TABLE brugere ADD COLUMN notif_mail BOOLEAN DEFAULT TRUE;
              END IF;
              IF NOT EXISTS (SELECT 1 FROM information_schema.columns
                             WHERE table_name='brugere' AND column_name='notif_sms') THEN
                ALTER TABLE brugere ADD COLUMN notif_sms BOOLEAN DEFAULT FALSE;
              END IF;
              IF NOT EXISTS (SELECT 1 FROM information_schema.columns
                             WHERE table_name='brugere' AND column_name='email') THEN
                ALTER TABLE brugere ADD COLUMN email TEXT;
              END IF;
              IF NOT EXISTS (SELECT 1 FROM information_schema.columns
                             WHERE table_name='brugere' AND column_name='sms') THEN
                ALTER TABLE brugere ADD COLUMN sms TEXT;
              END IF;
            END$$;
        """)
        conn.commit()

        cur.execute("""
            SELECT id, brugernavn, kode, email, sms, COALESCE(godkendt, TRUE),
                   COALESCE(notif_mail, TRUE), COALESCE(notif_sms, FALSE)
            FROM brugere
            ORDER BY LOWER(brugernavn)
        """)
        rows = cur.fetchall() or []
        cols = ["id","brugernavn","kode","email","sms","godkendt","notif_mail","notif_sms"]
        brugere = [user_row_to_dict(r, cols) for r in rows]
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

    return render_template("vis_brugere.html", brugere=brugere)

@app.route("/admin/brugere/opret", methods=["POST"])
def admin_opret_bruger():
    if not require_admin():
        return redirect("/login")

    bnavn = (request.form.get("brugernavn") or "").strip()
    kode  = (request.form.get("kode") or "").strip()
    kode2 = (request.form.get("kode2") or "").strip()
    email = (request.form.get("email") or "").strip() or None
    sms   = (request.form.get("sms") or "").strip() or None
    godk  = 1 if request.form.get("godkendt") == "1" else 0

    if not bnavn or not kode or kode != kode2:
        return redirect(url_for("admin_vis_brugere", fejl="Ugyldigt brugernavn eller kode stemmer ikke."))

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # tjek dublet
        cur.execute("SELECT 1 FROM brugere WHERE LOWER(brugernavn)=LOWER(%s)", (bnavn,))
        if cur.fetchone():
            return redirect(url_for("admin_vis_brugere", fejl="Brugernavn findes allerede."))

        cur.execute("""
            INSERT INTO brugere (brugernavn, kode, email, sms, godkendt, notif_mail, notif_sms)
            VALUES (%s,%s,%s,%s,%s, TRUE, FALSE)
        """, (bnavn, kode, email, sms, godk))
        conn.commit()
        return redirect(url_for("admin_vis_brugere", besked=f"Oprettet: {bnavn}"))
    except Exception as e:
        conn.rollback()
        print("Fejl opret bruger:", e)
        return redirect(url_for("admin_vis_brugere", fejl="Kunne ikke oprette bruger."))
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

@app.route("/admin/brugere/gem", methods=["POST"])
def admin_gem_bruger():
    if not require_admin():
        return redirect("/login")

    uid   = request.form.get("id")
    bnavn = (request.form.get("brugernavn") or "").strip()
    kode  = (request.form.get("kode") or "").strip()
    email = (request.form.get("email") or "").strip() or None
    sms   = (request.form.get("sms") or "").strip() or None

    # Checkboxe sender altid noget pga skjulte 0-felter i HTML
    notif_mail = 1 if request.form.get("notif_mail") == "1" else 0
    notif_sms  = 1 if request.form.get("notif_sms") == "1" else 0
    godk      = 1 if request.form.get("godkendt") == "1" else 0

    if not uid or not bnavn:
        return redirect(url_for("admin_vis_brugere", fejl="Manglende data ved gem."))

    conn = get_db_connection(); cur = conn.cursor()
    try:
        cur.execute("""
            UPDATE brugere
               SET brugernavn=%s,
                   kode=%s,
                   email=%s,
                   sms=%s,
                   godkendt=%s,
                   notif_mail=%s,
                   notif_sms=%s
             WHERE id=%s
        """, (bnavn, kode, email, sms, godk, notif_mail, notif_sms, uid))
        conn.commit()
        return redirect(url_for("admin_vis_brugere", besked=f"Gemt: {bnavn}"))
    except Exception as e:
        conn.rollback()
        print("Fejl gem bruger:", e)
        return redirect(url_for("admin_vis_brugere", fejl="Kunne ikke gemme ændringer."))
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

@app.route("/admin/brugere/slet", methods=["POST"])
def admin_slet_bruger():
    if not require_admin():
        return redirect("/login")
    uid = request.form.get("id")
    if not uid:
        return redirect(url_for("admin_vis_brugere", fejl="Mangler id."))

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # valgfrit: slet også relaterede rækker (bookinger) hvis ønsket
        cur.execute("DELETE FROM brugere WHERE id=%s", (uid,))
        conn.commit()
        return redirect(url_for("admin_vis_brugere", besked="Bruger slettet."))
    except Exception as e:
        conn.rollback()
        print("Fejl slet bruger:", e)
        return redirect(url_for("admin_vis_brugere", fejl="Kunne ikke slette."))
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

@app.route("/admin/brugere/godkend", methods=["POST"])
def admin_godkend_bruger():
    if not require_admin():
        return redirect("/login")
    uid = request.form.get("id")
    if not uid:
        return redirect(url_for("admin_vis_brugere", fejl="Mangler id."))

    conn = get_db_connection(); cur = conn.cursor()
    try:
        cur.execute("UPDATE brugere SET godkendt=TRUE WHERE id=%s", (uid,))
        conn.commit()
        return redirect(url_for("admin_vis_brugere", besked="Bruger godkendt."))
    except Exception as e:
        conn.rollback()
        print("Fejl godkend:", e)
        return redirect(url_for("admin_vis_brugere", fejl="Kunne ikke godkende."))
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

@app.route("/admin/brugere/book", methods=["POST"])
def admin_book_for_user():
    # kun admin
    if session.get('brugernavn','').lower() != 'admin':
        return redirect('/login')

    bnavn = (request.form.get("brugernavn") or "").strip()
    dato  = (request.form.get("dato") or "").strip()
    slot  = request.form.get("slot")
    btype = (request.form.get("type") or "full").strip()  # full/early/late

    if not bnavn or not dato or slot is None:
        return redirect("/vis_brugere?fejl=Udfyld+bruger%2C+dato+og+slot")

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # bruger findes og er godkendt
        cur.execute("SELECT 1 FROM brugere WHERE LOWER(brugernavn)=LOWER(%s) AND COALESCE(godkendt,TRUE)=TRUE", (bnavn,))
        if not cur.fetchone():
            return redirect("/vis_brugere?fejl=Bruger+findes+ikke+eller+ikke+godkendt")

        # max 2 pr. dag
        cur.execute("""
            SELECT COUNT(*) FROM bookinger
            WHERE LOWER(brugernavn)=LOWER(%s)
              AND dato_rigtig::date = %s::date
              AND COALESCE(status,'booked') IN ('booked','active','pending_activation')
        """, (bnavn, dato))
        if int(cur.fetchone()[0] or 0) >= 2:
            return redirect(f"/vis_brugere?fejl={bnavn}+har+allerede+2+bookinger+den+dag")

        # indsæt booking (slot_index gemmes som int)
        cur.execute("""
            INSERT INTO bookinger (brugernavn, dato_rigtig, slot_index, booking_type, status, created_at, activation_required)
            VALUES (%s, %s::date, %s::int, %s, 'booked', NOW(), FALSE)
            RETURNING id
        """, (bnavn, dato, int(slot), btype))
        bid = cur.fetchone()[0]

        # log forsøg (hvis booking_log findes, ellers ignorer fejl)
        try:
            cur.execute("""
                INSERT INTO booking_log (brugernavn, handling, dato, slot_index, booking_type, resultat, tidspunkt)
                VALUES (%s,'admin_book',%s::date,%s::int,%s,'ok',NOW())
            """, (bnavn, dato, int(slot), btype))
        except Exception:
            pass

        conn.commit()
    except Exception as e:
        conn.rollback()
        print("Fejl admin-book:", e)
        return redirect("/vis_brugere?fejl=Kunne+ikke+booke")
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

    return redirect(f"/vis_brugere?besked=Booket+for+{bnavn}+%28id+{bid}%29")


# ===============
# Bookninger
# ===============

@app.get("/dag_status_json")
def dag_status_json():
    if "brugernavn" not in session:
        return jsonify({"error":"unauthorized"}), 401

    dato_str = (request.args.get("dato") or "").strip()
    if not dato_str:
        return jsonify({"error":"missing ?dato=YYYY-MM-DD"}), 400

    try:
        d = datetime.strptime(dato_str, "%Y-%m-%d").date()
    except ValueError:
        return jsonify({"error":"invalid date format"}), 400

    conn = get_db_connection()
    with conn.cursor() as cur:
        status = hent_slot_status_for_dag(cur, d)
    conn.close()

    # Response: { "dato": "YYYY-MM-DD", "slots": { "0": {...}, "1": {...}, ... } }
    return jsonify({
        "dato": d.isoformat(),
        "slots": {str(k): v for k, v in status.items()}
    }), 200

@app.get('/bookinger_json')
def bookinger_json():
    # Kun admin må hente statistik-feed
    user = (session.get('brugernavn') or '').lower()
    if user != 'admin':
        return jsonify({"error": "Unauthorized"}), 401  # JSON i stedet for redirect

    # Param: ?days=14 (default 14)
    try:
        days = int(request.args.get('days', 14))
        days = max(1, min(days, 60))  # værn mod alt for store vinduer
    except ValueError:
        days = 14

    # Brug lokal tidszone
    from pytz import timezone
    tz = timezone("Europe/Copenhagen")
    idag = datetime.now(tz).date()
    slutdato = idag + timedelta(days=days)

    conn = get_db_connection()
    cur = conn.cursor()

    # (Ydelse) – sørg for disse indexes i din DB én gang:
    # CREATE INDEX IF NOT EXISTS idx_bookinger_dato ON bookinger(dato_rigtig);
    # CREATE INDEX IF NOT EXISTS idx_bookinger_dato_slot ON bookinger(dato_rigtig, slot_index);

    # Hent alle bookinger i interval – med flere felter
    # NB: bookinger.slot_index er TEXT hos dig → vi caster til INT for join/tekst.
    cur.execute("""
        SELECT
            b.brugernavn,
            b.dato_rigtig,
            b.slot_index,                 -- behold rå (TEXT) til JSON
            COALESCE(v.tekst, CONCAT('Slot ', b.slot_index)) AS slot_tekst,
            COALESCE(b.status, 'booked')  AS status,
            b.activation_deadline,
            b.activated_at,
            b.created_at
        FROM bookinger b
        LEFT JOIN vasketider v
               ON v.slot_index = CAST(b.slot_index AS INTEGER)
        WHERE b.dato_rigtig >= %s
          AND b.dato_rigtig <= %s
        ORDER BY b.dato_rigtig ASC, CAST(b.slot_index AS INTEGER) ASC
    """, (idag, slutdato))
    rows = cur.fetchall()
    conn.close()

    result = []
    for brugernavn, dato, slot_index_raw, slot_tekst, status, deadline, activated_at, created_at in rows:
        # Behold dit dd-mm-YYYY format + original “tid:” tekstfelt,
        # men tilføj også ISO felter (hjælper Excel/HA/JS)
        result.append({
            "dato": dato.strftime('%d-%m-%Y'),
            "dato_iso": dato.isoformat(),
            "tid": slot_tekst,
            "slot_index": slot_index_raw,          # rå fra DB (TEXT)
            "slot_index_int": _safe_int(slot_index_raw),  # hjælper i UI
            "navn": brugernavn,
            "status": status,
            "activation_deadline": deadline.isoformat() if deadline else None,
            "activated_at": activated_at.isoformat() if activated_at else None,
            "created_at": created_at.isoformat() if created_at else None
        })

    return jsonify(result)


def _safe_int(x):
    try:
        return int(x)
    except Exception:
        return None

@app.post("/book")
def book_full():
    # kræver login
    if "brugernavn" not in session:
        return redirect(url_for("login", fejl="Log ind for at booke en tid"))

    brugernavn = session["brugernavn"]
    valgt_uge  = (request.form.get("valgt_uge") or "").strip()

    # input
    try:
        dato = datetime.strptime((request.form.get("dato") or "").strip(), "%Y-%m-%d").date()
        slot = int(request.form.get("tid", "-1"))
    except Exception:
        return redirect(url_for("index", uge=valgt_uge, fejl="Ugyldige bookingfelter."))

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # optaget-check: fuld eller begge halvdele
        cur.execute("""
            SELECT
              SUM(CASE WHEN COALESCE(sub_slot,'full')='full' THEN 1 ELSE 0 END) AS fulls,
              SUM(CASE WHEN sub_slot='early' AND brugernavn IS NOT NULL THEN 1 ELSE 0 END) AS e_taken,
              SUM(CASE WHEN sub_slot='late'  AND brugernavn IS NOT NULL THEN 1 ELSE 0 END) AS l_taken
            FROM bookinger
            WHERE dato_rigtig=%s AND slot_index::int=%s
        """, (dato, slot))
        fulls, e_taken, l_taken = [x or 0 for x in cur.fetchone()]
        if fulls > 0 or (e_taken > 0 and l_taken > 0):
            return redirect(url_for("index", uge=valgt_uge, fejl="Tiden er allerede optaget."))

        # max 2 pr. dag
        cur.execute("""
            SELECT COUNT(*)
            FROM bookinger
            WHERE dato_rigtig=%s AND LOWER(brugernavn)=LOWER(%s)
        """, (dato, brugernavn))
        if (cur.fetchone()[0] or 0) >= 2:
            return redirect(url_for("index", uge=valgt_uge, fejl="Du har allerede 2 bookinger den dag."))

        # aktiveringsvindue: 30 min
        slot_start, _ = slot_start_end(dato.strftime("%Y-%m-%d"), slot)
        activation_deadline = slot_start + timedelta(minutes=30)
        activation_deadline_naive = activation_deadline.replace(tzinfo=None) if getattr(activation_deadline, "tzinfo", None) else activation_deadline

        cur.execute("""
            INSERT INTO bookinger (
              dato_rigtig, slot_index, brugernavn,
              sub_slot, status, activation_required, activation_deadline, created_at
            )
            VALUES (%s,%s,%s,'full','pending_activation',TRUE,%s,NOW())
        """, (dato, slot, brugernavn, activation_deadline_naive))

        conn.commit()
    except Exception as e:
        conn.rollback()
        print("❌ /book fejl:", e, flush=True)
        return redirect(url_for("index", uge=valgt_uge, fejl="Fejl under fuld booking."))
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

    # Notifikation EFTER commit
    try:
        send_booking_notice(brugernavn, dato, slot, None, "booked")
    except Exception as e:
        print("⚠️ Notifikation (book full) fejlede:", e, flush=True)

    return redirect(url_for("index", uge=valgt_uge,
                            besked="Tid booket. Start maskinen inden 30 min, ellers frigives tiden automatisk."))

@app.before_request
def auto_release():
    conn = get_db_connection()
    cur = conn.cursor()
    try:
        # 1) tjek om der har været Miele-aktivitet de sidste 3 min
        cur.execute("""
            SELECT 1 FROM miele_activity
             WHERE ts > NOW() - INTERVAL '3 minutes'
             LIMIT 1
        """)
        active_recently = bool(cur.fetchone())

        # 2) hvis aktivitet → aktiver pending (inden for 10 min margin)
        if active_recently:
            cur.execute("""
                UPDATE bookinger
                   SET status='active',
                       activated_at=NOW(),
                       activation_required=FALSE
                 WHERE activation_required=TRUE
                   AND status='pending_activation'
                   AND activation_deadline >= NOW() - INTERVAL '10 minutes'
            """)
            activated = cur.rowcount
            if activated > 0:
                print(f"🟢 auto_release: {activated} pending aktiveret pga. Miele-aktivitet")

        # 3) markér dem som udløbet (ingen aktivitet inden frist)
        cur.execute("""
            UPDATE bookinger
               SET status='expired'
             WHERE activation_required=TRUE
               AND status='pending_activation'
               AND activation_deadline < NOW()
            RETURNING id, brugernavn, dato_rigtig, slot_index, COALESCE(sub_slot,'full'), COALESCE(booking_type,'full')
        """)
        expired_rows = cur.fetchall() or []

        # 3a) log alle expired som 'auto_remove' i booking_log
        if expired_rows:
            cur.executemany("""
                INSERT INTO booking_log (brugernavn, handling, dato, slot_index, booking_type, resultat, tidspunkt)
                VALUES (%s,'auto_remove',%s,%s,%s,'ok',NOW())
            """, [(r[1], r[2], r[3], r[5]) for r in expired_rows])

        # 4) slet de udløbne (efter de er logget)
        if expired_rows:
            cur.execute("DELETE FROM bookinger WHERE status='expired'")

        conn.commit()
        if expired_rows:
            print(f"🟠 auto_release: {len(expired_rows)} udløbet → slettet (logget som auto_remove)")

    except Exception as e:
        print("❌ Fejl i auto_release:", e)
        conn.rollback()
    finally:
        try:
            cur.close(); conn.close()
        except Exception:
            pass

@app.post("/slet")
def slet_booking():
    if "brugernavn" not in session:
        return redirect(url_for("login"))

    brugernavn = session["brugernavn"]
    valgt_uge  = request.form.get("valgt_uge", "")

    try:
        dato_str  = (request.form.get("dato") or "").strip()
        tid_str   = (request.form.get("tid") or "-1").strip()
        sub       = (request.form.get("sub") or "").strip()  # None | 'early' | 'late'
        dato      = datetime.strptime(dato_str, "%Y-%m-%d").date()
        slot_int  = int(tid_str)
        slot_txt  = str(slot_int)
    except Exception:
        return redirect(url_for("index", uge=valgt_uge, fejl="Ugyldige felter."))

    other = "late" if sub == "early" else "early"

    conn = get_db_connection(); cur = conn.cursor()
    try:
        if sub in ("early", "late"):
            # Slet egen halv-booking (tolerér slot_index som TEXT eller INT)
            cur.execute("""
                DELETE FROM bookinger
                WHERE dato_rigtig = %s
                  AND (slot_index = %s OR slot_index::text = %s)
                  AND sub_slot = %s
                  AND LOWER(brugernavn) = LOWER(%s)
                RETURNING 1
            """, (dato, slot_int, slot_txt, sub, brugernavn))
            deleted = cur.fetchone() is not None

            # Ryd evt. tom placeholder på den anden halvdel (harmløst hvis ingen)
            if deleted:
                cur.execute("""
                    DELETE FROM bookinger
                    WHERE dato_rigtig = %s
                      AND (slot_index = %s OR slot_index::text = %s)
                      AND sub_slot = %s
                      AND brugernavn IS NULL
                """, (dato, slot_int, slot_txt, other))

            conn.commit()

            if deleted:
                try:
                    send_booking_notice(brugernavn, dato, slot_int, sub, "cancelled")
                except Exception as e:
                    print("⚠️ Notifikation (slet_half) fejlede:", e)
                return redirect(url_for("index", uge=valgt_uge, besked="Din halve booking er aflyst."))
            else:
                return redirect(url_for("index", uge=valgt_uge, fejl="Ingen matchende halv-booking at aflyse."))
        else:
            # Slet fuld booking
            cur.execute("""
                DELETE FROM bookinger
                WHERE dato_rigtig = %s
                  AND (slot_index = %s OR slot_index::text = %s)
                  AND LOWER(brugernavn) = LOWER(%s)
                  AND COALESCE(sub_slot, 'full') = 'full'
                RETURNING 1
            """, (dato, slot_int, slot_txt, brugernavn))
            deleted = cur.fetchone() is not None

            conn.commit()

            if deleted:
                try:
                    send_booking_notice(brugernavn, dato, slot_int, None, "cancelled")
                except Exception as e:
                    print("⚠️ Notifikation (slet_full) fejlede:", e)
                return redirect(url_for("index", uge=valgt_uge, besked="Din fulde booking er aflyst."))
            else:
                return redirect(url_for("index", uge=valgt_uge, fejl="Ingen matchende fuld booking at aflyse."))
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

@app.post("/book_half")
def book_half():
    if "brugernavn" not in session:
        return redirect(url_for("login"))

    brugernavn = session["brugernavn"]
    valgt_uge  = (request.form.get("valgt_uge") or "").strip()

    try:
        dato_str = (request.form.get("dato") or "").strip()
        tid_str  = (request.form.get("tid") or "").strip()
        sub      = (request.form.get("sub") or "").strip().lower()  # 'early' | 'late'
        if sub not in ("early", "late"):
            return redirect(url_for("index", uge=valgt_uge, fejl="Vælg 'tidlig' eller 'sen'."))

        dato = datetime.strptime(dato_str, "%Y-%m-%d").date()
        slot_txt = str(int(tid_str))  # altid TEXT-sammenligning i SQL
    except Exception:
        return redirect(url_for("index", uge=valgt_uge, fejl="Ugyldige bookingfelter."))

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # 0) Loft: max 2 pr. dag
        cur.execute("""
            SELECT COUNT(*) FROM bookinger
             WHERE dato_rigtig=%s AND LOWER(brugernavn)=LOWER(%s)
        """, (dato, brugernavn))
        if (cur.fetchone()[0] or 0) >= 2:
            print(f"🛑 book_half: afvist:max2 user={brugernavn} dato={dato}")
            return redirect(url_for("index", uge=valgt_uge, fejl="Du har allerede 2 bookinger den dag."))

        # 1) Fuldt slot blokerer halvdele
        cur.execute("""
            SELECT 1
              FROM bookinger
             WHERE dato_rigtig=%s
               AND slot_index::text=%s
               AND COALESCE(sub_slot,'full')='full'
               AND brugernavn IS NOT NULL
             LIMIT 1
        """, (dato, slot_txt))
        if cur.fetchone():
            print(f"🛑 book_half: afvist:full-taken user={brugernavn} dato={dato} slot={slot_txt}")
            return redirect(url_for("index", uge=valgt_uge, fejl="Slot er fuldt booket."))

        # 2) Min valgte halvdel taget?
        cur.execute("""
            SELECT 1
              FROM bookinger
             WHERE dato_rigtig=%s
               AND slot_index::text=%s
               AND sub_slot=%s
               AND brugernavn IS NOT NULL
             LIMIT 1
        """, (dato, slot_txt, sub))
        if cur.fetchone():
            print(f"🛑 book_half: afvist:half-taken user={brugernavn} dato={dato} slot={slot_txt} sub={sub}")
            return redirect(url_for("index", uge=valgt_uge, fejl="Den valgte halvdel er allerede taget."))

        # 3A) FORSØG FØRST AT OVERTAGE PLACEHOLDER (brugernavn IS NULL)
        cur.execute("""
            UPDATE bookinger
               SET brugernavn=%s,
                   status='active',
                   activation_required=FALSE,
                   created_at=NOW()
             WHERE dato_rigtig=%s
               AND slot_index::text=%s
               AND sub_slot=%s
               AND brugernavn IS NULL
             RETURNING 1
        """, (brugernavn, dato, slot_txt, sub))
        took_over = cur.fetchone() is not None

        # 3B) Hvis ingen placeholder: almindelig INSERT (kan stadig race-conflicte → håndteres af unique index)
        if not took_over:
            cur.execute("""
                INSERT INTO bookinger
                    (dato_rigtig, slot_index, brugernavn, sub_slot, status, activation_required, created_at)
                VALUES (%s, %s, %s, %s, 'active', FALSE, NOW())
            """, (dato, slot_txt, brugernavn, sub))

        conn.commit()
        print(f"✅ book_half: success user={brugernavn} dato={dato} slot={slot_txt} sub={sub} took_over={took_over}")

        # Notifikation efter commit
        try:
            send_booking_notice(brugernavn, dato, int(slot_txt), sub, "booked")
        except Exception as e:
            print("⚠️ Notifikation (book_half) fejlede:", e)

        return redirect(url_for("index", uge=valgt_uge, besked="Halv tid booket."))

    except Exception as e:
        conn.rollback()
        # vis reel psycopg info hvis tilgængelig
        code = getattr(e, "sqlstate", None) or getattr(e, "pgcode", None)
        diag  = getattr(e, "diag", None)
        print("❌ DB-fejl i book_half:", repr(e), "| sqlstate:", code, "| diag:", getattr(diag, "message_primary", None))
        return redirect(url_for("index", uge=valgt_uge, fejl="Kunne ikke booke halvtid (DB-konflikt)."))
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

@app.get("/api/booking_allowed_now")
def api_booking_allowed_now():
    secret = request.headers.get("X-HA-Token", "")
    if secret != HA_WEBHOOK_SECRET:
        return jsonify({"error": "Unauthorized"}), 401

    tz = timezone("Europe/Copenhagen")
    now = datetime.now(tz)
    dato_iso = now.strftime("%Y-%m-%d")
    slot_idx = _current_slot_index(now)

    if slot_idx is None:
        return jsonify({
            "allowed": False,
            "slot_index": None,
            "slot_text": "",
            "booked_by": "",
            "reason": "Uden for vasketidsvinduer"
        }), 200

    try:
        conn = get_db_connection()
        cur = conn.cursor()

        # Læs slot-tekst (INT i vasketider)
        cur.execute("SELECT tekst FROM vasketider WHERE slot_index = %s", (slot_idx,))
        row = cur.fetchone()
        slot_text = row[0] if row else f"Slot {slot_idx}"

        # bookinger.slot_index er TEXT → sammenlign med str(slot_idx)
        slot_idx_str = str(slot_idx)

        # Find relevant booking for nuværende dato/slot
        # - tilladelig status: pending_activation (hvis frist ikke udløbet), booked, active
        # - prioritet i visning: active > pending_activation > booked
        cur.execute("""
            SELECT brugernavn,
                   status,
                   COALESCE(activation_deadline, TIMESTAMP 'epoch') AS activation_deadline
            FROM bookinger
            WHERE dato_rigtig = %s
              AND slot_index   = %s
              AND status IN ('pending_activation','booked','active')
            ORDER BY CASE status
                        WHEN 'active' THEN 0
                        WHEN 'pending_activation' THEN 1
                        ELSE 2
                     END
            LIMIT 1
        """, (dato_iso, slot_idx_str))
        r = cur.fetchone()
        conn.close()

        if not r:
            return jsonify({
                "allowed": False,
                "slot_index": slot_idx,
                "slot_text": slot_text,
                "booked_by": "",
                "reason": "Ingen booking i aktivt tidsrum"
            }), 200

        booked_by, status, activation_deadline = r

        # Logik for allowed:
        # active → altid OK
        # booked → OK (du tillader start i hele slotten)
        # pending_activation → OK kun hvis frist ikke er udløbet
        if status == "active":
            allowed = True
            reason = "Aktiv booking"
        elif status == "booked":
            allowed = True
            reason = "Booket slot"
        elif status == "pending_activation":
            # hvis activation_deadline findes og er overskredet → ikke tilladt
            if activation_deadline and activation_deadline < now:
                allowed = False
                reason = "Aktiveringsfrist udløbet"
            else:
                allowed = True
                reason = "Afventer aktivering (inden for frist)"
        else:
            allowed = False
            reason = f"Status '{status}' tillader ikke drift"

        return jsonify({
            "allowed": allowed,
            "slot_index": slot_idx,
            "slot_text": slot_text,
            "booked_by": booked_by or "",
            "status": status,
            "activation_deadline": activation_deadline.isoformat() if activation_deadline else None,
            "now": now.isoformat(),
            "reason": reason
        }), 200

    except Exception as e:
        try:
            conn.close()
        except Exception:
            pass
        return jsonify({"error": "DB-fejl", "detail": str(e)}), 500

# ==============
# Bruger
# ==============

@app.route("/profil", methods=["GET", "POST"])
def profil():
    if 'brugernavn' not in session:
        return redirect('/login')

    fejl = ""
    besked = ""
    brugernavn = session['brugernavn']

    conn = get_db_connection()
    cur = conn.cursor()

    if request.method == "POST":
        email = request.form.get("email", "")
        sms = request.form.get("sms", "")
        if sms and not sms.startswith("+"):
            sms = "+45" + sms.strip()
        notifikation = 'ja' if _truthy(request.form.get("notifikation")) else 'nej'

        cur.execute("""
            UPDATE brugere
            SET email = %s, sms = %s, notifikation = %s
            WHERE brugernavn = %s
        """, (email, sms, notifikation, brugernavn))
        conn.commit()
        besked = "Oplysninger opdateret"

    cur.execute("SELECT email, sms, notifikation FROM brugere WHERE brugernavn = %s", (brugernavn,))
    result = cur.fetchone()
    email, sms, notifikation = result if result else ("", "", "nej")
    conn.close()

    return render_template("opret bruger.html", email=email, sms=sms, notifikation=notifikation, fejl=fejl, besked=besked, profil_visning=True)

@app.route('/opret', methods=['GET', 'POST'])
def opret():
    if request.method == 'POST':
        brugernavn = request.form['brugernavn'].lower()
        adgangskode = request.form['adgangskode']
        email = request.form.get('email', '')
        sms = request.form.get('sms', '')
        if sms and not sms.startswith("+"):
            sms = "+45" + sms.strip()
        notifikation = 'ja' if _truthy(request.form.get('notifikation')) else 'nej'
        godkendt = False  # kræver admin-godkendelse

        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("""
            INSERT INTO brugere (brugernavn, kode, email, sms, notifikation, godkendt)
            VALUES (%s, %s, %s, %s, %s, %s)
        """, (brugernavn, adgangskode, email, sms, notifikation, godkendt))
        conn.commit()
        cur.close()
        conn.close()

        token = generer_token(brugernavn)
        link = f"https://vasketider.onrender.com/godkend/{brugernavn}?token={token}"
        besked = f"En ny bruger er oprettet: '{brugernavn}'\n\nKlik for at godkende:\n{link}"
        send_email("vasketider.dk@gmail.com", "Godkend ny bruger", besked)

        return redirect('/login?besked=Bruger+oprettet+og+venter+godkendelse')

    return render_template("opret bruger.html")

@app.route("/vis_brugere")
def vis_brugere():
    conn = get_db_connection(); cur = conn.cursor()
    try:
        ensure_user_columns(cur); conn.commit()
        cur.execute("""
            SELECT brugernavn, kode, email, sms,
                   COALESCE(notifikation,'ja') AS notifikation,
                   COALESCE(notif_email,'ja') AS notif_email,
                   COALESCE(notif_sms,'nej')  AS notif_sms,
                   COALESCE(godkendt, TRUE)   AS godkendt
            FROM brugere
            ORDER BY LOWER(brugernavn)
        """)
        rows = cur.fetchall() or []
        cols = ['brugernavn','adgangskode','email','sms','notifikation','notif_email','notif_sms','godkendt']
        brugere = [dict(zip(cols, r)) for r in rows]
    finally:
        try: cur.close(); conn.close()
        except Exception: pass

    return render_template("vis_brugere.html", brugere=brugere)

@app.route("/opret_bruger", methods=["POST"])
def opret_bruger():
    brugernavn  = (request.form.get("brugernavn") or "").strip()
    adgangskode = (request.form.get("adgangskode") or "").strip()
    email       = (request.form.get("email") or "").strip() or None
    sms         = (request.form.get("sms") or "").strip() or None
    if sms and not sms.startswith("+"):
        sms = "+45" + sms

    # samlet + kanaler (skabelonen sender alle tre)
    notifikation = _ja_nej(_truthy(request.form.get("notifikation")))
    notif_email  = _ja_nej(_truthy(request.form.get("notif_email")))
    notif_sms    = _ja_nej(_truthy(request.form.get("notif_sms")))
    godkendt     = _truthy(request.form.get("godkendt"))

    if not brugernavn or not adgangskode:
        return redirect("/vis_brugere?fejl=Mangler+brugernavn+eller+password")

    conn = get_db_connection(); cur = conn.cursor()
    try:
        ensure_user_columns(cur)
        # sikr unikt brugernavn (case-insensitive)
        cur.execute("SELECT 1 FROM brugere WHERE LOWER(brugernavn)=LOWER(%s)", (brugernavn,))
        if cur.fetchone():
            return redirect("/vis_brugere?fejl=Brugernavn+findes+allerede")

        cur.execute("""
            INSERT INTO brugere (brugernavn, kode, email, sms, notifikation, notif_email, notif_sms, godkendt)
            VALUES (%s,%s,%s,%s,%s,%s,%s,%s)
        """, (brugernavn, adgangskode, email, sms, notifikation, notif_email, notif_sms, godkendt))
        conn.commit()
    finally:
        try: cur.close(); conn.close()
        except Exception: pass
    return redirect("/vis_brugere?besked=Bruger+oprettet")

@app.route("/slet_bruger", methods=["POST"])
def slet_bruger():
    brugernavn = (request.form.get("brugernavn") or "").strip()
    if not brugernavn:
        return redirect("/vis_brugere?fejl=Mangler+brugernavn")
    conn = get_db_connection(); cur = conn.cursor()
    try:
        cur.execute("DELETE FROM brugere WHERE LOWER(brugernavn)=LOWER(%s)", (brugernavn,))
        conn.commit()
    finally:
        try: cur.close(); conn.close()
        except Exception: pass
    return redirect("/vis_brugere?besked=Slettet")

@app.route("/godkend_bruger", methods=["POST"])
def godkend_bruger():
    brugernavn = (request.form.get("brugernavn") or "").strip()
    if not brugernavn:
        return redirect("/vis_brugere?fejl=Mangler+brugernavn")
    conn = get_db_connection(); cur = conn.cursor()
    try:
        cur.execute("UPDATE brugere SET godkendt=TRUE WHERE LOWER(brugernavn)=LOWER(%s)", (brugernavn,))
        conn.commit()
    finally:
        try: cur.close(); conn.close()
        except Exception: pass
    return redirect("/vis_brugere?besked=Godkendt")

@app.route("/opdater_bruger", methods=["POST"])
def opdater_bruger():
    brugernavn   = (request.form.get("brugernavn") or "").strip()
    adgangskode  = (request.form.get("adgangskode") or "").strip()
    email        = (request.form.get("email") or "").strip() or None
    sms          = (request.form.get("sms") or "").strip() or None
    if sms and not sms.startswith("+"):
        sms = "+45" + sms

    # checkbox linjen i HTML sender altid et skjult 'nej' + et 'ja' hvis kryds
    notifikation = _ja_nej(_truthy(request.form.get("notifikation")))
    notif_email  = _ja_nej(_truthy(request.form.get("notif_email")))
    notif_sms    = _ja_nej(_truthy(request.form.get("notif_sms")))
    godkendt     = _truthy(request.form.get("godkendt"))

    if not brugernavn:
        return redirect("/vis_brugere?fejl=Mangler+brugernavn")

    conn = get_db_connection(); cur = conn.cursor()
    try:
        ensure_user_columns(cur)
        cur.execute("""
            UPDATE brugere
               SET kode=%s,
                   email=%s,
                   sms=%s,
                   notifikation=%s,
                   notif_email=%s,
                   notif_sms=%s,
                   godkendt=%s
             WHERE brugernavn=%s
        """, (adgangskode, email, sms, notifikation, notif_email, notif_sms, godkendt, brugernavn))
        conn.commit()
    finally:
        try: cur.close(); conn.close()
        except Exception: pass
    return redirect("/vis_brugere?besked=Gemt")

@app.route("/godkend/<brugernavn>")
def godkend_via_link(brugernavn):
    token = request.args.get("token", "")
    korrekt_token = generer_token(brugernavn)

    if token != korrekt_token:
        return "Ugyldigt token – godkendelse afvist"

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("UPDATE brugere SET godkendt = TRUE WHERE brugernavn = %s", (brugernavn,))
    conn.commit()
    conn.close()

    return f"Brugeren '{brugernavn}' er nu godkendt."

@app.route('/skiftkode', methods=['GET'])
def skiftkode_get():
    fejl = request.args.get("fejl", "")
    return render_template("skiftkode.html", fejl=fejl)

@app.route('/skiftkode', methods=['POST'])
def skiftkode_post():
    brugernavn = request.form['brugernavn'].strip().lower()
    gammel_kode = request.form['gammel_kode']
    ny_kode1 = request.form['ny_kode1']
    ny_kode2 = request.form['ny_kode2']

    # NYT: kun admin må ændre 'direkte'-kode
    if brugernavn == 'direkte' and session.get('brugernavn','').lower() != 'admin':
        return redirect('/skiftkode?fejl=Kun+admin+kan+ændre+kode+for+direkte')

    if ny_kode1 != ny_kode2:
        return redirect('/skiftkode?fejl=Kodeord+matcher+ikke')

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("SELECT kode FROM brugere WHERE LOWER(brugernavn) = %s", (brugernavn,))
    result = cur.fetchone()

    if not result or result[0] != gammel_kode:
        conn.close()
        return redirect('/skiftkode?fejl=Forkert+brugernavn+eller+kodeord')

    if brugernavn == 'admin':
        conn.close()
        return redirect('/skiftkode?fejl=Admin+kan+kun+ændres+af+admin')

    cur.execute("UPDATE brugere SET kode = %s WHERE LOWER(brugernavn) = %s", (ny_kode1, brugernavn))
    conn.commit()
    conn.close()
    return redirect('/login?besked=Adgangskode+opdateret')

@app.route('/index')
def index():
    if 'brugernavn' not in session:
        return redirect('/login')
    brugernavn = session['brugernavn']

    idag_dt = datetime.today()
    idag = idag_dt.date()

    valgt_uge = request.args.get("uge")
    if valgt_uge:
        valgt_uge = int(valgt_uge)
        # mandag i den valgte ISO-uge
        start_dato = datetime.strptime(f"{idag.year} {valgt_uge} 1", "%G %V %u").date()
    else:
        valgt_uge = idag_dt.isocalendar().week
        start_dato = (idag_dt - timedelta(days=idag_dt.weekday())).date()

    uge_start = start_dato
    uge_slut  = start_dato + timedelta(days=6)

    ugedage_dk   = ["Mandag", "Tirsdag", "Onsdag", "Torsdag", "Fredag", "Lørdag", "Søndag"]
    ugedage_dato = [uge_start + timedelta(days=i) for i in range(7)]

    conn = get_db_connection()
    cur  = conn.cursor()

    # Vasketider
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider_raw = cur.fetchall()
    tider = [r[1] for r in tider_raw]

    # Hent ugens bookinger med sub_slot + status
    cur.execute("""
        SELECT dato_rigtig, slot_index, COALESCE(sub_slot,'full') AS sub, brugernavn, COALESCE(status,'active')
        FROM bookinger
        WHERE dato_rigtig BETWEEN %s AND %s
        ORDER BY dato_rigtig, slot_index
    """, (uge_start, uge_slut))
    rows = cur.fetchall()

    # Byg struktur til kalenderen
    bookinger = {}
    for d, slot, sub, navn, status in rows:
        key  = (d, int(slot))
        cell = bookinger.setdefault(key, {"full": None, "early": None, "late": None})
        item = {"navn": navn, "status": status}
        if sub == "full":
            cell["full"] = item
        elif sub == "early":
            cell["early"] = item
        elif sub == "late":
            cell["late"]  = item

    # Kommende 14 dage (til listen nederst)
    frem_slut = idag + timedelta(days=14)
    cur.execute("""
        SELECT b.dato_rigtig, b.slot_index, b.brugernavn, v.tekst
        FROM bookinger b
        JOIN vasketider v ON v.slot_index = b.slot_index
        WHERE b.dato_rigtig >= %s AND b.dato_rigtig <= %s
        ORDER BY b.dato_rigtig, b.slot_index
    """, (idag, frem_slut))
    kommende = [{
        "dato_iso": r[0].strftime("%Y-%m-%d"),
        "dato_dk":  r[0].strftime("%d-%m-%Y"),
        "slot_index": r[1],
        "brugernavn": r[2],
        "slot_tekst": r[3],
    } for r in cur.fetchall()]

    # Miele status (uændret – din eksisterende kode kan bevares)
    cur.execute("SELECT vaerdi FROM indstillinger WHERE navn = 'iot_vaskemaskine'")
    iot_row = cur.fetchone()
    iot = iot_row[0] if iot_row else "nej"

    cur.execute("SELECT status, remaining_time, opdateret FROM miele_status ORDER BY opdateret DESC LIMIT 1")
    row = cur.fetchone()
    if row:
        miele_status, remaining_time, miele_opdateret = row[0], row[1], row[2]
    else:
        miele_status, remaining_time, miele_opdateret = "Ukendt", None, None

    conn.close()

    return render_template(
        "index.html",
        ugedage_dk=ugedage_dk,
        ugedage_dato=ugedage_dato,
        tider=tider,
        valgt_uge=valgt_uge,
        bookinger=bookinger,        # ← nu den rigtige struktur
        bruger=brugernavn,
        idag_iso=idag_dt.strftime("%Y-%m-%d"),
        start_dato=uge_start.strftime("%Y-%m-%d"),
        kommende_bookinger=kommende,
        iot=iot,
        miele_status=miele_status,
        miele_remaining=remaining_time,
        miele_opdateret=miele_opdateret
    )

    # kommentar og dokumenter

@app.route('/kommentar', methods=['GET', 'POST'])
def kommentar():
    if 'brugernavn' not in session:
        return redirect('/login')

    if request.method == 'POST':
        brugernavn = session['brugernavn']
        tekst = request.form.get('kommentar', '')
        conn = get_db_connection()
        cur = conn.cursor()
        cur.execute("INSERT INTO kommentar (brugernavn, kommentar) VALUES (%s, %s)", (brugernavn, tekst))
        conn.commit()
        conn.close()
        return redirect('/kommentar')

    # GET: hent alle kommentar
    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("SELECT brugernavn, kommentar FROM kommentar ORDER BY id DESC")
    kommentar = cur.fetchall()
    conn.close()

    return render_template("kommentar.html", kommentar=kommentar)

@app.route("/dokumenter")
def dokumenter():
    if 'brugernavn' not in session:
        return redirect('/login')
    try:
        filer = [f for f in sorted(os.listdir(DOCS_DIR)) if f.lower().endswith(".pdf")]
    except FileNotFoundError:
        filer = []
    return render_template("dokumenter.html", filer=filer, admin=session['brugernavn'].lower() == 'admin')

@app.route("/doc/<path:filename>")
def serve_pdf(filename):
    if 'brugernavn' not in session:
        return redirect('/login')

    safe_path = safe_join(DOCS_DIR, filename)  # beskytter mod path traversal
    if not safe_path or not os.path.isfile(safe_path):
        return "Filen findes ikke", 404

    return send_from_directory(DOCS_DIR, filename, mimetype="application/pdf", as_attachment=False)

@app.route("/iot_toggle", methods=["POST"])
def iot_toggle():
    status = request.form.get("iot_vaskemaskine", "nej")
    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("UPDATE indstillinger SET vaerdi = %s WHERE navn = 'iot_vaskemaskine'", (status,))
    conn.commit()
    conn.close()
    return redirect("/admin")

    # kiosken

@app.route('/direkte', methods=['GET', 'POST'])
def direkte():
    from pytz import timezone as _tz
    TZ = _tz("Europe/Copenhagen")

    nu = datetime.now(TZ)  # dansk tid
    dato = nu.strftime('%Y-%m-%d')      # ISO (brug i DB-queries)
    vis_dato = nu.strftime('%d-%m-%Y')  # til visning i UI
    klokkeslaet = nu.strftime('%H:%M')

    conn = get_db_connection()
    cur = conn.cursor()

    # Hent definerede vasketider (bruges til select i template)
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider_raw = cur.fetchall()
    # Lav string-keys (så de matcher template som forventer str(slot_index))
    tider = [(str(int(r[0])), r[1]) for r in tider_raw]

    fejl = ""

    if request.method == 'POST':
        slot = request.form.get("tid")
        # Vi forventer slot som string (fx "0","1","2","3"). Konverter ved behov.
        try:
            slot_int = int(slot)
            slot_key = str(slot_int)
        except Exception:
            fejl = "Ugyldigt slot"
            slot_key = None

        if slot_key:
            # Er tiden taget?
            cur.execute(
                "SELECT brugernavn FROM bookinger WHERE dato_rigtig = %s AND slot_index = %s",
                (dato, slot_int)
            )
            eksisterende = cur.fetchone()
            if eksisterende:
                fejl = f"Tiden er allerede booket af {eksisterende[0]}"
            else:
                # max 2 tider pr. dag for 'direkte'
                cur.execute(
                    "SELECT COUNT(*) FROM bookinger WHERE brugernavn = 'direkte' AND dato_rigtig = %s",
                    (dato,)
                )
                antal = cur.fetchone()[0]
                if antal >= 2:
                    fejl = "Direkte har allerede booket 2 tider i dag"
                else:
                    # opret booking
                    cur.execute(
                        "INSERT INTO bookinger (brugernavn, dato_rigtig, slot_index) VALUES (%s, %s, %s)",
                        ('direkte', dato, slot_int)
                    )
                    # Opdater statistik (sikker tabel-creation hvis nødvendigt)
                    cur.execute("""
                        CREATE TABLE IF NOT EXISTS statistik (
                            dato DATE NOT NULL,
                            type TEXT NOT NULL,
                            antal INT DEFAULT 0,
                            PRIMARY KEY (dato, type)
                        )
                    """)
                    cur.execute("""
                        INSERT INTO statistik (dato, type, antal)
                        VALUES (%s, 'direktetid', 1)
                        ON CONFLICT (dato, type) DO UPDATE
                        SET antal = statistik.antal + 1
                    """, (dato,))
                    conn.commit()

    # Hent hvilke slots der er booket i dag
    cur.execute("SELECT slot_index, brugernavn FROM bookinger WHERE dato_rigtig = %s", (dato,))
    rows = cur.fetchall()
    # Debug (fjern senere): viser DB-rækker i server-log
    current_app.logger.debug("DEBUG /direkte bookede rows: %r", rows)

    # Byg mapping med STRING-nøgler så den matcher `tider`/template
    bookede = { str(int(slot_index)): brugernavn for slot_index, brugernavn in rows }

    cur.close()
    conn.close()

    return render_template(
        "direkte.html",
        dato=vis_dato,
        tider=tider,        # liste af (slot_str, tekst)
        bookede=bookede,    # dict med string keys: { "0": "navn", ... }
        klokkeslaet=klokkeslaet,
        fejl=fejl
    )

# ===============
# statestik
# ===============

@app.route("/statistik")
def statistik():
    # Kun admin
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    conn = get_db_connection()
    cur = conn.cursor()

    try:
        # Sørg for hjælpe-tabeller (ændrer ikke eksisterende data)
        ensure_stat_support_tables(cur)
        conn.commit()

        # Periode: 30 dage bagud inkl. i dag
        cur.execute("SELECT (CURRENT_DATE - INTERVAL '29 days')::date, CURRENT_DATE::date")
        dfrom, dto = cur.fetchone()
        # antal kalenderdage i vinduet
        day_count = (dto - dfrom).days + 1
        # slots per dag i din løsning
        SLOTS_PER_DAY = 4

        # ========== KPI (30 dage) ==========
        # Unikke (dato, slot) der er brugt af rigtige brugere (ikke 'service')
        cur.execute("""
            SELECT COUNT(DISTINCT (b.dato_rigtig::date, CAST(b.slot_index AS int)))
            FROM bookinger b
            WHERE b.dato_rigtig::date BETWEEN %s AND %s
              AND COALESCE(b.brugernavn,'') <> 'service'
        """, (dfrom, dto))
        used_slots_30d = int(cur.fetchone()[0] or 0)

        # Ikke brugt = auto_remove-hændelser i booking_log
        cur.execute("""
            SELECT COUNT(*)
            FROM booking_log
            WHERE handling = 'auto_remove'
              AND tidspunkt::date BETWEEN %s AND %s
        """, (dfrom, dto))
        not_used_30d = int(cur.fetchone()[0] or 0)

        total_slots_30d = SLOTS_PER_DAY * day_count
        utilization_30d = round(100.0 * used_slots_30d / max(1, total_slots_30d), 1)

        # KPI: aktive bookinger næste 14 dage, unikke brugere, service-blokke, direkte
        cur.execute("""
            SELECT COUNT(*)
            FROM bookinger
            WHERE dato_rigtig BETWEEN CURRENT_DATE AND CURRENT_DATE + INTERVAL '14 days'
        """)
        aktive_14 = int(cur.fetchone()[0] or 0)

        cur.execute("""
            SELECT COUNT(DISTINCT LOWER(brugernavn))
            FROM bookinger
            WHERE dato_rigtig BETWEEN CURRENT_DATE AND CURRENT_DATE + INTERVAL '14 days'
              AND COALESCE(brugernavn,'') <> 'service'
        """)
        unikke_brugere = int(cur.fetchone()[0] or 0)

        # total_direkte – først statistik, ellers fallback på bookinger
        cur.execute("SELECT COALESCE(SUM(antal),0) FROM statistik WHERE type='direktetid'")
        total_direkte = int(cur.fetchone()[0] or 0)
        if total_direkte == 0:
            cur.execute("SELECT COUNT(*) FROM bookinger WHERE brugernavn='direkte'")
            total_direkte = int(cur.fetchone()[0] or 0)

        cur.execute("""
            SELECT COUNT(*)
            FROM bookinger
            WHERE dato_rigtig BETWEEN CURRENT_DATE AND CURRENT_DATE + INTERVAL '14 days'
              AND brugernavn = 'service'
        """)
        service_blok = int(cur.fetchone()[0] or 0)

        kpi = {
            'aktive_14': aktive_14,
            'unikke_brugere': unikke_brugere,
            'total_direkte': total_direkte,
            'service_blok': service_blok,
            'bookinger_30d': used_slots_30d,
            'ikke_brugt_30d': not_used_30d,
            'udnyttelse_30d_pct': utilization_30d
        }

        # Kæde-KPI’er (30 dage)
        cur.execute("""
            SELECT COUNT(*), COALESCE(AVG(score)::numeric,0)
            FROM direkte_kæder
            WHERE created_at::date BETWEEN %s AND %s
        """, (dfrom, dto))
        row = cur.fetchone() or (0, 0)
        kpi['kaeder_30d'] = int(row[0] or 0)
        kpi['kaede_avg_score'] = round(float(row[1] or 0.0), 1)

        # ========== Ikke brugte bookinger (tabel) ==========
        cur.execute("""
            SELECT to_char(dato,'YYYY-MM-DD') AS d,
                   slot_index::text,
                   COALESCE(brugernavn,'') AS u
            FROM booking_log
            WHERE handling='auto_remove'
              AND tidspunkt::date BETWEEN %s AND %s
            ORDER BY tidspunkt DESC
            LIMIT 30
        """, (dfrom, dto))
        ikke_bruge_tabel = [
            {'dato': r[0], 'slot': r[1], 'brugernavn': r[2]}
            for r in (cur.fetchall() or [])
        ]

        # ========== Kæder (Direkte→Bruger) ==========
        cur.execute("""
            SELECT to_char(created_at,'YYYY-MM-DD') AS d,
                   direkte_slot, bruger_slot, bruger, score,
                   COALESCE(note,''), created_at
            FROM direkte_kæder
            ORDER BY created_at DESC
            LIMIT 30
        """)
        kaeder_list = [
            (r[0], r[1], r[2], r[3], int(r[4] or 0), r[5], r[6])
            for r in (cur.fetchall() or [])
        ]

        # ========== Ændringslog (seneste 100) ==========
        cur.execute("""
            SELECT id, brugernavn, handling, dato, slot_index, tidspunkt
            FROM booking_log
            ORDER BY tidspunkt DESC
            LIMIT 100
        """)
        rows = cur.fetchall() or []
        from datetime import date as _date, datetime as _dt
        booking_log = []
        for (lid, bnavn, handling, d, slot, ts) in rows:
            d_fmt = d.strftime('%d-%m-%Y') if isinstance(d, (_date, _dt)) else (d or '')
            ts_fmt = ts.strftime('%d-%m-%Y %H:%M:%S') if isinstance(ts, _dt) else (ts or '')
            booking_log.append((lid, bnavn, handling, d_fmt, slot, ts_fmt))

        # ========== Systemstatus (Miele) ==========
        miele_status, miele_opdateret, miele_logs = 'Ukendt', '—', 0
        try:
            cur.execute("""
                SELECT status, remaining_time, opdateret
                FROM miele_status
                ORDER BY opdateret DESC
                LIMIT 1
            """)
            r = cur.fetchone()
            if r:
                miele_status = r[0] or 'Ukendt'
                miele_opdateret = r[2].strftime('%Y-%m-%d %H:%M:%S') if r[2] else '—'
        except Exception:
            pass
        try:
            cur.execute("SELECT COUNT(*) FROM miele_activity")
            miele_logs = int(cur.fetchone()[0] or 0)
        except Exception:
            try:
                cur.execute("SELECT COUNT(*) FROM miele_status")
                miele_logs = int(cur.fetchone()[0] or 0)
            except Exception:
                miele_logs = 0

        # ========== Login-aktivitet (30 dage) ==========
        cur.execute("""
            SELECT to_char(tidspunkt,'YYYY-MM-DD HH24:MI') AS ts,
                brugernavn, status,
                -- RÅ IP + FULD UA + HASH
                COALESCE(ip,''), COALESCE(enhed,''), COALESCE(ip_hash,''),
                -- Udledte UA/geo felter
                COALESCE(ua_browser,''), COALESCE(ua_os,''), COALESCE(ua_device,''),
                COALESCE(ip_country,''), COALESCE(ip_region,''), COALESCE(ip_city,''), COALESCE(ip_org,''), COALESCE(ip_is_datacenter,false),
                CASE WHEN LOWER(status) = 'ok' THEN 'OK' ELSE 'Afvist' END AS indikator_label,
                CASE WHEN LOWER(status) = 'ok' THEN 1 ELSE 0 END AS indikator_ok
            FROM login_log
            WHERE tidspunkt::date BETWEEN %s AND %s
            ORDER BY tidspunkt DESC
        """, (dfrom, dto))

        rows = cur.fetchall() or []
        logins_struct = [{
            "tidspunkt": r[0],
            "brugernavn": r[1],
            "status": r[2],
            "ip": r[3],
            "enhed": r[4],            # fuld User-Agent
            "ip_hash": r[5],
            "ua_browser": r[6],
            "ua_os": r[7],
            "ua_device": r[8],
            "ip_country": r[9],
            "ip_region": r[10],
            "ip_city": r[11],
            "ip_org": r[12],
            "ip_is_datacenter": bool(r[13]),
            "indikator_label": r[14],
            "indikator_ok": bool(r[15]),
        } for r in rows]

        # ========== Forsøg (30 dage) ==========
        cur.execute("""
           SELECT ts::date AS dato, brugernavn, COUNT(*) AS forsog
           FROM booking_attempts
           WHERE ts::date BETWEEN %s AND %s
           GROUP BY ts::date, brugernavn
           ORDER BY dato DESC, brugernavn
        """, (dfrom, dto))
        attempts_by_user_day = [{
            "dato": r[0].strftime('%Y-%m-%d'),
            "brugernavn": r[1],
            "forsøg": int(r[2])
        } for r in (cur.fetchall() or [])]

        cur.execute("""
           SELECT ts::date AS dato, brugernavn, COUNT(*) AS forsog
           FROM booking_attempts
           WHERE ts::date BETWEEN %s AND %s
           GROUP BY ts::date, brugernavn
           HAVING COUNT(*) > 2
           ORDER BY dato DESC, forsog DESC
        """, (dfrom, dto))
        attempts_over_2 = [{
            "dato": r[0].strftime('%Y-%m-%d'),
            "brugernavn": r[1],
            "forsøg": int(r[2])
        } for r in (cur.fetchall() or [])]

        # ========== Direkte pr. dag (graf) ==========
        cur.execute("""
            SELECT dato, antal
            FROM statistik
            WHERE type='direktetid'
              AND dato BETWEEN %s AND %s
            ORDER BY dato DESC
            LIMIT 30
        """, (dfrom, dto))
        direkte_pr_dag = cur.fetchall()
        if not direkte_pr_dag:
            cur.execute("""
                SELECT dato_rigtig::date AS dato, COUNT(*) AS antal
                FROM bookinger
                WHERE brugernavn='direkte'
                  AND dato_rigtig::date BETWEEN %s AND %s
                GROUP BY dato_rigtig::date
                ORDER BY dato DESC
                LIMIT 30
            """, (dfrom, dto))
            direkte_pr_dag = cur.fetchall()
        direkte_pr_dag = [
            ((d.strftime('%Y-%m-%d') if hasattr(d, 'strftime') else str(d)), int(a or 0))
            for (d, a) in (direkte_pr_dag or [])
        ]

        # ========== Brugsmønstre – slots ==========
        # Hent brugte pr. slot i perioden
        cur.execute("""
            SELECT CAST(b.slot_index AS int) AS s,
                   COUNT(DISTINCT (b.dato_rigtig::date, CAST(b.slot_index AS int))) AS cnt
            FROM bookinger b
            WHERE b.dato_rigtig::date BETWEEN %s AND %s
              AND COALESCE(b.brugernavn,'') <> 'service'
            GROUP BY s
            ORDER BY s
        """, (dfrom, dto))
        rows = cur.fetchall() or []
        used_per_slot = {int(s): int(cnt) for (s, cnt) in rows}
        slot_overblik = []
        for s in range(0, SLOTS_PER_DAY):
            used = used_per_slot.get(s, 0)
            possible = day_count  # ét slot pr. dag
            not_used = max(0, possible - used)
            pct = round(100.0 * used / max(1, possible), 1)
            slot_overblik.append({
                "slot": f"{s}",
                "brugte": used,
                "ikke_brugt": not_used,
                "udnyttelse_pct": pct
            })

        # ========== Brugsmønstre – ugedage ==========
        # Find antal kalenderdage pr. ugedag i vinduet
        cur.execute("""
            WITH days AS (
              SELECT generate_series(%s::date, %s::date, INTERVAL '1 day')::date AS d
            )
            SELECT EXTRACT(DOW FROM d)::int AS dow, COUNT(*) AS ndays
            FROM days
            GROUP BY EXTRACT(DOW FROM d)::int
            ORDER BY 1
        """, (dfrom, dto))
        ndays_map = {int(dow): int(n) for (dow, n) in (cur.fetchall() or [])}

        # Anvendte (dato,slot) per ugedag (distinct for at undgå dobbelttælling)
        cur.execute("""
            SELECT EXTRACT(DOW FROM b.dato_rigtig)::int AS dow,
                   COUNT(DISTINCT (b.dato_rigtig::date, CAST(b.slot_index AS int))) AS cnt
            FROM bookinger b
            WHERE b.dato_rigtig::date BETWEEN %s AND %s
              AND COALESCE(b.brugernavn,'') <> 'service'
            GROUP BY EXTRACT(DOW FROM b.dato_rigtig)::int
            ORDER BY 1
        """, (dfrom, dto))
        used_map = {int(dow): int(cnt) for (dow, cnt) in (cur.fetchall() or [])}

        # Postgres: 0=Sunday..6=Saturday
        dow_labels = {0:"Søndag", 1:"Mandag", 2:"Tirsdag", 3:"Onsdag", 4:"Torsdag", 5:"Fredag", 6:"Lørdag"}
        weekday_overblik = []
        for pg_dow in range(0,7):
            label = dow_labels.get(pg_dow, str(pg_dow))
            used = used_map.get(pg_dow, 0)
            ndays = ndays_map.get(pg_dow, 0)
            possible = ndays * SLOTS_PER_DAY
            not_used = max(0, possible - used)
            pct = round(100.0 * used / max(1, possible), 1)
            weekday_overblik.append({
                "dag": label,
                "brugte": used,
                "ikke_brugt": not_used,
                "udnyttelse_pct": pct
            })

        # ========== Bruger-mønstre (no-show-rate Top 15) ==========
        cur.execute("""
            WITH total AS (
              SELECT LOWER(brugernavn) AS u, COUNT(*) AS bookinger
              FROM bookinger
              WHERE dato_rigtig::date BETWEEN %s AND %s
                AND COALESCE(brugernavn,'') NOT IN ('service','direkte')
              GROUP BY LOWER(brugernavn)
            ),
            noshow AS (
              SELECT LOWER(brugernavn) AS u, COUNT(*) AS ikke
              FROM booking_log
              WHERE handling='auto_remove'
                AND tidspunkt::date BETWEEN %s AND %s
              GROUP BY LOWER(brugernavn)
            )
            SELECT t.u AS brugernavn,
                   COALESCE(t.bookinger,0) AS bookinger,
                   COALESCE(n.ikke,0) AS ikke_brugt,
                   CASE
                     WHEN COALESCE(t.bookinger,0) = 0 THEN NULL
                     ELSE ROUND(100.0 * COALESCE(n.ikke,0) / t.bookinger, 1)
                   END AS rate
            FROM total t
            LEFT JOIN noshow n ON n.u = t.u
            WHERE COALESCE(t.bookinger,0) > 0
            ORDER BY rate DESC NULLS LAST, ikke_brugt DESC, bookinger DESC
            LIMIT 15
        """, (dfrom, dto, dfrom, dto))
        bruger_moenstre = [{
            "brugernavn": r[0],
            "bookinger": int(r[1] or 0),
            "ikke_brugt": int(r[2] or 0),
            "ikke_brugt_rate": float(r[3] or 0.0)
        } for r in (cur.fetchall() or [])]

        # ========== Retention for login_log (90 dage) ==========
        cur.execute("DELETE FROM login_log WHERE tidspunkt < NOW() - INTERVAL '90 days'")
        conn.commit()

    except Exception as e:
        conn.rollback()
        raise  # lad Flask logge fejlen, så vi kan se linjen i loggen
    finally:
        try:
            cur.close()
            conn.close()
        except Exception:
            pass

    return render_template(
        "statistik.html",
        # KPI & status
        kpi=kpi,
        miele_status=miele_status,
        miele_opdateret=miele_opdateret,
        miele_logs=miele_logs,
        total_direkte=total_direkte,
        # Side 1
        direkte_pr_dag=direkte_pr_dag,
        ikke_bruge_tabel=ikke_bruge_tabel,
        kaeder=kaeder_list,
        # Side 2
        slot_overblik=slot_overblik,
        weekday_overblik=weekday_overblik,
        bruger_moenstre=bruger_moenstre,
        # Side 3
        logins=logins_struct,
        booking_log=booking_log,
        attempts_by_user_day=attempts_by_user_day,
        attempts_over_2=attempts_over_2
    )

@app.get("/statistik_data")
def statistik_data():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return jsonify({"error": "Unauthorized"}), 401

    days = request.args.get("days", 30, type=int)
    if days is None:
        days = 30
    days = max(1, min(days, 90))

    conn = get_db_connection(); cur = conn.cursor()

    # Totals
    cur.execute("""
        WITH d AS (
          SELECT (CURRENT_DATE - (%s::int - 1))::date AS start_d,
                 CURRENT_DATE::date AS end_d
        )
        SELECT
          (SELECT COUNT(*) FROM bookinger b, d
            WHERE b.dato_rigtig BETWEEN d.start_d AND d.end_d) AS total_bookings,
          (SELECT COUNT(*) FROM bookinger b, d
            WHERE b.dato_rigtig BETWEEN d.start_d AND d.end_d
              AND COALESCE(b.sub_slot,'full')='full'
              AND b.brugernavn IS NOT NULL) AS full_cnt,
          (SELECT COUNT(*) FROM bookinger b, d
            WHERE b.dato_rigtig BETWEEN d.start_d AND d.end_d
              AND b.sub_slot IN ('early','late')
              AND b.brugernavn IS NOT NULL) AS half_cnt,
          (SELECT COUNT(*) FROM booking_log bl, d
            WHERE bl.tidspunkt::date BETWEEN d.start_d AND d.end_d
              AND (bl.handling ILIKE 'cancel%%' OR bl.handling ILIKE 'aflys%%')) AS cancel_cnt,
          (SELECT COUNT(*) FROM booking_log bl, d
            WHERE bl.tidspunkt::date BETWEEN d.start_d AND d.end_d
              AND (bl.handling ILIKE 'auto_remove%%'
                   OR bl.handling ILIKE 'auto_release%%'
                   OR bl.handling ILIKE 'expired%%')) AS auto_removed_cnt
    """, (days,))
    row = cur.fetchone() or (0,0,0,0,0)
    totals = {
        "total_bookings": int(row[0] or 0),
        "full":           int(row[1] or 0),
        "half":           int(row[2] or 0),
        "cancellations":  int(row[3] or 0),
        "auto_removed":   int(row[4] or 0),
    }

    # Per slot (samlet/early/late)
    cur.execute("""
        WITH d AS (
          SELECT (CURRENT_DATE - (%s::int - 1))::date AS start_d,
                 CURRENT_DATE::date AS end_d
        )
        SELECT
          COALESCE(v.tekst, CONCAT('Slot ', CAST(b.slot_index AS INT))) AS slot_text,
          CAST(b.slot_index AS INT) AS slot_int,
          COUNT(*) FILTER (WHERE b.brugernavn IS NOT NULL) AS count_all,
          COUNT(*) FILTER (WHERE b.sub_slot='early' AND b.brugernavn IS NOT NULL) AS count_early,
          COUNT(*) FILTER (WHERE b.sub_slot='late'  AND b.brugernavn IS NOT NULL) AS count_late
        FROM bookinger b
        LEFT JOIN vasketider v ON v.slot_index = CAST(b.slot_index AS INT)
        , d
        WHERE b.dato_rigtig BETWEEN d.start_d AND d.end_d
        GROUP BY slot_text, slot_int
        ORDER BY slot_int ASC
    """, (days,))
    by_slot = [{
        "slot_text": r[0],
        "slot_index": int(r[1]),
        "count_all": int(r[2] or 0),
        "count_early": int(r[3] or 0),
        "count_late": int(r[4] or 0),
    } for r in (cur.fetchall() or [])]

    # Top brugere (ekskl. service/direkte)
    cur.execute("""
        WITH d AS (
          SELECT (CURRENT_DATE - (%s::int - 1))::date AS start_d,
                 CURRENT_DATE::date AS end_d
        )
        SELECT LOWER(brugernavn) AS u, COUNT(*) AS c
        FROM bookinger b, d
        WHERE b.dato_rigtig BETWEEN d.start_d AND d.end_d
          AND b.brugernavn IS NOT NULL
          AND LOWER(b.brugernavn) NOT IN ('service','direkte')
        GROUP BY LOWER(brugernavn)
        ORDER BY c DESC, u ASC
        LIMIT 20
    """, (days,))
    by_user_top = [{"brugernavn": r[0], "count": int(r[1] or 0)} for r in (cur.fetchall() or [])]

    # Pr dag (line chart)
    cur.execute("""
        WITH d AS (
          SELECT (CURRENT_DATE - (%s::int - 1))::date AS start_d,
                 CURRENT_DATE::date AS end_d
        )
        SELECT b.dato_rigtig::date AS d, COUNT(*) AS c
        FROM bookinger b, d
        WHERE b.dato_rigtig BETWEEN d.start_d AND d.end_d
        GROUP BY b.dato_rigtig::date
        ORDER BY d ASC
    """, (days,))
    by_day = [{"dato": r[0].strftime("%Y-%m-%d"), "count": int(r[1] or 0)} for r in (cur.fetchall() or [])]

    # Pr ugedag (bar)
    cur.execute("""
        WITH d AS (
          SELECT (CURRENT_DATE - (%s::int - 1))::date AS start_d,
                 CURRENT_DATE::date AS end_d
        )
        SELECT
           EXTRACT(DOW FROM b.dato_rigtig)::int AS dow,
           COUNT(*) AS c
        FROM bookinger b, d
        WHERE b.dato_rigtig BETWEEN d.start_d AND d.end_d
        GROUP BY EXTRACT(DOW FROM b.dato_rigtig)
        ORDER BY dow ASC
    """, (days,))
    wk_map = ["Sø","Ma","Ti","On","To","Fr","Lø"]
    by_weekday = [{"weekday": int(r[0]),
                   "weekday_dk": wk_map[int(r[0])%7],
                   "count": int(r[1] or 0)} for r in (cur.fetchall() or [])]

    conn.close()
    return jsonify({
        "totals": totals,
        "by_slot": by_slot,
        "by_user_top": by_user_top,
        "by_day": by_day,
        "by_weekday": by_weekday
    })

@app.route("/download_valg")
def download_valg():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')
    return render_template("download_statistik.html")

@app.route('/slet_loginforsøg', methods=['POST'])
def slet_loginforsøg():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    log_id = request.form.get("log_id")
    if not log_id:
        return redirect("/statistik")

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("DELETE FROM login_log WHERE id = %s", (log_id,))
    conn.commit()
    conn.close()

    return redirect("/statistik")

@app.route("/download_statistik_pdf", methods=["POST"])
def download_statistik_pdf():
    from fpdf import FPDF

    # Formular-valg (fallback: hent ALT hvis intet er sat)
    include_login = request.form.get("login_log") == "on"
    include_booking = request.form.get("booking_log") == "on"
    include_all = request.form.get("alle") == "on"
    date_from = request.form.get("fra_dato", "").strip()   # valgfrit, format: YYYY-MM-DD
    date_to   = request.form.get("til_dato", "").strip()   # valgfrit, format: YYYY-MM-DD

    if include_all or (not include_login and not include_booking):
        include_login = True
        include_booking = True

    # Hjælpere
    def add_header(pdf, title):
        pdf.set_font("Arial", "B", 14)
        pdf.cell(0, 10, latin1_sikker_tekst(title), ln=True)
        pdf.set_font("Arial", "", 10)

    def safe_multiline(pdf, text, h=6):
        pdf.multi_cell(0, h, latin1_sikker_tekst(str(text)))

    def maybe_new_page(pdf, room=10):
        # Simpelt “page break” tjek
        if pdf.get_y() > (pdf.h - 20 - room):
            pdf.add_page()

    # Byg simpel WHERE for datointerval
    where_login = []
    where_booking = []
    params_login = []
    params_booking = []

    if date_from:
        where_login.append("tidspunkt::date >= %s")
        where_booking.append("tidspunkt::date >= %s")
        params_login.append(date_from)
        params_booking.append(date_from)
    if date_to:
        where_login.append("tidspunkt::date <= %s")
        where_booking.append("tidspunkt::date <= %s")
        params_login.append(date_to)
        params_booking.append(date_to)

    if where_login:
        where_login_sql = "WHERE " + " AND ".join(where_login)
    else:
        where_login_sql = ""
    if where_booking:
        where_booking_sql = "WHERE " + " AND ".join(where_booking)
    else:
        where_booking_sql = ""

    # Hent data
    conn = get_db_connection()
    cur = conn.cursor()

    # For statuslinje i toppen
    genereret = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    # PDF setup
    pdf = FPDF()
    pdf.add_page()
    pdf.set_auto_page_break(auto=False, margin=15)
    pdf.set_font("Arial", size=10)

    # Titel
    pdf.set_font("Arial", "B", 16)
    pdf.cell(0, 10, latin1_sikker_tekst("Vasketider – Logudtræk"), ln=True)
    pdf.set_font("Arial", "", 10)
    pdf.cell(0, 8, latin1_sikker_tekst(f"Genereret: {genereret}"), ln=True)
    if date_from or date_to:
        pdf.cell(0, 8, latin1_sikker_tekst(f"Filter: {date_from or '—'} til {date_to or '—'}"), ln=True)
    else:
        pdf.cell(0, 8, latin1_sikker_tekst("Filter: Alle datoer"), ln=True)
    pdf.ln(2)

    # ====== BOOKING_LOG (ændringsbookninger) ======
    if include_booking:
        add_header(pdf, "Ændringsbookninger (booking_log)")
        # Tælling
        cur.execute(f"SELECT COUNT(*) FROM booking_log {where_booking_sql}", params_booking)
        total_booking = cur.fetchone()[0] or 0
        pdf.cell(0, 6, latin1_sikker_tekst(f"Antal poster: {total_booking}"), ln=True)
        pdf.ln(1)

        # Kolonneoverskrift
        pdf.set_font("Arial", "B", 10)
        pdf.cell(35, 6, "Tidspunkt", border=0)
        pdf.cell(25, 6, "Bruger", border=0)
        pdf.cell(40, 6, "Handling", border=0)
        pdf.cell(30, 6, "Dato", border=0)
        pdf.cell(15, 6, "Slot", border=0)
        pdf.ln(6)
        pdf.set_font("Arial", "", 10)

        # Strøm igennem alle rækker (DESC for nyeste først)
        cur.execute(f"""
            SELECT tidspunkt, brugernavn, handling, dato, slot_index
            FROM booking_log
            {where_booking_sql}
            ORDER BY tidspunkt DESC
        """, params_booking)

        for (ts, user, handling, d, slot) in cur.fetchall():
            maybe_new_page(pdf, room=20)
            ts_str = ts.strftime('%Y-%m-%d %H:%M:%S') if ts else ""
            d_str = d.strftime('%Y-%m-%d') if d else ""
            # korte celler (hold det kompakt)
            pdf.cell(35, 6, latin1_sikker_tekst(ts_str))
            pdf.cell(25, 6, latin1_sikker_tekst(user or ""))
            pdf.cell(40, 6, latin1_sikker_tekst(handling or ""))
            pdf.cell(30, 6, latin1_sikker_tekst(d_str))
            pdf.cell(15, 6, latin1_sikker_tekst(str(slot) if slot is not None else ""))
            pdf.ln(6)

        pdf.ln(4)

    # ====== LOGIN_LOG ======
    if include_login:
        add_header(pdf, "Loginforsøg (login_log)")
        # Tælling
        cur.execute(f"SELECT COUNT(*) FROM login_log {where_login_sql}", params_login)
        total_login = cur.fetchone()[0] or 0
        pdf.cell(0, 6, latin1_sikker_tekst(f"Antal poster: {total_login}"), ln=True)
        pdf.ln(1)

        # Kolonneoverskrift
        pdf.set_font("Arial", "B", 10)
        pdf.cell(35, 6, "Tidspunkt", border=0)
        pdf.cell(25, 6, "Bruger", border=0)
        pdf.cell(28, 6, "IP", border=0)
        pdf.cell(20, 6, "Status", border=0)
        pdf.cell(0, 6, "Enhed", border=0)
        pdf.ln(6)
        pdf.set_font("Arial", "", 10)

        # Strøm igennem alle rækker (DESC)
        cur.execute(f"""
            SELECT tidspunkt, brugernavn, ip, status, enhed
            FROM login_log
            {where_login_sql}
            ORDER BY tidspunkt DESC
        """, params_login)

        for (ts, user, ip, status, ua) in cur.fetchall():
            maybe_new_page(pdf, room=24)
            ts_str = ts.strftime('%Y-%m-%d %H:%M:%S') if ts else ""
            # Først faste felter på én linje…
            pdf.cell(35, 6, latin1_sikker_tekst(ts_str))
            pdf.cell(25, 6, latin1_sikker_tekst(user or ""))
            pdf.cell(28, 6, latin1_sikker_tekst(ip or ""))
            pdf.cell(20, 6, latin1_sikker_tekst(status or ""))
            pdf.ln(6)
            # … så User-Agent på egen linje (multiline), indrykket
            x = pdf.get_x(); y = pdf.get_y()
            pdf.set_x(35 + 25 + 28 + 20 + 4)  # lille indrykning
            safe_multiline(pdf, ua or "")
            # lille luft mellem poster
            pdf.ln(1)

    conn.close()

    # Svar
    response = make_response(pdf.output(dest="S").encode("latin1"))
    response.headers["Content-Type"] = "application/pdf"
    response.headers["Content-Disposition"] = "attachment; filename=statistik_logs.pdf"
    return response

@app.route("/slet_bookinglog", methods=["POST"])
def slet_bookinglog():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    log_id = request.form.get("log_id")
    if not log_id:
        return redirect("/statistik")

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("DELETE FROM booking_log WHERE id = %s", (log_id,))
    conn.commit()
    conn.close()

    return redirect("/statistik")

@app.route("/regler")
def regler():
    next_url = request.args.get("next", "/index")
    return render_template("regler.html", next_url=next_url)

@app.route("/regler/direkte")
def regler_direkte():
    return render_template("regler.html", next_url="/direkte")