from flask import Flask, render_template, request, redirect, session, jsonify, Response, url_for, g, flash
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
    from psycopg.errors import UniqueViolation as IntegrityError  # psycopg3
except Exception:
    try:
        from psycopg2 import IntegrityError  # psycopg2
    except Exception:
        IntegrityError = Exception
from flask import current_app
from functools import wraps
from flask import abort
import os
import secrets
import pytz
import smtplib
import hashlib
import threading
import time
from email.mime.text import MIMEText
from twilio.rest import Client
from werkzeug.utils import secure_filename

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

CITY_CANDIDATES = [
    "/config/geo/GeoLite2-City.mmdb",  # Home Assistant
    "/app/geo/GeoLite2-City.mmdb"  # Render.com
]
ASN_CANDIDATES = [
    "/config/geo/GeoLite2-ASN.mmdb",
    "/app/geo/GeoLite2-ASN.mmdb"
]

CITY_MMDB = _first_existing(CITY_CANDIDATES)
ASN_MMDB  = _first_existing(ASN_CANDIDATES)

_city_reader = geoip2.database.Reader(CITY_MMDB) if CITY_MMDB else None
_asn_reader  = geoip2.database.Reader(ASN_MMDB)  if ASN_MMDB else None
ALLOWED_EXTENSIONS = {'pdf'}
CPH = timezone("Europe/Copenhagen")
UGEDAGE_DK = ['Mandag', 'Tirsdag', 'Onsdag', 'Torsdag', 'Fredag', 'Lørdag', 'Søndag']
DATABASE_URL = os.environ.get("DATABASE_URL") or "din_default_postgres_url"

limiter = Limiter(
    key_func=get_remote_address,
    default_limits=[]
)
limiter.init_app(app)

# Definer starter en funktion i python

def get_db_connection():
    return psycopg.connect(DATABASE_URL, sslmode='require')

def init_db():
    try:
        conn = get_db_connection()
        cur = conn.cursor()

        cur.execute("""
            CREATE TABLE IF NOT EXISTS miele_activity (
                id SERIAL PRIMARY KEY,
                ts TIMESTAMP NOT NULL,
                status TEXT NOT NULL
            );
        """)
        cur.execute("CREATE INDEX IF NOT EXISTS idx_miele_activity_ts ON miele_activity(ts)")

        # booking_log (ændringslog for bookinger)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS booking_log (
                id SERIAL PRIMARY KEY,
                brugernavn TEXT,
                handling TEXT,              -- fx 'create', 'auto_remove', 'complete', 'fejl:max2' mv.
                dato DATE,
                slot_index INT,
                booking_type TEXT,
                resultat TEXT,
                tidspunkt TIMESTAMP DEFAULT NOW()
            )
        """)

        cur.execute("""
            CREATE INDEX IF NOT EXISTS ix_booking_log_time
            ON booking_log(tidspunkt DESC);
        """)

        # --- SCHEMA PATCHES (sikrer kolonner din kode bruger) ---
        # bookinger
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS status TEXT DEFAULT 'booked'")
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS booking_type TEXT")      # 'full'|'direkte'|'split_before'|'split_after' etc.
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS sub_slot TEXT")          # 'early'|'late' eller NULL
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS created_at TIMESTAMP DEFAULT NOW()")
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS start_ts TIMESTAMP")
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS end_ts TIMESTAMP")
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS activation_required BOOLEAN DEFAULT FALSE")
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS activation_deadline TIMESTAMP")
        cur.execute("ALTER TABLE IF EXISTS bookinger ADD COLUMN IF NOT EXISTS activated_at TIMESTAMP")

        # booking_attempts (bruges flere steder)
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

        # login_log (så ip_hash m.fl. findes)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS login_log (
                id SERIAL PRIMARY KEY,
                brugernavn TEXT,
                tidspunkt TIMESTAMP DEFAULT NOW(),
                status TEXT,
                ip TEXT,
                enhed TEXT,
                ua_browser TEXT,
                ua_os TEXT,
                ua_device TEXT,
                ip_hash TEXT,
                ip_country TEXT,
                ip_region TEXT,
                ip_city TEXT,
                ip_org TEXT,
                ip_is_datacenter BOOLEAN DEFAULT FALSE
            )
        """)
        conn.commit()
        conn.close()
        print("✅ DB-init færdig")
    except Exception as e:
        try: conn.close()
        except: pass
        print("⚠️ DB-init fejl:", e)

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

def local_geo(ip: str):
    country = region = city = org = ""
    is_dc = False
    if _city_reader:
        try:
            c = _city_reader.city(ip)
            country = c.country.iso_code or ""
            region  = (c.subdivisions[0].names.get("en","") if c.subdivisions else "")
            city    = c.city.name or ""
        except Exception:
            pass
    if _asn_reader:
        try:
            a = _asn_reader.asn(ip)
            org = a.autonomous_system_organization or ""
            dc_keywords = ("Amazon","Google","Microsoft","DigitalOcean","OVH","Hetzner","Akamai","Cloudflare")
            is_dc = any(k.lower() in (org or "").lower() for k in dc_keywords)
        except Exception:
            pass
    return {"country": country, "region": region, "city": city, "org": org, "is_dc": is_dc}

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

def send_email(modtager, emne, besked):
    afsender = "hornsbergmorten@gmail.com"
    adgangskode = os.environ.get("Gmail_adgangskode")

    if not adgangskode:
        print("❌ Gmail adgangskode mangler i miljøvariabler!")
        return

    msg = MIMEText(besked, "plain", "utf-8")
    msg["Subject"] = emne
    msg["From"] = f"No Reply Vasketid <{afsender}>"
    msg["To"] = modtager
    msg.add_header("Reply-To", "noreply@vasketider.dk")

    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as server:
            server.login(afsender, adgangskode)
            server.sendmail(afsender, [modtager], msg.as_string())
            print(f"📧 E-mail sendt til {modtager} med emne: {emne}")
    except Exception as e:
        print(f"❌ Fejl ved afsendelse af e-mail: {e}")

def send_sms_twilio(modtager, besked):
    account_sid = os.environ.get("Twilio_SID")
    auth_token = os.environ.get("Twilio_token")
    afsender_nummer = "+13515298337"

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

# Miele UI

@app.route('/ha_webhook', methods=['POST'])
def ha_webhook():
    try:
        data = request.get_json(force=True)
        status = data.get("status", "Ukendt")
        remaining_time = data.get("remaining_time", "")
        opdateret = data.get("opdateret", datetime.now())

        # Rå status fra HA
        raw_status = str(data.get("status", "Ukendt")).strip()
        remaining_time = str(data.get("remaining_time", "")).strip()  # f.eks. "0:45:00" eller ""
        opdateret = data.get("opdateret", datetime.now())

        # Konverter streng til datetime hvis nødvendigt
        if isinstance(opdateret, str):
            try:
                opdateret = datetime.fromisoformat(opdateret)
            except ValueError:
                opdateret = datetime.now()

        # Oversæt status til dansk med set_miele_status()
        norm_status = set_miele_status(raw_status)

        # Hvis der er resttid → omregn til "xx min"
        if remaining_time:
            try:
                h, m, s = map(int, remaining_time.split(":"))
                total_min = h * 60 + m
                remaining_time = f"{total_min} min"
            except ValueError:
                pass  # Hvis formatet ikke kan parses, bevar original streng

        # Gem i DB
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
        cur.execute("INSERT INTO miele_status (status, remaining_time, opdateret) VALUES (%s, %s, %s)",
                    (norm_status, remaining_time, opdateret))
        conn.commit()
        conn.close()

        # ------------------- NYT: log "kører"-aktivitet i historik -------------------
        try:
            from pytz import timezone
            CPH_TZ = timezone("Europe/Copenhagen")
            opdt = opdateret
            if getattr(opdt, "tzinfo", None) is None:
                opdt = CPH_TZ.localize(opdt)

            # minimalt og konservativt "kører"-sæt (udvid evt. hvis nødvendigt)
            KOERENDE = {"I brug", "kørende", "vask", "hovedvask"}

            if norm_status in KOERENDE:
                conn2 = get_db_connection()
                cur2 = conn2.cursor()
                cur2.execute("""
                    CREATE TABLE IF NOT EXISTS miele_activity (
                        id SERIAL PRIMARY KEY,
                        ts TIMESTAMP NOT NULL,
                        status TEXT NOT NULL
                    )
                """)
                # (valgfrit) index – gør range-queries hurtige
                cur2.execute("CREATE INDEX IF NOT EXISTS idx_miele_activity_ts ON miele_activity(ts)")
                cur2.execute("INSERT INTO miele_activity (ts, status) VALUES (%s, %s)", (opdt, norm_status))
                conn2.commit()
                conn2.close()
        except Exception:
            # vi må ikke vælte webhook'en pga. historik – fail-silent
            try:
                conn2.close()
            except Exception:
                pass
        # ---------------------------------------------------------------------------
        
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

# Login og Logud

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

# Admin

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
    booking_id = request.form.get("booking_id")
    conn = psycopg2.connect(DATABASE_URL)
    cur = conn.cursor()
    cur.execute("DELETE FROM bookinger WHERE id = %s", (booking_id,))
    conn.commit()
    conn.close()
    return redirect("/admin")

@app.route("/admin/delete_comment", methods=["POST"])
def admin_delete_comment():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    kommentar_id = request.form.get("kommentar_id")
    conn = psycopg2.connect(DATABASE_URL)
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

# Bookninger

@app.route('/bookinger_json')
def bookinger_json():
    # Kun admin må hente statistik-feed
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    idag = datetime.today().date()

    conn = get_db_connection()
    cur = conn.cursor()

    # Hent tiderne (tekst) fra vasketider
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider = dict(cur.fetchall())  # {0: '07–11', 1: '11–15', ...}

    # Hent bookinger 14 dage frem (ingen DELETE her)
    cur.execute("""
        SELECT brugernavn, dato_rigtig, slot_index
        FROM bookinger
        WHERE dato_rigtig >= %s AND dato_rigtig <= %s
        ORDER BY dato_rigtig ASC, slot_index ASC
    """, (idag, idag + timedelta(days=14)))
    alle_14 = cur.fetchall()

    conn.close()

    result = []
    for brugernavn, dato, slot_index in alle_14:
        # behold dd-mm-YYYY så din JS-gruppering er uændret
        dato_str = dato.strftime('%d-%m-%Y')
        # robust opslag af tidstekst
        try:
            tekst = tider[int(slot_index)]
        except (KeyError, ValueError, TypeError):
            tekst = f"Slot {slot_index}"
        result.append({
            "dato": dato_str,
            "tid": tekst,
            "navn": brugernavn
        })

    return jsonify(result)

@app.post("/book")
def book_full():
    if "brugernavn" not in session:
        # Ikke logget ind
        conn = get_db_connection(); cur = conn.cursor()
        try:
            log_booking_attempt(cur, "", request.form.get("dato",""), int(request.form.get("tid", -1)), "afvist:ikke_logget_ind")
            conn.commit()
        finally:
            cur.close(); conn.close()
        # vis fejl i UI via querystring
        return redirect(url_for("login", fejl="Log ind for at booke en tid"))

    brugernavn = session["brugernavn"]
    raw_dato = request.form["dato"]  # ISO fra formen
    dato = datetime.strptime(raw_dato, "%Y-%m-%d").date()  # -> datetime.date

    tid  = int(request.form["tid"])        # 0..3
    valgt_uge = request.form.get("valgt_uge","")

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # 1) Er slot optaget?
        cur.execute("""
            SELECT
              SUM(CASE WHEN COALESCE(sub_slot,'full')='full' THEN 1 ELSE 0 END) AS fulls,
              SUM(CASE WHEN sub_slot='early' AND brugernavn IS NOT NULL THEN 1 ELSE 0 END) AS early_taken,
              SUM(CASE WHEN sub_slot='late'  AND brugernavn IS NOT NULL THEN 1 ELSE 0 END) AS late_taken
            FROM bookinger
            WHERE dato_rigtig = %s AND slot_index = %s
        """, (dato, tid))
        fulls, early_taken, late_taken = [x or 0 for x in cur.fetchone()]
        if fulls > 0 or (early_taken > 0 and late_taken > 0):
            log_booking_attempt(cur, brugernavn, dato, tid, "afvist:taget")
            conn.commit()
            # redirect med ?fejl=
            return redirect(url_for("index", uge=valgt_uge, fejl="Tiden er allerede optaget."))

        # 2) Max-regler (eksempel max 2 pr. dag)
        cur.execute("""
            SELECT COUNT(*) FROM bookinger
            WHERE dato_rigtig=%s AND LOWER(brugernavn)=LOWER(%s)
        """, (dato, brugernavn))
        if (cur.fetchone()[0] or 0) >= 2:
            log_booking_attempt(cur, brugernavn, dato, tid, "afvist:max2")
            conn.commit()
            # redirect med ?fejl=
            return redirect(url_for("index", uge=valgt_uge, fejl="Du har allerede 2 bookinger den dag."))

        # --- Opret fuld booking med aktiveringsvindue (30 min) ---
        slot_start, slot_end = slot_interval(dato, tid)
        activation_required = True
        activation_deadline = slot_start + timedelta(minutes=30)

        cur.execute("""
            INSERT INTO bookinger (
              dato_rigtig, slot_index, brugernavn,
              sub_slot, status, activation_required, activation_deadline, created_at
            )
            VALUES (%s,%s,%s,'full','pending_activation',%s,%s, NOW())
            RETURNING id
        """, (dato, tid, brugernavn, activation_required, activation_deadline))
        _ = cur.fetchone()

        # Log forsøg/succes
        log_booking_attempt(cur, brugernavn, dato, tid, "success")
        conn.commit()

        # EFTER commit: evt. kæde-registrering (best effort)
        try:
            with get_db_connection() as _c:
                registrer_kæde_hvis_nødvendigt(_c, dato_iso=dato, bruger_slot=tid, brugernavn=brugernavn)
        except Exception:
            current_app.logger.exception("Kæde-registrering fejlede (ignoreret)")

        # redirect med ?besked=
        return redirect(url_for(
            "index",
            uge=valgt_uge,
            besked="Tid booket. Start maskinen inden 30 min, ellers frigives tiden automatisk."
        ))

    except Exception as e:
        conn.rollback()
        current_app.logger.exception("BOOK FEJL")   # ← logger hele stacktrace
        try:
            log_booking_attempt(cur, brugernavn, dato, tid, f"afvist:ukendt:{e}")
            conn.commit()
        except:
            pass
        return redirect(url_for("index", uge=valgt_uge, fejl=f"DB-fejl: {str(e)}"))
    finally:
        cur.close(); conn.close()

@app.before_request
def auto_release():
    conn = get_db_connection(); cur = conn.cursor()
    try:
        now = datetime.now(CPH)
        # Markér udløbne fuld-bookinger
        cur.execute("""
            UPDATE bookinger
               SET status='expired'
             WHERE activation_required=TRUE
               AND status='pending_activation'
               AND activation_deadline < %s
        """, (now,))
        # Slet de udløbne (så slot bliver ledig)
        cur.execute("DELETE FROM bookinger WHERE status='expired'")
        conn.commit()
    finally:
        cur.close(); conn.close()

@app.post("/slet")
def slet_booking():
    if "brugernavn" not in session:
        return redirect(url_for("login"))

    brugernavn = session["brugernavn"]
    raw_dato = request.form["dato"]
    dato = datetime.strptime(raw_dato, "%Y-%m-%d").date()   # ISO -> date
    tid   = int(request.form["tid"])
    sub   = request.form.get("sub")        # None | 'early' | 'late'
    valgt_uge = request.form.get("valgt_uge","")

    conn = get_db_connection(); cur = conn.cursor()
    try:
        if sub in ("early", "late"):
            # Slet kun egen halvdel
            cur.execute("""
                DELETE FROM bookinger
                WHERE dato_rigtig=%s AND slot_index=%s AND sub_slot=%s AND LOWER(brugernavn)=LOWER(%s)
                RETURNING 1
            """, (dato, tid, sub, brugernavn))
            deleted = cur.fetchone() is not None

            # (valgfrit) ryd den anden halvdel hvis den var en tom placeholder
            if deleted:
                cur.execute("""
                    DELETE FROM bookinger
                    WHERE dato_rigtig=%s AND slot_index=%s AND sub_slot=%s AND brugernavn IS NULL
                """, (dato, tid, "late" if sub == "early" else "early"))

            conn.commit()
            if deleted:
                return redirect(url_for("index", uge=valgt_uge, besked="Din halve booking er aflyst."))
            else:
                return redirect(url_for("index", uge=valgt_uge, fejl="Ingen matchende halv-booking at aflyse."))

        else:
            # Fuld booking
            cur.execute("""
                DELETE FROM bookinger
                WHERE dato_rigtig=%s AND slot_index=%s AND LOWER(brugernavn)=LOWER(%s)
                  AND COALESCE(sub_slot,'full')='full'
                RETURNING 1
            """, (dato, tid, brugernavn))
            deleted = cur.fetchone() is not None
            conn.commit()
            if deleted:
                return redirect(url_for("index", uge=valgt_uge, besked="Din fulde booking er aflyst."))
            else:
                return redirect(url_for("index", uge=valgt_uge, fejl="Ingen matchende fuld booking at aflyse."))
    finally:
        cur.close(); conn.close()

@app.post("/book_half")
def book_half():
    if "brugernavn" not in session:
        return redirect(url_for("login"))

    brugernavn = session["brugernavn"]
    raw_dato = request.form["dato"]
    dato = datetime.strptime(raw_dato, "%Y-%m-%d").date()   # <- ISO til date-objekt
    tid   = int(request.form["tid"])
    sub   = request.form["sub"]            # 'early' eller 'late'
    valgt_uge = request.form.get("valgt_uge","")

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # Tag den ledige halvdel (bruger NULL)
        cur.execute("""
            UPDATE bookinger
               SET brugernavn=%s
             WHERE dato_rigtig=%s AND slot_index=%s AND sub_slot=%s AND brugernavn IS NULL
             RETURNING id
        """, (brugernavn, dato, tid, sub))
        row = cur.fetchone()

        if not row:
            # enten allerede snuppet eller findes ikke
            log_booking_attempt(cur, brugernavn, dato, tid, f"afvist:half_{sub}_taget")
            conn.commit()
            flash("Ups – den anden halvdel blev taget af en anden.", "error")
            return redirect(url_for("index", uge=valgt_uge))

        # Log succes
        log_booking_attempt(cur, brugernavn, dato, tid, f"success:half_{sub}")
        conn.commit()

        flash("Halv tid booket.", "success")
        return redirect(url_for("index", uge=valgt_uge))
    except Exception:
        conn.rollback()
        try:
            log_booking_attempt(cur, brugernavn, dato, tid, f"afvist:half_{sub}:ukendt")
            conn.commit()
        except:
            pass
        flash("Fejl ved booking af halv tid.", "error")
        return redirect(url_for("index", uge=valgt_uge))
    finally:
        cur.close(); conn.close()

@app.post("/book_split")
def book_split():
    if "brugernavn" not in session:
        return redirect(url_for("login"))

    brugernavn = session["brugernavn"]
    raw_dato = request.form["dato"]
    dato = datetime.strptime(raw_dato, "%Y-%m-%d").date()   # <- ISO til date-objekt
    tid    = int(request.form["tid"])
    choice = request.form["del"]            # 'early' eller 'late'
    valgt_uge = request.form.get("valgt_uge","")

    conn = get_db_connection(); cur = conn.cursor()
    try:
        # Bloker hvis der allerede findes en fuld booking på slot
        cur.execute("""
            SELECT 1 FROM bookinger
            WHERE dato_rigtig=%s AND slot_index=%s AND COALESCE(sub_slot,'full')='full'
            LIMIT 1
        """, (dato, tid))
        if cur.fetchone():
            log_booking_attempt(cur, brugernavn, dato, tid, "afvist:taget")
            conn.commit()
            flash("Slot er optaget.", "error")
            return redirect(url_for("index", uge=valgt_uge))

        # Tjek om der allerede er split igang (så vi ikke opretter 3. halvdel)
        cur.execute("""
            SELECT COUNT(*) FROM bookinger
            WHERE dato_rigtig=%s AND slot_index=%s AND COALESCE(sub_slot,'full') IN ('early','late')
        """, (dato, tid))
        if (cur.fetchone()[0] or 0) >= 2:
            log_booking_attempt(cur, brugernavn, dato, tid, "afvist:split_fyldt")
            conn.commit()
            flash("Begge halvdele er allerede optaget.", "error")
            return redirect(url_for("index", uge=valgt_uge))

        # Opret din halvdel
        cur.execute("""
            INSERT INTO bookinger (dato_rigtig, slot_index, brugernavn, sub_slot, status, activation_required, created_at)
            VALUES (%s,%s,%s,%s,'active',FALSE,NOW())
            RETURNING id
        """, (dato, tid, brugernavn, choice))
        _ = cur.fetchone()

        other = "late" if choice == "early" else "early"
        # opret/hold præcis én placeholder for mod-halvdelen
        cur.execute("""
            SELECT 1 FROM bookinger
            WHERE dato_rigtig=%s AND slot_index=%s AND sub_slot=%s
            LIMIT 1
        """, (dato, tid, other))
        if not cur.fetchone():
            cur.execute("""
                INSERT INTO bookinger (dato_rigtig, slot_index, brugernavn, sub_slot, status, activation_required, created_at)
                VALUES (%s,%s,NULL,%s,'active',FALSE,NOW())
            """, (dato, tid, other))

        # Log
        log_booking_attempt(cur, brugernavn, dato, tid, f"success:split:{choice}")
        conn.commit()

        # (Valgfrit) Kæde-relation giver ikke så meget mening for halvdel → spring over
        flash(f"Du har booket { 'tidlig' if choice=='early' else 'sen' } halvdel. Den anden halvdel er ledig for andre.", "success")
        return redirect(url_for("index", uge=valgt_uge))
    except Exception:
        conn.rollback()
        try:
            log_booking_attempt(cur, brugernavn, dato, tid, f"afvist:split_{choice}:ukendt")
            conn.commit()
        except:
            pass
        flash("Fejl under split-booking.", "error")
        return redirect(url_for("index", uge=valgt_uge))
    finally:
        cur.close(); conn.close()

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

        # vasketider.slot_index er INT hos dig → denne er fin:
        cur.execute("SELECT tekst FROM vasketider WHERE slot_index = %s", (slot_idx,))
        row = cur.fetchone()
        slot_text = row[0] if row else f"Slot {slot_idx}"

        # bookinger.slot_index er TEXT hos dig → CAST til INT i sammenligningen:
        cur.execute("""
            SELECT brugernavn
            FROM bookinger
            WHERE dato_rigtig = %s
              AND slot_index = %s
            LIMIT 1
        """, (dato_iso, slot_idx))
        r = cur.fetchone()
        conn.close()

        if r and r[0]:
            return jsonify({
                "allowed": True,
                "slot_index": slot_idx,
                "slot_text": slot_text,
                "booked_by": r[0]
            }), 200
        else:
            return jsonify({
                "allowed": False,
                "slot_index": slot_idx,
                "slot_text": slot_text,
                "booked_by": "",
                "reason": "Ingen booking i aktivt tidsrum"
            }), 200

    except Exception as e:
        try:
            conn.close()
        except Exception:
            pass
        # TIP: log evt. e til console
        return jsonify({"error": "DB-fejl", "detail": str(e)}), 500

# Bruger

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
        notifikation = "ja" if request.form.get("notifikation") == "on" else "nej"

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
        notifikation = 'ja' if request.form.get('notifikation') == 'ja' else 'nej'
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
        send_email("hornsbergmorten@gmail.com", "Godkend ny bruger", besked)

        return redirect('/login?besked=Bruger+oprettet+og+venter+godkendelse')

    return render_template("opret bruger.html")

@app.route("/vis_brugere")
def vis_brugere():
    conn = psycopg2.connect(DATABASE_URL)
    cur = conn.cursor()
    cur.execute("SELECT brugernavn, kode, email, notifikation, sms, godkendt FROM brugere")
    brugere = [dict(zip(['brugernavn','adgangskode','email','notifikation','sms','godkendt'], row)) for row in cur.fetchall()]
    conn.close()
    return render_template("vis_brugere.html", brugere=brugere)

@app.route("/opret_bruger", methods=["POST"])
def opret_bruger():
    brugernavn = request.form.get("brugernavn")
    adgangskode = request.form.get("adgangskode")
    email = request.form.get("email")
    notifikation = request.form.get("notifikation")
    sms = request.form.get("sms")
    godkendt = False
    conn = psycopg2.connect(DATABASE_URL)
    cur = conn.cursor()
    cur.execute("INSERT INTO brugere (brugernavn, kode, email, notifikation, sms, godkendt) VALUES (%s, %s, %s, %s, %s, %s)",
                (brugernavn, adgangskode, email, notifikation, sms, godkendt))
    conn.commit()
    conn.close()
    return redirect("/vis_brugere")

@app.route("/slet_bruger", methods=["POST"])
def slet_bruger():
    brugernavn = request.form.get("brugernavn")
    conn = psycopg2.connect(DATABASE_URL)
    cur = conn.cursor()
    cur.execute("DELETE FROM brugere WHERE brugernavn = %s", (brugernavn,))
    conn.commit()
    conn.close()
    return redirect("/vis_brugere")

@app.route("/godkend_bruger", methods=["POST"])
def godkend_bruger():
    brugernavn = request.form.get("brugernavn")
    conn = psycopg2.connect(DATABASE_URL)
    cur = conn.cursor()
    cur.execute("UPDATE brugere SET godkendt = TRUE WHERE brugernavn = %s", (brugernavn,))
    conn.commit()
    conn.close()
    return redirect("/vis_brugere")

@app.route("/opdater_bruger", methods=["POST"])
def opdater_bruger():
    brugernavn = request.form.get("brugernavn")
    adgangskode = request.form.get("adgangskode")
    email = request.form.get("email")
    sms = request.form.get("sms")
    notifikation = "ja" if request.form.get("notifikation") == "on" else "nej"
    godkendt = True if request.form.get("godkendt") == "on" else False

    conn = psycopg2.connect(DATABASE_URL)
    cur = conn.cursor()
    cur.execute("""
        UPDATE brugere
        SET kode = %s, email = %s, sms = %s, notifikation = %s, godkendt = %s
        WHERE brugernavn = %s
    """, (adgangskode, email, sms, notifikation, godkendt, brugernavn))
    conn.commit()
    conn.close()
    return redirect("/vis_brugere")

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

    conn = psycopg2.connect(DATABASE_URL)
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
        try:
            start_dato = datetime.strptime(f"{idag.year} {valgt_uge} 1", "%G %V %u").date()
        except ValueError:
            valgt_uge = 1
            start_dato = datetime.strptime(f"{idag.year} 1 1", "%G %V %u").date()
    else:
        valgt_uge = idag_dt.isocalendar().week
        start_dato = (idag_dt - timedelta(days=idag_dt.weekday())).date()

    # Ugedage labels og dato-objekter
    ugedage_dk = ["Mandag", "Tirsdag", "Onsdag", "Torsdag", "Fredag", "Lørdag", "Søndag"]
    ugedage_dato = [start_dato + timedelta(days=i) for i in range(7)]

    conn = get_db_connection()
    cur = conn.cursor()

    # Vasketider
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider_raw = cur.fetchall()
    tider = [r[1] for r in tider_raw]

    # Hele ugevisningen
    uge_start = start_dato
    uge_slut = start_dato + timedelta(days=6)
    cur.execute("""
        SELECT dato_rigtig, slot_index, brugernavn
        FROM bookinger
        WHERE dato_rigtig BETWEEN %s AND %s
        ORDER BY dato_rigtig, slot_index
    """, (uge_start, uge_slut))
    bookinger_uge = cur.fetchall()

    # Kommende bookinger (14 dage)
    frem_slut = idag + timedelta(days=14)
    cur.execute("""
        SELECT b.dato_rigtig, b.slot_index, b.brugernavn, v.tekst
        FROM bookinger b
        JOIN vasketider v ON v.slot_index = b.slot_index
        WHERE b.dato_rigtig >= %s AND b.dato_rigtig <= %s
        ORDER BY b.dato_rigtig, b.slot_index
    """, (idag, frem_slut))
    kommende = [
        {
            "dato_iso": r[0].strftime("%Y-%m-%d"),
            "dato_dk":  r[0].strftime("%d-%m-%Y"),
            "slot_index": r[1],
            "brugernavn": r[2],
            "slot_tekst": r[3],
        }
        for r in cur.fetchall()
    ]

    # Mapping til kalenderen → nøgler er date-objekter
    booked = {(row[0], int(row[1])): row[2] for row in bookinger_uge}

    # Miele status
    cur.execute("SELECT vaerdi FROM indstillinger WHERE navn = 'iot_vaskemaskine'")
    iot = cur.fetchone()[0] if cur.rowcount > 0 else "nej"

    cur.execute("SELECT status, remaining_time, opdateret FROM miele_status ORDER BY opdateret DESC LIMIT 1")
    row = cur.fetchone()
    if row:
        miele_status = row[0]
        remaining_time = row[1]
        miele_opdateret = row[2]
        if miele_status.lower() in ["i brug", "in use", "running"] and remaining_time is not None:
            try:
                minutes = int(remaining_time)
                hours = minutes // 60
                mins = minutes % 60
                if hours > 0:
                    tids_str = f"{hours} time{'r' if hours > 1 else ''} og {mins} min."
                else:
                    tids_str = f"{mins} min."
                miele_status += f" – {tids_str} tilbage"
            except ValueError:
                miele_status += f" – {remaining_time} tilbage"
    else:
        miele_status = "Ukendt"
        remaining_time = None
        miele_opdateret = None

    conn.close()

    # Ugens bookinger → også date-objekter
    bookinger = {}
    for b in bookinger_uge:
        d = b[0]   # allerede date fra DB
        slot = int(b[1])
        bookinger[(d, slot)] = b[2]

    return render_template(
        "index.html",
        ugedage_dk=ugedage_dk,
        ugedage_dato=ugedage_dato,   # ← date-objekter
        tider=tider,
        valgt_uge=valgt_uge,
        bookinger=bookinger,
        booked=booked,
        idag_iso=idag_dt.strftime("%Y-%m-%d"),
        kommende_bookinger=kommende,
        bookinger_14=bookinger,
        bruger=brugernavn,
        start_dato=start_dato.strftime("%Y-%m-%d"),
        timedelta=timedelta,
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

@app.route("/dokumenter", methods=["GET", "POST"])
def dokumenter():
    if 'brugernavn' not in session:
        return redirect('/login')

    if request.method == "POST":
        if session['brugernavn'].lower() != 'admin':
            return "Adgang nægtet", 403

        if "slet_fil" in request.form:
            filnavn = request.form["slet_fil"]
            sti = os.path.join(app.config['UPLOAD_FOLDER'], filnavn)
            if os.path.exists(sti):
                os.remove(sti)

        filer = request.files.getlist("fil")
        for fil in filer:
            if fil and tilladt_fil(fil.filename):
                navn = secure_filename(fil.filename)
                fil.save(os.path.join(app.config['UPLOAD_FOLDER'], navn))

        return redirect("/dokumenter")

    filer = [f for f in os.listdir(app.config['UPLOAD_FOLDER']) if f.endswith(".pdf")]
    return render_template("dokumenter.html", filer=filer, admin=session['brugernavn'].lower() == 'admin')
    # on/off tilslutning af vaskemaskine

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

# statestik

@app.route("/statistik")
def statistik():
    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    conn = get_db_connection()
    cur = conn.cursor()

    # Sørg for at 'statistik' findes (bruges til 'direktetid')
    cur.execute("""
        CREATE TABLE IF NOT EXISTS statistik (
            dato DATE NOT NULL,
            type TEXT NOT NULL,
            antal INT DEFAULT 0,
            PRIMARY KEY (dato, type)
        )
    """)
    conn.commit()

    # ====== KPI'er til vindue 1 ======
    # Aktive bookinger (fra i dag og 14 dage frem)
    cur.execute("""
        SELECT COUNT(*)
        FROM bookinger
        WHERE dato_rigtig BETWEEN CURRENT_DATE AND CURRENT_DATE + INTERVAL '14 days'
    """)
    aktive_14 = cur.fetchone()[0] or 0

    # Unikke brugere i samme periode (ekskl. 'service')
    cur.execute("""
        SELECT COUNT(DISTINCT brugernavn)
        FROM bookinger
        WHERE dato_rigtig BETWEEN CURRENT_DATE AND CURRENT_DATE + INTERVAL '14 days'
          AND brugernavn <> 'service'
    """)
    unikke_brugere = cur.fetchone()[0] or 0

    # Direkte-bookinger total (historik)
    cur.execute("SELECT COALESCE(SUM(antal),0) FROM statistik WHERE type='direktetid'")
    total_direkte = cur.fetchone()[0] or 0
    if total_direkte == 0:
        cur.execute("SELECT COUNT(*) FROM bookinger WHERE brugernavn='direkte'")
        total_direkte = cur.fetchone()[0] or 0

    # Service-blokeringer i samme 14-dages horisont (slots reserveret som 'service')
    cur.execute("""
        SELECT COUNT(*)
        FROM bookinger
        WHERE dato_rigtig BETWEEN CURRENT_DATE AND CURRENT_DATE + INTERVAL '14 days'
          AND brugernavn = 'service'
    """)
    service_blok = cur.fetchone()[0] or 0

    kpi = {
        'aktive_14': aktive_14,
        'unikke_brugere': unikke_brugere,
        'total_direkte': total_direkte,
        'service_blok': service_blok
    }

    # ====== Fejl & blokeringer til vindue 2 ======
    # Vi antager, at du logger disse som booking_log.handling med værdier:
    # 'fejl:max2', 'fejl:seriebooking', 'fejl:blokering_manglende_vask'
    def _count_handling(kode):
        cur.execute("SELECT COUNT(*) FROM booking_log WHERE handling = %s", (kode,))
        return cur.fetchone()[0] or 0

    fejl_stats = {
        'for_mange': _count_handling('fejl:max2'),
        'serie': _count_handling('fejl:seriebooking'),
        'ude_uden_afbud': _count_handling('fejl:blokering_manglende_vask'),
    }

    # ====== Systemstatus + loginforsøg (vindue 4) ======
    # Seneste Miele-status
    cur.execute("""
        SELECT status, remaining_time, opdateret
        FROM miele_status
        ORDER BY opdateret DESC
        LIMIT 1
    """)
    row = cur.fetchone()
    if row:
        miele_status = row[0]
        miele_opdateret = row[2].strftime('%Y-%m-%d %H:%M:%S') if row[2] else '—'
    else:
        miele_status, miele_opdateret = 'Ukendt', '—'

    # Antal status-logs (brug miele_activity hvis du har den, ellers fald tilbage)
    try:
        cur.execute("SELECT COUNT(*) FROM miele_activity")
        miele_logs = cur.fetchone()[0] or 0
    except Exception:
        # fallback: antal rækker i miele_status
        cur.execute("SELECT COUNT(*) FROM miele_status")
        miele_logs = cur.fetchone()[0] or 0

    # Loginforsøg (seneste 100)
    cur.execute("""
        SELECT brugernavn, ip, enhed, tidspunkt, status, id
        FROM login_log
        ORDER BY tidspunkt DESC
        LIMIT 100
    """)
    logins = cur.fetchall()

    # ====== Ændringsbookninger (vindue 3) ======
    cur.execute("""
        SELECT id, brugernavn, handling, dato, slot_index, tidspunkt
        FROM booking_log
        ORDER BY tidspunkt DESC
        LIMIT 100
    """)
    booking_log = cur.fetchall()

    # ====== Direktetid pr. dag (seneste 30 dage) tl grafen og tabel ======
    cur.execute("""
        SELECT dato, antal
        FROM statistik
        WHERE type='direktetid'
        ORDER BY dato DESC
        LIMIT 30
    """)
    direkte_pr_dag = cur.fetchall()
    if not direkte_pr_dag:
        cur.execute("""
            SELECT dato_rigtig::date AS dato, COUNT(*) AS antal
            FROM bookinger
            WHERE brugernavn='direkte'
            GROUP BY dato_rigtig::date
            ORDER BY dato DESC
            LIMIT 30
        """)
        direkte_pr_dag = cur.fetchall()

    # ====== Omformater data til templates ======
    from datetime import date, datetime as dt

    # booking_log → strenge til tabellen
    booking_log = [
        (
            lid, bnavn, handling,
            d.strftime('%d-%m-%Y') if isinstance(d, (date, dt)) else (d or ''),
            slot,
            ts.strftime('%d-%m-%Y %H:%M:%S') if isinstance(ts, dt) else (ts or '')
        )
        for (lid, bnavn, handling, d, slot, ts) in (booking_log or [])
    ]

    # direkte_pr_dag → [["YYYY-MM-DD", antal], ...] (bruges af Chart.js og tabel)
    direkte_pr_dag = [
        (
            (d.strftime('%Y-%m-%d') if isinstance(d, (date, dt)) else str(d)),
            int(a or 0)
        )
        for (d, a) in (direkte_pr_dag or [])
    ]

# Retention for login_log (valgfrit – 90 dage)
    cur.execute("""
      DELETE FROM login_log
      WHERE tidspunkt < NOW() - INTERVAL '90 days'
    """)
    conn.commit()

# Login-liste (30 dage) i det format som statistik.html forventer
    cur.execute("""
       SELECT to_char(tidspunkt,'YYYY-MM-DD HH24:MI') AS ts,
              brugernavn, status,
              COALESCE(ua_browser,''), COALESCE(ua_os,''), COALESCE(ua_device,''),
              COALESCE(ip_country,''), COALESCE(ip_region,''), COALESCE(ip_city,''), COALESCE(ip_org,''), COALESCE(ip_is_datacenter,false),
              CASE WHEN LOWER(status) = 'ok' THEN 'OK' ELSE 'Afvist' END AS indikator_label,
              CASE WHEN LOWER(status) = 'ok' THEN 1 ELSE 0 END AS indikator_ok
       FROM login_log
       WHERE tidspunkt::date BETWEEN CURRENT_DATE - INTERVAL '30 days' AND CURRENT_DATE
       ORDER BY tidspunkt DESC
    """)

    logins_struct = [{
       "tidspunkt": r[0], "brugernavn": r[1], "status": r[2],
       "ua_browser": r[3], "ua_os": r[4], "ua_device": r[5],
       "ip_country": r[6], "ip_region": r[7], "ip_city": r[8], "ip_org": r[9],
       "ip_is_datacenter": bool(r[10]),
       "indikator_label": r[11],
       "indikator_ok": bool(r[12]),
    } for r in (cur.fetchall() or [])]

    # Bookingforsøg pr. dag (30 dage)
    cur.execute("""
       SELECT ts::date AS dato, brugernavn, COUNT(*) AS forsog
       FROM booking_attempts
       WHERE ts::date BETWEEN CURRENT_DATE - INTERVAL '30 days' AND CURRENT_DATE
       GROUP BY ts::date, brugernavn
       ORDER BY dato DESC, brugernavn
    """)
    attempts_by_user_day = [{"dato":r[0].strftime('%Y-%m-%d'), "brugernavn":r[1], "forsøg":int(r[2])} for r in cur.fetchall() or []]

    cur.execute("""
       SELECT ts::date AS dato, brugernavn, COUNT(*) AS forsog
       FROM booking_attempts
       WHERE ts::date BETWEEN CURRENT_DATE - INTERVAL '30 days' AND CURRENT_DATE
       GROUP BY ts::date, brugernavn
       HAVING COUNT(*) > 2
       ORDER BY dato DESC, forsog DESC
    """)
    attempts_over_2 = [{"dato":r[0].strftime('%Y-%m-%d'), "brugernavn":r[1], "forsøg":int(r[2])} for r in cur.fetchall() or []]

    # KPI'er for kæder (30d)
    cur.execute("SELECT COUNT(*), COALESCE(AVG(score)::numeric,0) FROM direkte_kæder WHERE created_at >= CURRENT_DATE - INTERVAL '30 days'")
    row = cur.fetchone() or (0,0)
    kpi['kaeder_30d'] = int(row[0] or 0)
    kpi['kaede_avg_score'] = round(float(row[1] or 0.0), 1)

    cur.execute("""
       SELECT to_char(created_at,'YYYY-MM-DD') AS d, direkte_slot, bruger_slot, bruger, score, note, created_at
       FROM direkte_kæder
       ORDER BY created_at DESC
       LIMIT 30
    """)
    kaeder_list = [(r[0], r[1], r[2], r[3], int(r[4] or 0), r[5] or "", r[6]) for r in cur.fetchall() or []]
    # ... og medsend kaeder=kaeder_list i render_template()

    conn.close()

    # Render siden – ingen Python-genereret top10-graf længere
    return render_template(
        "statistik.html",
        kpi=kpi,
        fejl_stats=fejl_stats,
        miele_status=miele_status,
        miele_opdateret=miele_opdateret,
        miele_logs=miele_logs,
        logins=logins_struct,
        booking_log=booking_log,
        direkte_pr_dag=direkte_pr_dag,
        total_direkte=total_direkte or 0,
        attempts_by_user_day=attempts_by_user_day,
        attempts_over_2=attempts_over_2
    )

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