from flask import Flask, render_template, request, redirect, session, jsonify
import psycopg2
from datetime import datetime, timedelta
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from fpdf import FPDF
from pytz import timezone
from flask import make_response
from psycopg2 import IntegrityError
from flask import current_app
import os
import requests
import smtplib
import hashlib
import threading
import time
from email.mime.text import MIMEText
from twilio.rest import Client
from werkzeug.utils import secure_filename
import base64
import pandas as pd
import matplotlib.pyplot as plt
from io import BytesIO

app = Flask(__name__)
app.secret_key = 'hemmelig_nøgle'
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(days=int(os.getenv('REMEMBER_DAYS', '30')))
app.config.setdefault('SESSION_COOKIE_SAMESITE', 'Lax')
app.config.setdefault('SESSION_COOKIE_SECURE', True)  # Render kører HTTPS

HA_WEBHOOK_SECRET = os.environ.get("VASKETID_WEBHOOK_SECRET", "")

UPLOAD_FOLDER = 'static'
ALLOWED_EXTENSIONS = {'pdf'}
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER

UGEDAGE_DK = ['Mandag', 'Tirsdag', 'Onsdag', 'Torsdag', 'Fredag', 'Lørdag', 'Søndag']
DATABASE_URL = os.environ.get("DATABASE_URL") or "din_default_postgres_url"

limiter = Limiter(
    key_func=get_remote_address,
    default_limits=[]
)
limiter.init_app(app)

# Definer

def get_db_connection():
    return psycopg2.connect(DATABASE_URL, sslmode='require')

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

def set_miele_status(status):
    """Oversæt Miele status fra HA til korte danske ord"""
    s = (status or "").strip().lower().replace("_", " ")

    mapping = {
        # Slukket / ikke i brug
        "off": "Slukket",
        "idle": "Klar",
        "power off": "Strøm Slukket",
        "standby": "afventer",
        "not running": "ikke Klar",
        "not connected": "Ikke forbundet",

        # I gang
        "in use": "I brug",
        "running": "kørende",
        "washing": "vask",
        "main wash": "hovedvask",
        "autocleaning": "Selvrens",

        # Færdig
        "finished": "Færdig",
        "finish": "Færdig",
        "end": "Slut",
        "program ended": "Program Færdig",

        # Pause / afbrudt
        "pause": "Pause",
        "program interrupted": "Program Afbrudt",

        # Programmeret / klar til start
        "programmed": "Klar til start",
        "on": "Tændt",
        "waiting to start": "Venter på start",

        # Fejl
        "unavailable": "Ikke tilgænglig",
        "failure": "Fejl",
        "error": "Fejl",
        "fejl": "Fejl",

        # Specielle funktioner
        "rinse hold": "Skyl stop",
        "service": "Service",
        "supercooling": "Superkøling",
        "superheating": "Superopvarmning",
        "superfreezing": "Superfrysning",
        "supercooling superfreezing": "Superkøling/frysning"
    }

    # Vælg oversættelse, fallback til 'Ukendt'
    norm = mapping.get(s, "Ukendt")

    # Gem i DB
    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("""
        CREATE TABLE IF NOT EXISTS miele_status (
            id SERIAL PRIMARY KEY,
            status TEXT,
            tidspunkt TIMESTAMP DEFAULT CURRENT_TIMESTAMP
        )
    """)
    cur.execute("INSERT INTO miele_status (status) VALUES (%s)", (norm,))
    conn.commit()
    conn.close()

    return norm

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

def reminder_loop():
    tz = timezone("Europe/Copenhagen")
    notify_times = {6: 0, 10: 1, 14: 2, 18: 3}  # kl.→ slot_index (varsling 1 time før)
    run_hours = sorted(notify_times.keys())     # [6,10,14,18]

    while True:
        try:
            nu = datetime.now(tz)

            # find næste køretid i DK-tid
            næste = None
            for h in run_hours:
                if (nu.hour < h) or (nu.hour == h and nu.minute < 1):
                    næste = nu.replace(hour=h, minute=0, second=0, microsecond=0)
                    break
            if næste is None:
                # i morgen kl. første run-hour
                næste = (nu + timedelta(days=1)).replace(hour=run_hours[0], minute=0, second=0, microsecond=0)

            # sov til næste tidspunkt
            vent_tid = (næste - nu).total_seconds()
            print(f"⏳ Venter til {næste.strftime('%Y-%m-%d %H:%M')} (DK-tid)")
            time.sleep(max(1, vent_tid))

            # vi er nået til køretid → varsling for det slot, der starter om 1 time
            target_date = næste.date()              # dato i DK
            target_slot = notify_times[næste.hour]  # 0/1/2/3

            conn = get_db_connection()
            cur = conn.cursor()

            # hent kontaktinfo for bookinger på target_date + target_slot
            cur.execute("""
                SELECT b.brugernavn, u.email, u.sms
                FROM bookinger b
                JOIN brugere u ON u.brugernavn = b.brugernavn
                WHERE b.dato_rigtig = %s AND b.slot_index = %s
            """, (target_date, target_slot))
            modtagere = cur.fetchall()

            # hent menneskelig tekst for slot_index (kun til beskedteksten)
            cur.execute("SELECT tekst FROM vasketider WHERE slot_index = %s", (target_slot,))
            row = cur.fetchone()
            slot_tekst = (row[0] if row else {0:"07–11",1:"11–15",2:"15–19",3:"19–23"}[target_slot])

            conn.close()

            if not modtagere:
                print(f"ℹ️ Ingen bookinger {target_date} for slot {target_slot} ({slot_tekst})")
                continue

            besked = f"Din vasketid starter om 1 time ({slot_tekst})."
            for navn, email, sms in modtagere:
                try:
                    if email:
                        send_email(email, "Vasketid påmindelse", besked)
                    if sms:
                        send_sms_twilio(sms, besked)
                    print(f"📣 Varslet {navn} for {target_date} {slot_tekst}")
                except Exception as e:
                    print("⚠️ Fejl ved varsling:", e)

        except Exception as e:
            print("❌ Fejl i reminder_loop:", e)
            time.sleep(60)

# Route-dekorator

# Start baggrunds-jobs én gang
_jobs_started = False
def start_background_jobs():
    global _jobs_started
    if _jobs_started:
        return
    _jobs_started = True
    threading.Thread(target=reminder_loop, daemon=True).start()
    threading.Thread(target=ryd_gamle_bookinger_job, daemon=True).start()

start_background_jobs()

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

    # login og logout

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
            cur.execute("INSERT INTO login_log (brugernavn, ip, enhed, tidspunkt, status) VALUES (%s, %s, %s, %s, %s)",
                        (brugernavn, ip, enhed, tidspunkt, status))
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
            cur.execute("INSERT INTO login_log (brugernavn, ip, enhed, tidspunkt, status) VALUES (%s, %s, %s, %s, %s)",
                        (brugernavn, ip, enhed, tidspunkt, status))
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
            cur.execute("INSERT INTO login_log (brugernavn, ip, enhed, tidspunkt, status) VALUES (%s, %s, %s, %s, %s)",
                        (brugernavn, ip, enhed, tidspunkt, status))
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
        cur.execute("INSERT INTO login_log (brugernavn, ip, enhed, tidspunkt, status) VALUES (%s, %s, %s, %s, %s)",
                    (brugernavn, ip, enhed, tidspunkt, status))
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

# Login og Logud

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

# Bookninger

@app.route('/bookinger_json')
def bookinger_json():
    conn = get_db_connection()
    cur = conn.cursor()
    idag = datetime.today()

    start_af_uge = (idag - timedelta(days=idag.weekday())).date()
    cur.execute("DELETE FROM bookinger WHERE dato_rigtig < %s", (start_af_uge,))

    # Slet gamle bookinger
    cur.execute("DELETE FROM bookinger WHERE dato_rigtig < CURRENT_DATE")

    # Hent tiderne (tekst) fra vasketider
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider = dict(cur.fetchall())  # {0: '07–11', 1: ..., 2: ...}

    # Hent bookinger 14 dage frem
    cur.execute(
        "SELECT brugernavn, dato_rigtig, slot_index FROM bookinger WHERE dato_rigtig >= %s AND dato_rigtig <= %s",
        (idag.strftime('%Y-%m-%d'), (idag + timedelta(days=14)).strftime('%Y-%m-%d'))
    )
    alle_14 = cur.fetchall()
    conn.commit()
    conn.close()

    result = []
    for brugernavn, dato, slot_index in alle_14:
        dato_str = dato.strftime('%d-%m-%Y')
        tekst = tider[int(slot_index)] if int(slot_index) in tider else f"Slot {slot_index}"
        result.append({
            "dato": dato_str,
            "tid": tekst,
            "navn": brugernavn
        })

    return jsonify(result)

@app.route("/book", methods=["POST"])
def book():
    brugernavn = session.get('brugernavn')
    dato = request.form.get("dato")
    slot_raw = request.form.get("tid")      # stadig "tid" i formen
    valgt_uge = request.form.get("valgt_uge")
    uge_for_redirect = valgt_uge or datetime.today().isocalendar().week

    if not brugernavn or not dato or not slot_raw:
        return "Ugyldig anmodning", 400

    try:
        slot_index = int(slot_raw)
    except Exception:
        return "Ugyldigt slot_index", 400

    # normaliser dato til ISO
    try:
        dato_iso = datetime.strptime(dato, '%d-%m-%Y').strftime('%Y-%m-%d')
    except Exception:
        dato_iso = dato

    try:
        uge_for_redirect = (
            int(valgt_uge)
            if (valgt_uge and str(valgt_uge).isdigit())
            else datetime.strptime(dato_iso, "%Y-%m-%d").isocalendar().week
        )
    except Exception:
        uge_for_redirect = datetime.today().isocalendar().week

    conn = None
    cur = None
    tekst = None

    try:
        conn = get_db_connection()
        cur = conn.cursor()

        # Max 2 bookinger pr. dag pr. bruger
        cur.execute(
            "SELECT COUNT(*) FROM bookinger WHERE brugernavn=%s AND dato_rigtig=%s",
            (brugernavn, dato_iso)
        )
        if cur.fetchone()[0] >= 2:
            return redirect(f"/index?uge={uge_for_redirect}&fejl=Du+har+allerede+2+bookinger+denne+dag")

        # ÉN insert – undgå dobbelt-INSERT; lad DB håndhæve unikhed
        cur.execute(
            """
            INSERT INTO bookinger (brugernavn, dato_rigtig, slot_index)
            VALUES (%s, %s, %s)
            ON CONFLICT (dato_rigtig, slot_index) DO NOTHING
            """,
            (brugernavn, dato_iso, slot_index)
        )
        if cur.rowcount == 0:
            # Konflikt = tiden var optaget
            conn.rollback()
            return redirect(f"/index?uge={uge_for_redirect}&fejl=Tiden+er+allerede+booket")

        # Log
        cur.execute(
            "INSERT INTO booking_log (brugernavn, handling, dato, slot_index) VALUES (%s, %s, %s, %s)",
            (brugernavn, 'booket', dato_iso, slot_index)
        )

        # Slot-tekst til besked
        cur.execute("SELECT tekst FROM vasketider WHERE slot_index=%s", (slot_index,))
        r = cur.fetchone()
        tekst = r[0] if r else f"Slot {slot_index}"

        # Commit før notifikationer/redirect
        conn.commit()

    except psycopg2.Error:
        if conn:
            try: conn.rollback()
            except Exception: pass
        current_app.logger.exception("DB-fejl ved booking")
        return redirect(f"/index?uge={uge_for_redirect}&fejl=Database+fejl")

    except Exception:
        if conn:
            try: conn.rollback()
            except Exception: pass
        current_app.logger.exception("Generel fejl ved booking")
        return redirect(f"/index?uge={uge_for_redirect}&fejl=Der+skete+en+fejl")

    finally:
        if cur:
            try: cur.close()
            except Exception: pass
        if conn:
            try: conn.close()
            except Exception: pass

    # Notifikationer – må ikke vælte flowet
    try:
        with get_db_connection() as conn2:
            with conn2.cursor() as cur2:
                cur2.execute("SELECT email, sms FROM brugere WHERE brugernavn=%s", (brugernavn,))
                brugerinfo = cur2.fetchone()

        if brugerinfo:
            email, sms = brugerinfo
            if email:
                try:
                    send_email(email, "Vasketid bekræftet",
                               f"Du har booket vasketid den {dato} i tidsrummet: {tekst}.")
                except Exception:
                    current_app.logger.exception("Fejl ved send_email")
            if sms:
                try:
                    send_sms_twilio(sms, f"Vasketid booket {dato} – {tekst} – Vasketider.dk")
                except Exception:
                    current_app.logger.exception("Fejl ved send_sms_twilio")
    except Exception:
        current_app.logger.exception("Kunne ikke sende notifikationer")

    return redirect(f"/index?uge={uge_for_redirect}&besked=Booking+bekræftet")

# Bruger

@app.route("/slet", methods=["POST"])
def slet_booking():
    brugernavn = session.get("brugernavn")
    dato = request.form.get("dato")
    tid = request.form.get("tid")

    if not brugernavn or not dato or not tid:
        return "Ugyldig anmodning", 400

    try:
        dato_iso = datetime.strptime(dato, '%d-%m-%Y').strftime('%Y-%m-%d')
    except:
        dato_iso = dato

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("DELETE FROM bookinger WHERE brugernavn = %s AND dato_rigtig = %s AND slot_index = %s",
                (brugernavn, dato_iso, tid))
     
    # Før conn.close()
    cur.execute("""
    INSERT INTO booking_log (brugernavn, handling, dato, slot_index)
    VALUES (%s, %s, %s, %s)
""", (brugernavn, 'annulleret', dato_iso, tid))
    conn.commit()
    conn.close()

    valgt_uge = request.form.get("valgt_uge")
    return redirect(f"/index?uge={valgt_uge}" if valgt_uge else "/index")

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

# UI Brugeren

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

    ugedage_dk = ["Mandag", "Tirsdag", "Onsdag", "Torsdag", "Fredag", "Lørdag", "Søndag"]
    ugedage_dato = [(start_dato + timedelta(days=i)).strftime('%d-%m-%Y') for i in range(7)]

    conn = get_db_connection()
    cur = conn.cursor()

    # Vasketider
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider_raw = cur.fetchall()
    tider = [r[1] for r in tider_raw]

    # Hele uge-visningen (mandag–søndag), også for dage der er gået
    uge_start = start_dato
    uge_slut = start_dato + timedelta(days=6)
    cur.execute("""
        SELECT dato_rigtig, slot_index, brugernavn
        FROM bookinger
        WHERE dato_rigtig BETWEEN %s AND %s
        ORDER BY dato_rigtig, slot_index
    """, (uge_start, uge_slut))
    bookinger_uge = cur.fetchall()

    # Alle bookede tider fra dags dato og 14 dage frem
    frem_slut = idag + timedelta(days=14)
    cur.execute("""
        SELECT b.dato_rigtig, b.slot_index, b.brugernavn, v.tekst
        FROM bookinger b
        JOIN vasketider v ON v.slot_index::text = b.slot_index
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

    # Mapping til kalenderen
    booked = {(row[0].strftime("%d-%m-%Y"), row[1]): row[2] for row in bookinger_uge}

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

    # Læg hele ugens bookinger i dict til kalenderen
    bookinger = {}
    for b in bookinger_uge:
        dato_str = b[0].strftime('%d-%m-%Y')
        slot = int(b[1])
        bookinger[(dato_str, slot)] = b[2]

    return render_template(
        "index.html",
        ugedage_dk=ugedage_dk,
        ugedage_dato=ugedage_dato,
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
    nu = datetime.now(timezone("Europe/Copenhagen"))  # ← dansk tid
    dato = nu.strftime('%Y-%m-%d')
    vis_dato = nu.strftime('%d-%m-%Y')
    klokkeslaet = nu.strftime('%H:%M')

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider_raw = cur.fetchall()
    tider = [(str(r[0]), r[1]) for r in tider_raw]

    fejl = ""

    if request.method == 'POST':
        slot = request.form.get("tid")

        cur.execute("SELECT brugernavn FROM bookinger WHERE dato_rigtig = %s AND slot_index = %s", (dato, slot))
        eksisterende = cur.fetchone()
        if eksisterende:
            fejl = f"Tiden er allerede booket af {eksisterende[0]}"
        else:
            cur.execute("SELECT COUNT(*) FROM bookinger WHERE brugernavn = 'direkte' AND dato_rigtig = %s", (dato,))
            antal = cur.fetchone()[0]
            if antal >= 2:
                fejl = "Direkte har allerede booket 2 tider i dag"
            else:
                cur.execute("INSERT INTO bookinger (brugernavn, dato_rigtig, slot_index) VALUES (%s, %s, %s)",
                            ('direkte', dato, slot))
                conn.commit()

    cur.execute("SELECT slot_index, brugernavn FROM bookinger WHERE dato_rigtig = %s", (dato,))
    bookede = dict(cur.fetchall())
    conn.close()

    return render_template(
        "direkte.html",
        dato=vis_dato,
        tider=tider,
        bookede=bookede,
        klokkeslaet=klokkeslaet,
        fejl=fejl
    )

# statestik

@app.route("/statistik")
def statistik():
    import pandas as pd
    import matplotlib.pyplot as plt
    from io import BytesIO
    import base64

    if 'brugernavn' not in session or session['brugernavn'].lower() != 'admin':
        return redirect('/login')

    conn = get_db_connection()
    cur = conn.cursor()

    # 📊 Top 10 brugere
    cur.execute("""
        SELECT brugernavn, COUNT(*) AS antal
        FROM bookinger
        WHERE brugernavn != 'service'
        GROUP BY brugernavn
        ORDER BY antal DESC
        LIMIT 10
    """)
    rows = cur.fetchall()

    # 🛡️ Loginforsøg
    cur.execute("""
        SELECT brugernavn, ip, enhed, tidspunkt, status, id
        FROM login_log
        ORDER BY tidspunkt DESC
        LIMIT 100
    """)
    logins = cur.fetchall()

    # 🧾 Seneste bookinger (vis tekst fra slot_index)
    cur.execute("SELECT brugernavn, dato_rigtig, slot_index FROM bookinger ORDER BY dato_rigtig DESC LIMIT 20")
    alle = cur.fetchall()

    cur.execute("SELECT slot_index, tekst FROM vasketider ORDER BY slot_index")
    tider_dict = dict(cur.fetchall())

    seneste_bookinger = [
        {
            "brugernavn": row[0],
            "dato": row[1].strftime('%d-%m-%Y'),
            "tid": tider_dict.get(row[2], f"Slot {row[2]}")
        }
        for row in alle
    ]

    # 🔁 Ændringslog (booking_log)
    cur.execute("""
        SELECT id, brugernavn, handling, dato, slot_index, tidspunkt
        FROM booking_log
        ORDER BY tidspunkt DESC
        LIMIT 100
    """)
    booking_log = cur.fetchall()

    conn.close()

    # 📈 Diagram
    df = pd.DataFrame(rows, columns=["Brugernavn", "Bookinger"])
    fig, ax = plt.subplots(figsize=(10, 5))
    ax.bar(df["Brugernavn"], df["Bookinger"], color="skyblue")
    ax.set_title("Top 10 brugere med flest bookinger")
    ax.set_xlabel("Brugernavn")
    ax.set_ylabel("Antal bookinger")
    plt.xticks(rotation=45)
    buf = BytesIO()
    plt.tight_layout()
    plt.savefig(buf, format="png")
    buf.seek(0)
    image_base64 = base64.b64encode(buf.read()).decode("utf-8")
    buf.close()
    image_html = f'<img src="data:image/png;base64,{image_base64}" alt="Statistikdiagram">'

    return render_template(
        "statistik.html",
        diagram=image_html,
        logins=logins,
        bookinger=seneste_bookinger,
        booking_log=booking_log,
        tider_dict=tider_dict
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

    top10 = "top10" in request.form
    antal_login = "antal_login" in request.form
    seneste_login = "seneste_login" in request.form

    conn = get_db_connection()
    cur = conn.cursor()

    pdf = FPDF()
    pdf.add_page()
    pdf.set_font("Arial", size=12)

    if top10:
        cur.execute("""
            SELECT brugernavn, COUNT(*) AS antal
            FROM bookinger
            WHERE brugernavn != 'service'
            GROUP BY brugernavn
            ORDER BY antal DESC
            LIMIT 10
        """)
        top_rows = cur.fetchall()
        pdf.cell(0, 10, "Top 10 brugere med flest bookinger:", ln=True)
        for navn, antal in top_rows:
            pdf.cell(0, 10, f"{navn}: {antal} bookinger", ln=True)
        pdf.ln(5)

    if antal_login:
        cur.execute("SELECT COUNT(*) FROM login_log")
        total = cur.fetchone()[0]
        pdf.cell(0, 10, f"Totalt antal loginforsøg: {total}", ln=True)
        pdf.ln(5)

    if seneste_login:
        cur.execute("""
            SELECT brugernavn, ip, enhed, tidspunkt, status
            FROM login_log
            ORDER BY tidspunkt DESC
            LIMIT 20
        """)
        rows = cur.fetchall()
        pdf.cell(0, 10, "Seneste loginforsøg:", ln=True)
        for r in rows:
            tid = r[3].strftime('%d-%m-%Y %H:%M')
            linje = f"{r[0]} | {r[1]} | {tid} | {r[4]}"
            pdf.cell(0, 10, latin1_sikker_tekst(linje), ln=True)

    conn.close()

    response = make_response(pdf.output(dest="S").encode("latin1"))
    response.headers["Content-Type"] = "application/pdf"
    response.headers["Content-Disposition"] = "attachment; filename=statistik_valgt.pdf"
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

# Regler

@app.route("/regler")
def regler():
    return render_template("regler.html")