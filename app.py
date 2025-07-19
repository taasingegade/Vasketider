from flask import Flask, render_template, request, redirect, session, jsonify
import psycopg2
from datetime import datetime, timedelta
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from fpdf import FPDF
from flask import make_response
import os
import smtplib
import hashlib
from email.mime.text import MIMEText
from twilio.rest import Client
from werkzeug.utils import secure_filename
import base64
import pandas as pd
import matplotlib.pyplot as plt
from io import BytesIO

app = Flask(__name__)
app.secret_key = 'hemmelig_nøgle'

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

def ryd_gamle_bookinger():
    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("DELETE FROM bookinger WHERE dato_rigtig < CURRENT_DATE - INTERVAL '1 day'")
    conn.commit()
    conn.close()

ryd_gamle_bookinger()

    # login og logout

@app.route('/')
def home():
    return redirect('/login')

@limiter.limit("5 per 10 minutes")
@app.route('/login', methods=['GET', 'POST'])
def login():
    fejl = request.args.get("fejl", "")
    besked = request.args.get("besked", "")

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
            # Fejl – brugernavn findes ikke
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
            # Fejl – forkert kode
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

            # Tæl antal fejllogin fra IP i dag
            cur.execute("SELECT COUNT(*) FROM login_log WHERE ip = %s AND status = 'Fejl i login' AND tidspunkt::date = CURRENT_DATE", (ip,))
            antal = cur.fetchone()[0]
            conn.close()

            if antal >= 5:
                send_email("hornsbergmorten@gmail.com", "Advarsel: Fejllogin", f"{antal} fejllogin fra IP {ip} – Enhed:\n{enhed}")

            return redirect('/login?fejl=Forkert+adgangskode')

        if not godkendt:
            # Fejl – bruger ikke godkendt
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

        # ✅ SUCCESFULDT LOGIN
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
        if brugernavn == 'admin':
            return redirect('/admin')
        else:
            return redirect('/index')

    return render_template('login.html', fejl=fejl, besked=besked)

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
    cur = conn.cursor()    # Hent brugere
    cur.execute("SELECT * FROM brugere")
    brugere = [
        dict(
            brugernavn=row[0],
            adgangskode=row[1],
            email=row[2],
            sms=row[3]
        ) for row in cur.fetchall()
    ]

# Hent bookinger med korrekt ID
    cur.execute("SELECT id, brugernavn, dato_rigtig, tid FROM bookinger")
    bookinger = [
    dict(
        id=row[0],
        brugernavn=row[1],
        dato=row[2].strftime('%d-%m-%Y'),  # formatér dato_rigtig som tekst
        tid=row[3]
    ) for row in cur.fetchall()
]
    
    # Hent kommentar
    cur.execute("SELECT * FROM kommentar")
    kommentar = [
        dict(id=row[0], brugernavn=row[1], tekst=row[2]) for row in cur.fetchall()
    ]

    # Hent booking log
    cur.execute("SELECT brugernavn, handling, dato, tid, tidspunkt FROM booking_log ORDER BY tidspunkt DESC LIMIT 100")
    booking_log = cur.fetchall()
    conn.close()
    return render_template(
        "admin.html",
        brugere=brugere,
        bookinger=bookinger,
        kommentar=kommentar,
        booking_log=booking_log,
    )

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
    tid = request.form.get("tid")
    if not dato or not tid:
        return "Ugyldig dato eller tidspunkt", 400

    try:
        dato_iso = datetime.strptime(dato, '%Y-%m-%d').strftime('%Y-%m-%d')
    except:
        dato_iso = dato

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("INSERT INTO bookinger (brugernavn, dato_rigtig, tid) VALUES (%s, %s, %s)", ("service", dato_iso, tid))
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
    bookinger_14 = {}
    conn = get_db_connection()
    cur = conn.cursor()
    idag = datetime.today()
    cur.execute(
        "SELECT brugernavn, dato_rigtig, tid FROM bookinger WHERE dato_rigtig >= %s AND dato_rigtig <= %s",
        (idag.strftime('%Y-%m-%d'), (idag + timedelta(days=14)).strftime('%Y-%m-%d'))
    )
    alle_14 = cur.fetchall()
    conn.close()
    for b in alle_14:
        dato_str = b[1].strftime('%d-%m-%Y')  # dato_rigtig er allerede et DATE-objekt
        bookinger_14[(dato_str, b[2])] = b[0]
    return jsonify([
        {"dato": k[0], "tid": k[1], "navn": v}
        for k, v in bookinger_14.items()
    ])

def get_db_connection():
    db_url = os.environ.get("DATABASE_URL") or "postgresql://vasketid_db_user:rGVcD7xXGPrltSmj4AtKqoNcfwEe71bm@dpg-d1i3i09r0fns73bs6j4g-a.frankfurt-postgres.render.com/vasketid_db"
    return psycopg2.connect(db_url, sslmode='require')

def send_email(modtager, emne, besked):
    afsender = "hornsbergmorten@gmail.com"
    adgangskode =  os.environ.get("Gmail_adgangskode")

    msg = MIMEText(besked)
    msg["Subject"] = emne
    msg["From"] = f"No Reply Vasketid <{afsender}>"
    msg["To"] = modtager
    msg.add_header('Reply-To', 'noreply@vasketider.dk')

    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as server:
            server.login(afsender, adgangskode)
            server.sendmail(afsender, [modtager], msg.as_string())
    except Exception as e:
        print("Fejl ved afsendelse af e-mail:", e)

def send_sms_twilio(modtager, besked):
    account_sid = os.environ.get("Twilio_SID")
    auth_token = os.environ.get("Twilio_token")
    afsender_nummer = "+13515298337"

    if not all([account_sid, auth_token, afsender_nummer]):
        print("Twilio miljøvariabler mangler.")
        return

    try:
        client = Client(account_sid, auth_token)
        message = client.messages.create(
            body=besked,
            from_=afsender_nummer,
            to=modtager
        )
        print("Twilio SMS sendt:", message.sid)
    except Exception as e:
        print("Twilio fejl:", e)


@app.route("/book", methods=["POST"])
def book():
    brugernavn = session.get('brugernavn')
    dato = request.form.get("dato")
    tid = request.form.get("tid")
    valgt_uge = request.form.get("valgt_uge")

    if not brugernavn or not dato or not tid:
        return "Ugyldig anmodning", 400

    try:
        dato_iso = datetime.strptime(dato, '%d-%m-%Y').strftime('%Y-%m-%d')
    except:
        dato_iso = dato  # fallback hvis allerede i korrekt format

    conn = get_db_connection()
    cur = conn.cursor()

    # Tjek antal eksisterende bookinger på dagen
    cur.execute("SELECT COUNT(*) FROM bookinger WHERE brugernavn = %s AND dato_rigtig = %s", (brugernavn, dato_iso))
    antal = cur.fetchone()[0]
    if antal >= 2:
        conn.close()
        return redirect(f"/index?uge={valgt_uge}&fejl=Du+har+allerede+2+bookinger+denne+dag")

    # Indsæt ny booking
    cur.execute(
        "INSERT INTO bookinger (brugernavn, dato_rigtig, tid) VALUES (%s, %s, %s)",
        (brugernavn, dato_iso, tid)
    )
    # Efter cur.execute(...) for at indsætte booking:
    cur.execute("""
    INSERT INTO booking_log (brugernavn, handling, dato, tid)
    VALUES (%s, %s, %s, %s)
""", (brugernavn, 'booket', dato_iso, tid))
    conn.commit()

    # Send notifikationer hvis info findes
    cur.execute("SELECT email, sms FROM brugere WHERE brugernavn = %s", (brugernavn,))
    brugerinfo = cur.fetchone()
    if brugerinfo:
        email, sms = brugerinfo
        send_email(email, "Vasketid bekræftet", f"Du har booket vasketid den {dato} i følgende tidsrum {tid}.")
        send_sms_twilio(sms, f"Du har booket vasketid {dato} kl. {tid} – Vasketider.dk")

    conn.close()

    # Fallback hvis valgt_uge mangler
    if not valgt_uge:
        valgt_uge = datetime.today().isocalendar().week

    return redirect(f"/index?uge={valgt_uge}&besked=Booking+bekræftet")

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
    cur.execute("DELETE FROM bookinger WHERE brugernavn = %s AND dato_rigtig = %s AND tid = %s",
                (brugernavn, dato_iso, tid))
     
    # Før conn.close()
    cur.execute("""
    INSERT INTO booking_log (brugernavn, handling, dato, tid)
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

    # GET-request → vis opret bruger-formular
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

    # index siden

@app.route('/index')
def index():
    if 'brugernavn' not in session:
        return redirect('/login')
    brugernavn = session['brugernavn']

    valgt_uge = request.args.get("uge")
    idag = datetime.today()

    if valgt_uge:
        valgt_uge = int(valgt_uge)
        try:
            start_dato = datetime.strptime(f"{idag.year} {valgt_uge} 1", "%G %V %u")
        except ValueError:
            valgt_uge = 1
            start_dato = datetime.strptime(f"{idag.year} 1 1", "%G %V %u")
    else:
        valgt_uge = idag.isocalendar().week
        dag = idag.weekday()
        start_dato = idag - timedelta(days=dag)

    ugedage_dk = UGEDAGE_DK
    ugedage_dato = [(start_dato + timedelta(days=i)).strftime('%d-%m-%Y') for i in range(7)]
    tider = ['07–11', '11–15', '15–19', '19–23']

    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("SELECT brugernavn, dato_rigtig, tid FROM bookinger WHERE dato_rigtig >= %s AND dato_rigtig <= %s",
                (idag.strftime('%Y-%m-%d'), (idag + timedelta(days=14)).strftime('%Y-%m-%d')))
    alle_14 = cur.fetchall()

    cur.execute("SELECT vaerdi FROM indstillinger WHERE navn = 'iot_vaskemaskine'")
    iot = cur.fetchone()[0] if cur.rowcount > 0 else "nej"

    conn.close()

    bookinger = {}
    for b in alle_14:
        dato_str = b[1].strftime('%d-%m-%Y')  # dato_rigtig er allerede et DATE-objekt
        bookinger[(dato_str, b[2])] = b[0]

    print("BOOKINGER:")
    for k, v in bookinger.items():
        print(f"{k}: {v}")

    return render_template(
        "index.html",
        ugedage_dk=ugedage_dk,
        ugedage_dato=ugedage_dato,
        tider=tider,
        valgt_uge=valgt_uge,
        bookinger=bookinger,
        bookinger_14=bookinger,
        bruger=brugernavn,
        start_dato=start_dato,
        timedelta=timedelta,
        iot=iot,
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
    if request.method == 'POST':
        dato = datetime.today().strftime('%Y-%m-%d')
        tid = request.form.get("tid")
        conn = get_db_connection()
        cur = conn.cursor()

        # Tæl dagens kiosk-bookinger
        cur.execute("SELECT COUNT(*) FROM bookinger WHERE brugernavn = 'direkte' AND dato_rigtig = %s", (dato,))
        antal = cur.fetchone()[0]

        if antal >= 2:
            conn.close()
            return "Maks 2 tider booket i dag"

        cur.execute("INSERT INTO bookinger (brugernavn, dato_rigtig, tid) VALUES (%s, %s, %s)",
                    ('direkte', dato, tid))
        conn.commit()
        conn.close()
        return redirect('/direkte')

    # GET: vis dagens tider
    dato = datetime.today()
    tider = ['07–11', '11–15', '15–19', '19–23']
    conn = get_db_connection()
    cur = conn.cursor()
    cur.execute("SELECT tid FROM bookinger WHERE brugernavn = 'direkte' AND dato_rigtig = %s", (dato.strftime('%Y-%m-%d'),))
    bookede = [r[0] for r in cur.fetchall()]
    conn.close()

    return render_template("kiosk.html", dato=dato.strftime('%d-%m-%Y'), tider=tider, bookede=bookede)

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

# 🛡️ Loginforsøg (fra login_log)
    cur.execute("""
        SELECT brugernavn, ip, enhed, tidspunkt, status, id
        FROM login_log
        ORDER BY tidspunkt DESC
        LIMIT 100
    """)
    logins = cur.fetchall()

    # 🧾 Seneste bookinger
    cur.execute("SELECT brugernavn, dato_rigtig, tid FROM bookinger ORDER BY dato_rigtig DESC LIMIT 20")
    seneste_bookinger = [
        {"brugernavn": row[0], "dato": row[1].strftime('%d-%m-%Y'), "tid": row[2]}
        for row in cur.fetchall()
    ]

    # Ændringslog for bookninger
    cur.execute("""
    SELECT id, brugernavn, handling, dato, tid, tidspunkt
    FROM booking_log
    ORDER BY tidspunkt DESC
    LIMIT 100
""")
    booking_log = cur.fetchall()

    conn.close()

    # 📈 Lav bookingdiagram
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

    return render_template("statistik.html", diagram=image_html, logins=logins, bookinger=seneste_bookinger, booking_log=booking_log)

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