import psycopg2
import os
import time
from datetime import datetime, timedelta
from email.mime.text import MIMEText
import smtplib
from twilio.rest import Client

def get_db_connection():
    db_url = os.environ.get("DATABASE_URL")
    return psycopg2.connect(db_url, sslmode='require')

def send_email(modtager, emne, besked):
    afsender = "hornsbergmorten@gmail.com"
    adgangskode = os.environ.get("GMAIL_ADGANGSKODE")

    msg = MIMEText(besked)
    msg["Subject"] = emne
    msg["From"] = f"No Reply Vasketid <{afsender}>"
    msg["To"] = modtager

    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as server:
            server.login(afsender, adgangskode)
            server.sendmail(afsender, [modtager], msg.as_string())
    except Exception as e:
        print("E-mail fejl:", e)

def send_sms_twilio(modtager, besked):
    account_sid = os.environ.get("TWILIO_SID")
    auth_token = os.environ.get("TWILIO_TOKEN")
    afsender_nummer = os.environ.get("TWILIO_NUMBER")

    if not all([account_sid, auth_token, afsender_nummer]):
        return

    try:
        client = Client(account_sid, auth_token)
        client.messages.create(
            body=besked,
            from_=afsender_nummer,
            to=modtager
        )
    except Exception as e:
        print("SMS fejl:", e)

def check_bookinger():
    while True:
        nu = datetime.now()
        en_time_senere = nu + timedelta(hours=1)
        dato = en_time_senere.date().strftime("%Y-%m-%d")
        tid = en_time_senere.hour

        if 7 <= tid < 11:
            slot = "07–11"
        elif 11 <= tid < 15:
            slot = "11–15"
        elif 15 <= tid < 19:
            slot = "15–19"
        elif 19 <= tid < 23:
            slot = "19–23"
        else:
            slot = None

        if slot:
            conn = get_db_connection()
            cur = conn.cursor()
            cur.execute("SELECT brugernavn FROM bookinger WHERE dato_rigtig = %s AND tid = %s", (dato, slot))
            brugere = cur.fetchall()

            for (brugernavn,) in brugere:
                cur.execute("SELECT email, sms, notifikation FROM brugere WHERE brugernavn = %s", (brugernavn,))
                data = cur.fetchone()
                if data:
                    email, sms, notifikation = data
                    if notifikation == "ja":
                        send_email(email, "Påmindelse", f"Du har vasketid om 1 time: {dato}, {slot}")
                        send_sms_twilio(sms, f"Påmindelse: Vasketid om 1 time ({slot})")

            conn.close()

        time.sleep(600)  # 10 minutter

if __name__ == "__main__":
    check_bookinger()