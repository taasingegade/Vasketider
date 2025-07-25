import psycopg2
import os
import time
from datetime import datetime, timedelta
from pytz import timezone
from email.mime.text import MIMEText
import smtplib
from twilio.rest import Client

def get_db_connection():
    db_url = os.environ.get("DATABASE_URL")
    return psycopg2.connect(db_url, sslmode='require')

def send_email(modtager, emne, besked):
    afsender = "hornsbergmorten@gmail.com"
    adgangskode = os.environ.get("Gmail_adgangskode")

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
    account_sid = os.environ.get("Twilio_SID")
    auth_token = os.environ.get("Twilio_token")
    afsender_nummer = os.environ.get("+13515298337")

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
        nu = datetime.now(timezone("Europe/Copenhagen"))
        en_time_senere = nu + timedelta(hours=1)
        dato = en_time_senere.strftime("%Y-%m-%d")
        klok = en_time_senere.hour

        # Find hvilket tidsrum det passer ind i
        slot = None
        if 7 <= klok < 11:
            slot = "07–11"
        elif 11 <= klok < 15:
            slot = "11–15"
        elif 15 <= klok < 19:
            slot = "15–19"
        elif 19 <= klok < 23:
            slot = "19–23"
        else:
            slot = None  # uden for gyldig bookingtid

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
                    if notifikation and notifikation.strip() in ['ja', 'on', 'true']:
  # 📱 Automatisk +45 foran hvis ikke angivet
    if sms and not sms.startswith("+"):
        sms = "+45" + sms.strip()
                        send_email(email, "Påmindelse", f"Husk du har vasketid om 1 time: {dato}, {slot}")
                        send_sms_twilio(sms, f"Påmindelse om: Vasketid om 1 time ({slot})")

            conn.close()

        time.sleep(600)  # 10 minutter

if __name__ == "__main__":
    check_bookinger()