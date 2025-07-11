from datetime import datetime, timedelta
import psycopg2, os
from app import send_sms_twilio, send_email

DATABASE_URL = os.environ.get("DATABASE_URL")
conn = psycopg2.connect(DATABASE_URL)
cur = conn.cursor()

nu = datetime.now()
om_en_time = nu + timedelta(hours=1)
dato = om_en_time.strftime('%Y-%m-%d')
tidspunkt = om_en_time.strftime('%H')

# Find det tilhørende tidsrum
tidsrum = None
if 7 <= om_en_time.hour < 11: tidsrum = '07–11'
elif 11 <= om_en_time.hour < 15: tidsrum = '11–15'
elif 15 <= om_en_time.hour < 19: tidsrum = '15–19'
elif 19 <= om_en_time.hour < 23: tidsrum = '19–23'

if tidsrum:
    cur.execute("""
        SELECT b.brugernavn, u.email, u.sms, u.notifikation
        FROM bookinger b
        JOIN brugere u ON b.brugernavn = u.brugernavn
        WHERE b.dato_rigtig = %s AND b.tid = %s
    """, (dato, tidsrum))

    for navn, email, sms, notifikation in cur.fetchall():
        besked = f"Påmindelse: Du har vasketid kl. {tidsrum} i dag ({dato}) – Vasketider.dk"
        if notifikation == 'ja':
            if email:
                send_email(email, "Påmindelse om vasketid", besked)
            if sms:
                send_sms_twilio(sms, besked)

conn.close()
