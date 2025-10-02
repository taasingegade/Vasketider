import geoip2.database
import os

DB_PATH = "geo/GeoLite2-City.mmdb"

if os.path.exists(DB_PATH):
    reader = geoip2.database.Reader(DB_PATH)
    print(f"✅ GeoLite2 DB indlæst fra {DB_PATH}")
else:
    print(f"❌ GeoLite2 DB mangler i {DB_PATH}")