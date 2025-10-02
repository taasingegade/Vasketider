import os, sys, tarfile, io, urllib.request

LICENSE = os.getenv("MAXMIND_LICENSE_KEY")
if not LICENSE:
    sys.exit("Missing MAXMIND_LICENSE_KEY env var")

DOWNLOADS = [
    ("https://download.maxmind.com/app/geoip_download?edition_id=GeoLite2-City&license_key={}&suffix=tar.gz".format(LICENSE),
     "geo/GeoLite2-City.mmdb"),
    ("https://download.maxmind.com/app/geoip_download?edition_id=GeoLite2-ASN&license_key={}&suffix=tar.gz".format(LICENSE),
     "geo/GeoLite2-ASN.mmdb"),
]

os.makedirs("geo", exist_ok=True)

def extract_mmdb_from_targz(data: bytes, out_path: str):
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tf:
        mmdb_member = next((m for m in tf.getmembers() if m.name.endswith(".mmdb")), None)
        if not mmdb_member:
            raise RuntimeError("No .mmdb file in archive")
        f = tf.extractfile(mmdb_member)
        with open(out_path, "wb") as out:
            out.write(f.read())

for url, outp in DOWNLOADS:
    print(f"Downloading {url} → {outp}")
    with urllib.request.urlopen(url) as r:
        data = r.read()
    extract_mmdb_from_targz(data, outp)

print("✅ GeoLite2 databases fetched to ./geo")