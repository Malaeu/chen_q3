"""Verify and restore the complete21153-row sector CSV."""
from pathlib import Path
import json,hashlib,gzip
P=Path(__file__).resolve().parent;j=json.loads((P/'SCAN_ARCHIVE.json').read_text());pieces=[]
for x in j['parts']:
 d=(P/x['path']).read_bytes();assert hashlib.sha256(d).hexdigest()==x['sha256'];pieces.append(d)
data=b''.join(pieces);assert hashlib.sha256(data).hexdigest()==j['gzip_sha256'];raw=gzip.decompress(data);assert hashlib.sha256(raw).hexdigest()==j['csv_sha256'];(P/'all_sectors.csv').write_bytes(raw);print('Restored all_sectors.csv',len(raw),'bytes')
