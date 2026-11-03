from pathlib import Path
import json,hashlib,tarfile,io
P=Path(__file__).resolve().parent;j=json.loads((P/'DATA_ARCHIVE.json').read_text());parts=[]
for x in j['parts']:
 d=(P/x['path']).read_bytes();assert hashlib.sha256(d).hexdigest()==x['sha256'];parts.append(d)
d=b''.join(parts);assert hashlib.sha256(d).hexdigest()==j['archive_sha256']
with tarfile.open(fileobj=io.BytesIO(d))as t:
 for m in t.getmembers():assert m.isfile()and not Path(m.name).is_absolute()and '..'not in Path(m.name).parts
 t.extractall(P,filter='data')
print('Restored',len(j['members']),'raw artifacts')
