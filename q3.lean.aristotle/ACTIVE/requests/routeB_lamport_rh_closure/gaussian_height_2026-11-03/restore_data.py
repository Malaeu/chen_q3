from pathlib import Path
import json,hashlib,tarfile,io
P=Path(__file__).resolve().parent;j=json.loads((P/'DATA_ARCHIVE.json').read_text());parts=[]
for r in j['parts']:
 b=(P/r['path']).read_bytes();assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256'];parts.append(b)
b=b''.join(parts);assert hashlib.sha256(b).hexdigest()==j['archive_sha256'];expected={r['path']:r for r in j['members']}
with tarfile.open(fileobj=io.BytesIO(b),mode='r:gz')as t:
 assert len(t.getmembers())==len(expected)
 for m in t.getmembers():
  assert m.isfile()and m.name in expected and not Path(m.name).is_absolute()and'..'not in Path(m.name).parts
  b=t.extractfile(m).read();r=expected[m.name];assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256'];f=P/m.name
  if f.exists():assert f.read_bytes()==b
  else:f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
print('PASS',len(expected),'archive members')
