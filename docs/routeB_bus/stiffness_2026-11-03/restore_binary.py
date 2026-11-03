from pathlib import Path
import json,hashlib,tarfile,io
P=Path(__file__).resolve().parent;j=json.loads((P/'BINARY_ARCHIVE.json').read_text());chunks=[]
for r in j['parts']:
 b=(P/r['path']).read_bytes();assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256'];chunks.append(b)
b=b''.join(chunks);assert hashlib.sha256(b).hexdigest()==j['sha256'];expected={r['path']:r for r in j['members']}
with tarfile.open(fileobj=io.BytesIO(b),mode='r:gz')as t:
 assert len(t.getmembers())==len(expected)
 for m in t.getmembers():
  assert m.isfile()and m.name in expected and not Path(m.name).is_absolute()and'..'not in Path(m.name).parts
  b=t.extractfile(m).read();r=expected[m.name];assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256'];p=P/m.name
  if p.exists():assert p.read_bytes()==b
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print('PASS:24binary scalar/vector receipts restored; no dense arrays')
