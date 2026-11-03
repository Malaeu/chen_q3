from pathlib import Path
import hashlib,json,csv,tarfile,io
P=Path(__file__).resolve().parent
for line in(P/'SHA256SUMS').read_text().splitlines():
 h,n=line.split('  ',1);assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,n
j=json.loads((P/'DATA_ARCHIVE.json').read_text());parts=[]
for r in j['parts']:
 b=(P/r['path']).read_bytes();assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256'];parts.append(b)
b=b''.join(parts);assert hashlib.sha256(b).hexdigest()==j['archive_sha256'];expected={r['path']:r for r in j['members']};cases={}
with tarfile.open(fileobj=io.BytesIO(b),mode='r:gz')as t:
 assert len(t.getmembers())==len(expected)==42
 for m in t.getmembers():
  r=expected[m.name];data=t.extractfile(m).read();assert len(data)==r['bytes']and hashlib.sha256(data).hexdigest()==r['sha256']
  if m.name.startswith('cells/'):
   d=json.loads(data);cases[m.name]=d
   for s,rec in zip(d['summary'],d['receipts']):
    assert s['sectors']==len(rec['evaluated'])+len(rec['bounded'])or(len(rec['evaluated'])==1 and s['sectors']==len(rec['bounded']))
    assert s['max_gap_lower']<=s['best_gap']<=s['max_gap_upper']
    assert s['scope'].startswith('FINITE_CENSUS')
rows=list(csv.DictReader((P/'SUMMARY.csv').open()));assert len(rows)==108
assert {int(r['m'])for r in rows if r['world']=='zeta'}==set(range(310,601,10))
assert len(json.loads((P/'SOURCE_CHECK.json').read_text()))==60
assert max(float(r['relative_integral_error'])for r in json.loads((P/'GAUSSIAN_INTEGRAL_CHECK.json').read_text()))<1e-65
assert len(json.loads((P/'CARRIER_PRECISION_CHECK.json').read_text()))==18
assert len(json.loads((P/'FRAME_PRECISION_CHECK.json').read_text()))==9
assert all(float(r['minimum'])<0 for r in csv.DictReader((P/'NEGATIVE_SWEEP.csv').open()))
print('PASS: committed hashes,42 archive members,108 summary rows,30 zeta windows, source and precision controls')
