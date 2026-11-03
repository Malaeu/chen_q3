from pathlib import Path
import json,csv,hashlib,tarfile,io
P=Path(__file__).resolve().parent
for line in(P/'SHA256SUMS').read_text().splitlines():
 h,n=line.split('  ',1);assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h,n
j=json.loads((P/'CONTROL_ARCHIVE.json').read_text());parts=[]
for x in j['parts']:
 b=(P/x['path']).read_bytes();assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256'];parts.append(b)
b=b''.join(parts);assert hashlib.sha256(b).hexdigest()==j['archive_sha256'];expected={x['path']:x for x in j['members']}
with tarfile.open(fileobj=io.BytesIO(b),mode='r:gz')as t:
 assert len(t.getmembers())==len(expected)==300
 for m in t.getmembers():
  b=t.extractfile(m).read();r=expected[m.name];assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'];d=json.loads(b);assert d['row_labels_count']==d['q']
assert json.loads((P/'baseline_manifest.json').read_text())['status']=='SEVEN_BASELINE_GATES_PASS'
assert len(list(csv.DictReader((P/'BASELINE_SCALAR_RESTORE.csv').open())))==945
pairs=list(csv.DictReader((P/'PAIRS.csv').open()));assert len(pairs)==5911
rows=list(csv.DictReader((P/'SUMMARY.csv').open()));assert len(rows)==2835
for t,yes in [('0.5',12),('0.6',12),('0.75',9)]:
 r=[x for x in rows if x['world']=='zeta' and int(x['m'])>=310 and x['theta']==t];assert len(r)==30 and sum(x['status']=='YES_NUMERIC' for x in r)==yes
 assert all(x['status']=='UNRESOLVED' for x in r if x['original_status']=='UNRESOLVED')
assert sum(x['status']=='EMPTY_ADMISSIBLE' for x in rows)==4
m=next(x for x in rows if x['world']=='zeta' and x['m']=='248' and x['theta']=='0.6');assert m['original_q']=='127' and m['best_measured_q']=='128'
score=json.loads((P/'L2_SCORE.json').read_text());assert score['primary_L2']['outcome_and_pair']==9 and score['primary_L2']['outcome_n']==47
h=json.loads((P/'hermite_VALIDATION.json').read_text());assert h['distinct_nonidentity_transforms']==8 and h['active_theta_receipts']==13 and h['max_relative_delta_difference']<1e-10
assert json.loads((P/'control_delta_dualspan.json').read_text())['status']=='ALL_SIX_DUAL_SPAN_CHECKS_PASS'
assert len(list(csv.DictReader((P/'ORIGINAL_DELTA_MAX.csv').open())))==945
assert len(json.loads((P/'envelope_complete.json').read_text()))==85
print('PASS: hashes, 300 controls, 945 cells, 2835 restrictions, pair and Hermite checks')
