"""Offline diagnostic packet integrity and scalar consistency checks."""
from pathlib import Path
from decimal import Decimal
from datetime import datetime
import csv,gzip,json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parents[1];mp.mp.dps=50
def read(n):return json.loads((P/n).read_text())
def rows(n):return list(csv.DictReader((P/n).open()))
s=read('NATIVE_SUMMARY.json');r=read('REFINED_EXTREMA.json');reg=read('PREREGISTRATION.json');g=read('GATES.json')
assert s['max_m']==100000000 and s['evaluated_integers']==99999999 and s['nonpositive_count']==0
assert s['long_double_mantissa_bits']==64 and s['prime_count']==5761455 and s['higher_prime_power_count']==1404
pred=(P/'PREDICTIONS.md').read_bytes();assert hashlib.sha1(b'blob '+str(len(pred)).encode()+b'\0'+pred).hexdigest()==reg['predictions_blob']=='efaaf570e175e7c213afa07a6aa657d378ea531e'
assert len(rows('G1_NATIVE.csv'))==3
for x in rows('G1_NATIVE.csv'):assert mp.mpf(x['abs_error'])<=mp.mpf('1e-10')and x['pass']=='1'
c=rows('CHECKPOINT_COMPARISON.csv');assert [int(x['m'])for x in c]==[10**k for k in range(1,9)]
for x in c:
 diff=abs(mp.mpf(x['native_Psi'])-mp.mpf(x['mpmath40_Psi']));assert diff<mp.mpf('1e-9')and x['pass_gate']=='True';assert abs(diff-mp.mpf(x['abs_difference']))<mp.mpf('1e-35')
mpref=read('CHECKPOINTS_MP.json');assert mpref['dps']==40 and mpref['all_primepowers']and mpref['prime_count']==5761455
assert r['dps']==40 and r['no_root_sums_read']and r['checkpoint_sha256']==hashlib.sha256((P/'CHECKPOINTS_MP.json').read_bytes()).hexdigest()
assert s['minimum_m']==r['candidate_minimum']['m']==34186454 and s['maximum_m']==r['maximum_neighborhood_winner']['m']==319439
best=r['minimum_top20'];assert len(best)==20 and all(mp.mpf(a['Psi'])<mp.mpf(b['Psi'])for a,b in zip(best,best[1:]))
assert [x['m']for x in best]==[int(x['m'])for x in rows('TWENTY_SMALLEST_NATIVE.csv')]
assert [int(x['m'])for x in rows('TWENTY_SMALLEST.csv')]==[x['m']for x in best]
assert len(r['minimum_ranked_rows'])==read('REFINEMENT_PLAN.json')['candidate_count']==40
for a,b in [('mean_uniform_t_continuous','uniform_t_mean_from_log2'),('mean_uniform_t_from_zero','uniform_t_mean_from_zero')]:assert abs(mp.mpf(s[a])-mp.mpf(r['mean'][b]))<mp.mpf('1e-9')
assert abs(mp.mpf(r['mean']['uniform_t_mean_from_log2'])-mp.mpf('.0462'))<mp.mpf('.003')
assert mp.mpf(r['candidate_minimum']['Psi'])>=mp.mpf('.002')and mp.mpf(r['maximum_neighborhood_winner']['Psi'])<=mp.mpf('.0924')
env=rows('LOG_ENVELOPE.csv');previous=1;total=0
for x in env:
 lo,hi=int(x['m_first']),int(x['m_last']);assert lo==previous+1 and hi>=lo;total+=hi-lo+1;previous=hi
 assert mp.mpf(x['Psi_min'])<=mp.mpf(x['Psi_max'])
assert total==99999999 and previous==100000000
idx=read('RECORDS_INDEX.json');hfull=hashlib.sha256();prev_m=0;prev_v=Decimal('Infinity');count=0
for k,item in enumerate(idx['parts']):
 h=hashlib.sha256();nr=0
 with gzip.open(P/item['file'],'rb')as f:
  header=next(f);h.update(header)
  if k==0:hfull.update(header)
  for line in f:
   h.update(line);hfull.update(line);a,_,b=line.decode().strip().split(',');m=int(a);v=Decimal(b)
   assert m>prev_m and v<prev_v;prev_m,prev_v=m,v;nr+=1
 assert nr==item['rows']and h.hexdigest()==item['uncompressed_sha256'];count+=nr
assert count==idx['total_rows']==s['record_count']==605239 and prev_m==s['minimum_m']
assert hfull.hexdigest()==idx['full_uncompressed_sha256']
assert sum(int(x['records'])for x in rows('RECORD_RUNS.csv'))==count
for i in range(1,5):assert g[f'T{i}']['score']=='PASS_DIAGNOSTIC'
assert g['G1']=='PASS'and g['G2']=='PASS'and not g['RH_export']and not g['route_state_changed']
for line in(P/'SHA256SUMS').read_text().splitlines():
 expected,name=line.split('  ',1);assert hashlib.sha256((P/name).read_bytes()).hexdigest()==expected,name
print('PASS: 99,999,999-sample coverage; G1/G2; independent refinement/means; all605,239strictrecords reconstructed; prediction blob; SHA256SUMS')
