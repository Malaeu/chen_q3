"""Read-only numerical-receipt validation; no source/eigen/root computation."""
from pathlib import Path
import json,hashlib,csv
import mpmath as mp
mp.mp.dps=150
P=Path(__file__).resolve().parent;rows=[]
for m in range(81,120,2):
 p=P/f'dh_m{m}_half.json';z=json.loads(p.read_text());assert z['outcome']=='RESOLVED_FIXED_DECIMAL_MATRIX'
 assert len(z['attempts'])==2 and [a['dps'] for a in z['attempts']]==[200,240]
 first,last=z['attempts'];assert first['q']==last['q'] and last['q']>=last['dimension'] and z['J_dimension']==0
 agreement=abs(mp.mpf(last['sigma'])/mp.mpf(first['sigma'])-1);assert agreement<mp.mpf('1e-20')
 for a in z['attempts']:
  assert mp.mpf(a['sigma'])>0 and mp.mpf(a['relative_residual'])<mp.mpf('1e-30') and mp.mpf(a['relative_change'])<mp.mpf('1e-30')
  assert len(a['weak_left'])==a['q']
  mass=mp.fsum(mp.mpf(r['mass']) for r in a['weak_left']);assert abs(mass-1)<mp.mpf('1e-90')
  assert max(abs(mp.mpf(r['coordinate'])**2-mp.mpf(r['mass'])) for r in a['weak_left'])<mp.mpf('1e-90')
 rows.append(dict(m=m,q=last['q'],dimension=last['dimension'],sigma=last['sigma'],relative_200_240=z['relative_200_240'],relative_residual=last['relative_residual'],iterations=last['iterations'],weak_pair_left=last['weak_pair_left'],weak_pair_right=last['weak_pair_right'],weak_pair_mass=last['weak_pair_mass'],weak_pair_localization=last['weak_pair_localization'],receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
with (P/'odd_receipts.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
done=json.loads((P/'odd_DONE.json').read_text());assert done['status']=='COMPLETE' and len(done['completed'])==20 and not done['missing']
out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',complete=True,cells=20,CPU_seconds=done['cpu_seconds'],CPU_cap=done['cpu_cap'],all_stored_gates_pass=True,full_weak_left_ledgers_present=True,left_mass_sum_and_coordinate_square_checks_pass=True,max_relative_200_240=str(max(mp.mpf(r['relative_200_240']) for r in rows)),max_relative_residual=str(max(mp.mpf(r['relative_residual']) for r in rows)),max_iterations=max(r['iterations'] for r in rows),localized_count=sum(r['weak_pair_localization']=='localized' for r in rows),diffuse_count=sum(r['weak_pair_localization']=='diffuse' for r in rows),input_scope='fixed approximately80-digit DH zero table; no root uncertainty propagated; no source eigensolve',receipts_csv_sha256=hashlib.sha256((P/'odd_receipts.csv').read_bytes()).hexdigest())
(P/'odd_POSTVALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
