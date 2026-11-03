from pathlib import Path
import json,csv,hashlib,os
import mpmath as mp
mp.mp.dps=120;P=Path(__file__).resolve().parent;data=[json.loads((P/f'm{m}.json').read_text())for m in [16,24,40]];rows=[r for a in data for r in a['rows']]
assert len(rows)==15 and all(r['status']=='MP_NUMERICAL_DIAGNOSTIC'for r in rows)
for r in rows:assert mp.mpf(r['u_minus_minus_1'])<0<mp.mpf(r['u_plus_minus_1'])
with(P/'EPSILON_SENSITIVITY.csv').open('w',newline='')as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
qs=[a['quiet']for a in data]
with(P/'QUIET.csv').open('w',newline='')as f:
 w=csv.DictWriter(f,fieldnames=qs[0]);w.writeheader();w.writerows(qs)
a=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=[16,24,40],epsilon_rows=15,all_endpoint_offsets_straddle_zero=True,max_E_Q_entry=mp.nstr(max(mp.mpf(q['E_Q_max_entry'])for q in qs),110),max_Q_orthogonality_entry=mp.nstr(max(mp.mpf(q['Q_orthogonality_max_entry'])for q in qs),110),max_Cholesky_entry_residual=mp.nstr(max(mp.mpf(r['cholesky_max_entry_residual'])for r in rows),110),no_interval_certification=True,source_sha256=hashlib.sha256((P.parent/'source/split.py').read_bytes()).hexdigest(),zero_table_sha256=hashlib.sha256(Path(os.environ.get('QUIET_ZETA',str(P.parent/'source_inputs/zeta_zeros.csv'))).read_bytes()).hexdigest())
ends=[r for m in [16,24,40] for r in json.loads((P/f'ENDPOINTS_m{m}.json').read_text())['endpoints']]
a['endpoint_carriers']=len(ends);a['max_endpoint_equation_entry_residual']=mp.nstr(max(mp.mpf(r['endpoint_residual_max_entry'])for r in ends),110)
(P/'CHECKS.json').write_text(json.dumps(a,indent=2)+'\n');print(a)
with(P/'SHA256SUMS').open('w')as f:
 for p in sorted(list(P.glob('*.py'))+list(P.glob('*.json'))+list(P.glob('*.csv'))+list(P.glob('*.md'))):f.write(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n')
