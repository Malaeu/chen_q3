"""Compact DH edge summaries; arithmetic only, no new minimum claim."""
from pathlib import Path
import json,csv,sys,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;FAKE=P.parents[1];sys.path.insert(0,str(P))
from extend_zeros import register
mp.mp.dps=120
register('DH compact edge summary and saved80/120 baselines','Evaluate the prescribed signed ratio lambda/[edge² log(T)/(pi T)] on the saved minimizing vectors; keep all cutoffs and census scopes explicit.','Do not invert the ratio, replace actualT, or infer a cofinal edge law from these finite rows.')
rows=[]
for path in sorted(P.glob('cell_m*_dps120_gl192.json')):
 d=json.loads(path.read_text());rows.append({'m':d['m'],'mode':d['mode'],'q':d['q'],'T':d['T'],'minimum':d['complement_minimum'],'endpoint_squared':d['endpoint_squared'],'R_edge':d['R_edge'],'source_dps':d['dps'],'census_height_bound':d['census_height_bound'],'census_status':d['census_status'],'minimum_final_residual':d['minimum_controls']['final_residual'],'source_file':path.name,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'diagnostic_never_a_proof':True})
for m,q,kind in ((80,41,'matched'),(80,73,'native'),(120,63,'matched_bracket63'),(120,65,'matched_bracket65'),(120,108,'native')):
 suffix='_native' if kind=='native' else '';path=FAKE/'ledger_diff/matched_cells'/f'dh_m{m}_q{q}{suffix}.json';d=json.loads(path.read_text());f=list(map(mp.mpf,d['complement_f']));norm=mp.fsum(x*x for x in f);L=mp.log(m);T=mp.mpf(d['T']);edge=mp.fsum((1 if n==0 else mp.sqrt(2))*x for n,x in enumerate(f))/mp.sqrt(L*norm);lam=mp.mpf(d['complement_minimum']);ratio=lam/(edge*edge*mp.log(T)/(mp.pi*T));fmt=lambda x:mp.nstr(x,110)
 rows.append({'m':m,'mode':'saved_'+kind,'q':q,'T':d['T'],'minimum':d['complement_minimum'],'endpoint_squared':fmt(edge*edge),'R_edge':fmt(ratio),'source_dps':d['dps'],'census_height_bound':230,'census_status':'NUMERICAL_COUNT_MATCH_NOT_INTERVAL_CERTIFIED','minimum_final_residual':d['complement_eigen_residual'],'source_file':str(path.relative_to(FAKE)),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'diagnostic_never_a_proof':True})
rows.sort(key=lambda r:(r['m'],r['mode']))
with (P/'summary.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
print('summary rows',len(rows))
