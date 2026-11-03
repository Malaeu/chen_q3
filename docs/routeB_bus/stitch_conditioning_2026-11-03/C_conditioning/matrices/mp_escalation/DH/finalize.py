"""Index completed DH spectra and explicit numerical guards; no eigensolves."""
from pathlib import Path
import json,csv,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;M=P.parents[1];mp.mp.dps=130
rows=[];coverage=[];index=[]
for m in range(16,121):
 meta=json.loads((M/f'cell_dh_m{m}.json').read_text());f=P/f'mp_cell_dh_m{m}_dps100_GL160.json'
 if meta.get('mp_eigenvalues') and not f.exists():
  coverage.append(dict(m=m,status='REUSED_EXISTING_MP_METADATA',source=meta.get('mp_eigenvalues_source','see matrix metadata'),new_file=''))
  continue
 if not f.exists():coverage.append(dict(m=m,status='MISSING_MP',source='',new_file=''));continue
 z=json.loads(f.read_text());assert z['world']=='dh' and z['m']==m and z['N']==m and len(z['eigenvalues'])==m+1;assert z['dps']==100 and z['GL']==160
 origin=z['source_metadata']['origin'];assert origin['kind']=='fresh_MP_source_build' and origin['input_dps']==100 and origin['GL']==160
 vals=list(map(mp.mpf,z['eigenvalues']));assert all(a<=b for a,b in zip(vals,vals[1:]));g=mp.mpf(z['roundoff_heuristic']);positive=[x for x in vals if x>g];neg=sum(x<-g for x in vals);unknown=sum(abs(x)<=g for x in vals)
 rows.append(dict(m=m,dps=100,GL=160,dimension=m+1,roundoff_heuristic=z['roundoff_heuristic'],negative_beyond_heuristic=neg,unresolved_within_heuristic=unknown,positive_beyond_heuristic=len(positive),smallest_positive_beyond_heuristic=mp.nstr(min(positive),100) if positive else '',source_MP_float_Frobenius=z['float_matrix_difference_Frobenius'],float_numeric_radius=z['float_numeric_radius']))
 coverage.append(dict(m=m,status='FRESH_MP100_GL160',source='reviewed Q2 physical even source',new_file=f.name));index.append(dict(path=f.name,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size,m=m))
for name,data in [('guard_summary.csv',rows),('coverage.csv',coverage)]:
 with (P/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=data[0]);w.writeheader();w.writerows(data)
(P/'SPECTRUM_INDEX.json').write_text(json.dumps(index,indent=2)+'\n')
result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',new_MP_count=len(rows),reused_existing_count=sum(x['status']=='REUSED_EXISTING_MP_METADATA' for x in coverage),missing_ms=[x['m'] for x in coverage if x['status']=='MISSING_MP'],all_new_sources_fresh_MP100_GL160=True,maximum_Frobenius_difference=max(r['source_MP_float_Frobenius'] for r in rows),guard_status='Diagnostic roundoff heuristics only; no interval certification.')
(P/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
