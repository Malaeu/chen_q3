"""Assemble all540 cells and all sector bounds; no numeric sign promotion."""
from pathlib import Path
import json,csv,collections,hashlib
P=Path(__file__).resolve().parent
def csvwrite(path,rows):
 keys=list(dict.fromkeys(k for r in rows for k in r))
 with path.open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
ss=[];counts=[];sectors=[];metadata=[];spectrum=[]
for m in range(121,301):
 for world in ['zeta','plant','dh']:
  j=json.loads((P/'scan_cells'/f'{world}_m{m}.json').read_text());s=j['summary'];s['best_level_status']='UNRESOLVED_AT_ZERO'if abs(s['best_lambda_r'])<=s['numeric_guard']else('POSITIVE_BELOW_C2'if 0<s['best_lambda_r']<2 else('AT_OR_ABOVE_C2'if s['best_lambda_r']>=2 else'NEGATIVE_RESOLVED'));s['best_delta_status']='UNRESOLVED_FLOAT_FLOOR'if s['best_delta']<=s['numeric_guard']else'RESOLVED_NUMERIC';ss.append(s)
  for kind in ['evaluated','bounded']:
   for r in j[kind]:sectors.append(dict(world=world,m=m,record_kind=kind,**r))
  meta=json.loads((P/'matrices'/f'{world}_m{m}.json').read_text());metadata.append(meta)
  counts.append(dict(world=world,m=m,n_minus_lower=meta['negative_count_range'][0],n_minus_upper=meta['negative_count_range'][1],uncertain_zero_sign_modes=meta['negative_count_range'][1]-meta['negative_count_range'][0],raw_LDL_zero_count=meta['ldl']['0']['negative'],raw_zero_count_not_certified=True,guard=meta['guard'],bits=meta['bits'],GL=meta['GL_order'],matrix_sha256=s['source_matrix_sha256']))
  import numpy as np
  ev=np.load(P/'matrices'/f'{world}_m{m}.npz')['eigenvalues'];spectrum.extend(dict(world=world,m=m,index=i,lambda_float64=float(v),zero_sign='UNRESOLVED_FLOAT_FLOOR'if abs(v)<=s['numeric_guard']else('NEGATIVE'if v<0 else'POSITIVE'))for i,v in enumerate(ev))
csvwrite(P/'SUMMARY.csv',ss);csvwrite(P/'COUNTS_ZERO.csv',counts);csvwrite(P/'all_sectors.csv',sectors);csvwrite(P/'float_spectra.csv',spectrum)
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',cells=len(ss),sectors=len(sectors),evaluated=sum(r['evaluated_sectors']for r in ss),bounded=sum(r['bounded_sectors']for r in ss),worlds={w:dict(separator_status_counts=dict(collections.Counter(r['separator_kappa_ge1']for r in ss if r['world']==w)),negative_lower_range=[min(r['n_minus_lower']for r in ss if r['world']==w),max(r['n_minus_lower']for r in ss if r['world']==w)])for w in ['zeta','plant','dh']},all_best_gap_brackets_within4guards=all(r['best_gap_resolved']for r in ss),max_frame_orthogonality=max(r['MP_frame_float_orthogonality']or 0 for r in ss))
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
