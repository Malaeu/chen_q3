from pathlib import Path
import json,csv,hashlib
import numpy as np
P=Path(__file__).resolve().parent;O=P.parent/'matrices';rows=[];missing=[]
for m in range(310,601,10):
 for w in ['zeta','plant','dh']:
  p=O/f'{w}_m{m}.json';q=O/f'{w}_m{m}.npz'
  if not p.exists() or not q.exists():missing.append([w,m]);continue
  a=json.loads(p.read_text());z=np.load(q);assert z['A'].shape==(m+1,m+1) and np.isfinite(z['A']).all();assert (np.diff(z['eigenvalues'])>=0).all();assert np.array_equal(z['A'],z['A'].T)
  lo,hi=a['negative_count_range'];assert 0<=lo<=hi<=m+1
  rows.append(dict(m=m,world=w,negative_lower_heuristic=lo,negative_upper_heuristic=hi,uncertain=hi-lo,float_minimum=a['float_minimum'],float_numeric_radius=a['float_numeric_radius']))
if rows:
 with (P/'SUMMARY.csv').open('w',newline='') as f:
  x=csv.DictWriter(f,fieldnames=rows[0]);x.writeheader();x.writerows(rows)
a=dict(status='DIAGNOSTIC_NEVER_A_PROOF',requested_cells=90,completed=len(rows),missing=missing,checked='finite symmetric matrices,dimensions,sorted eigenvalues,ordered heuristic count ranges',MP_inertia_computed=False)
(P/'COMPLETION.json').write_text(json.dumps(a,indent=2)+'\n');print(a)
with (P/'SHA256SUMS').open('w') as f:
 for p in sorted(list(P.glob('*.py'))+list(P.glob('*.json'))+list(P.glob('*.md'))+list(P.glob('*.csv'))+list(O.glob('*.json'))+list(O.glob('*.npz'))):f.write(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(P.parent))+'\n')
