from pathlib import Path
import json,csv,hashlib
import numpy as np
P=Path(__file__).resolve().parent;rows=[];missing=[];maxcontrol=0.;maxrec=0.;maxsg=0.
for m in range(16,301):
 zfiles={}
 for w in ['zeta','dh','double2']:
  p=P/f'{w}_m{m}.json';n=P/f'{w}_m{m}.npz'
  if not p.exists()or not n.exists():missing.append((w,m));continue
  a=json.loads(p.read_text());z=np.load(n);zfiles[w]=z;assert z['C'].shape==(m+1,m+1)
  for k in ['C','B','A1','atom2']:assert np.isfinite(z[k]).all() and np.array_equal(z[k],z[k].T)
  rec=float(np.max(abs(z['C']+z['B']-z['A1'])));maxrec=max(maxrec,rec);maxsg=max(maxsg,float(a['sign_conservation_max_entry']))
  rows.append(dict(world=w,m=m,C_minimum=a['C_minimum'],B_minimum=a['B_minimum'],A1_minimum=a['A1_minimum'],numeric_radius=a['numeric_radius'],float_reconstruction=rec,sign_conservation=a['sign_conservation_max_entry'],frozen_A_difference=a['frozen_A_regression']['max_abs_entry_difference'] if a['frozen_A_regression'] else None))
 if all(w in zfiles for w in ['zeta','double2']):
  a,b=zfiles['zeta'],zfiles['double2'];assert np.array_equal(a['C'],b['C']);maxcontrol=max(maxcontrol,float(np.max(abs(b['B']-a['B']-a['atom2']))))
if rows:
 with (P/'SUMMARY.csv').open('w',newline='')as f:
  x=csv.DictWriter(f,fieldnames=rows[0]);x.writeheader();x.writerows(rows)
a=dict(status='DIAGNOSTIC_NEVER_A_PROOF',expected=855,completed=len(rows),missing=missing,float_C_B_A1_max_reconstruction=maxrec,double2_control_max_float_reconstruction=maxcontrol,sign_groups_max_MP_entry_residual=maxsg,source_operator_fixed=True,no_inertia_or_interval_claim=True)
(P/'COMPLETION.json').write_text(json.dumps(a,indent=2)+'\n');print(a)
with (P/'SHA256SUMS').open('w')as f:
 for p in sorted(list(P.glob('*.py'))+list(P.glob('*.json'))+list(P.glob('*.npz'))+list(P.glob('*.md'))+list(P.glob('*.csv'))):f.write(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n')
