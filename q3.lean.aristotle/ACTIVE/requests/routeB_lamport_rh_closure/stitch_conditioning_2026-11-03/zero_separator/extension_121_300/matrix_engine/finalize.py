"""Summarize guarded finite diagnostics; raw0 is never an exact inertia claim."""
from pathlib import Path
import json,csv,hashlib
P=Path(__file__).resolve().parent;O=P.parent/'matrices';rows=[];missing=[]
for m in range(121,301):
 for w in ['zeta','plant','dh']:
  p=O/f'{w}_m{m}.json';n=O/f'{w}_m{m}.npz'
  if not p.exists() or not n.exists():missing.append((w,m));continue
  a=json.loads(p.read_text());lo,hi=a['negative_count_range'];a.update(resolved_negative_count=lo,uncertain_zero_sign_modes=hi-lo if hi is not None and lo is not None else None,raw_zero_count_not_certified=True,raw_zero_count_within_empirical_guard_range=lo<=a['ldl']['0'].get('negative',-1)<=hi,bulk_source_guard_provenance='Paired GL192/256 pilots m80,120,121,300; max entry difference <1.2e-115. Fixed1e-70 exceeds empirical n-scaled discrepancy by >40orders, but is NOT interval certification.')
  p.write_text(json.dumps(a,indent=2)+'\n');rows.append(dict(m=m,world=w,negative_lower=lo,negative_upper=hi,uncertain=hi-lo,raw_zero=a['ldl']['0'].get('negative'),float_minimum=a['float_minimum'],float_numeric_radius=a['float_numeric_radius']))
if rows:
 with (P/'SUMMARY.csv').open('w',newline='') as f:
  x=csv.DictWriter(f,fieldnames=rows[0]);x.writeheader();x.writerows(rows)
s=dict(status='DIAGNOSTIC_NEVER_A_PROOF',requested_world_m_cells=540,completed=len(rows),missing=missing,all_guard_ranges_ordered=all(r['negative_lower']<=r['negative_upper'] for r in rows),all_zeta_guard_lower_zero=all(r['negative_lower']==0 for r in rows if r['world']=='zeta'),all_plant_guard_lower_at_least_one=all(r['negative_lower']>=1 for r in rows if r['world']=='plant'),exact_inertia_claim=False)
(P/'COMPLETION.json').write_text(json.dumps(s,indent=2)+'\n');print(s)
with (P/'SHA256SUMS').open('w') as f:
 for p in sorted(list(P.glob('*.py'))+list(P.glob('*.json'))+list(O.glob('*.json'))+list(O.glob('*.npz'))):f.write(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(P.parent))+'\n')
