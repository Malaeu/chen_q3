"""Freeze explicit bounded numerical coverage and floor exclusions."""
from pathlib import Path
import csv,json,hashlib
import common
P=Path(__file__).resolve().parent;L=Path('/workspace/pair_aware/local')
REQUEST=[16,24,40,80,120,200,248,300,310,400,600]
receipts=[json.loads(f.read_text())for f in sorted(P.glob('hermite_*_m*_q*.json'))];rows=[]
for w in ['zeta','dh','plant']:
 for m in REQUEST:
  rr=[z for z in receipts if z['world']==w and z['m']==m];active=[z for z in rr if any(x['status']=='TRANSFORM_EXECUTED'for x in z['rows'])];rows.append(dict(world=w,m=m,numeric_prefix_pilots=len(rr),nonidentity_prefix_pilots=len(active),tested_q=';'.join(str(z['q'])for z in rr),coverage='BOUNDED_NONIDENTITY_NUMERICAL_PILOT'if active else('IDENTITY_OR_NO_ADMISSIBLE_T1_PAIR_ONLY'if rr else'NOT_NUMERICALLY_EXECUTED'),exact_argument_scope='invertible coordinate identity applies only when both complete equal-multiplicity events are included; mixed events not numerically blended'))
common.write_csv('hermite_COVERAGE.csv',rows)
z=common.dataset()['zeta',600];r=z['original_best'];floor=dict(world='zeta',m=600,q=z['original_q'],r=r['r'],delta=r['delta'],original_guard=z['guard'],status='ORIGINAL_OPTIMUM_NOT_NUMERICALLY_REFRAMED_RELATIVE_UNRESOLVED',relative_delta_difference=None,explanation='original optimumq600 delta is at original float floor; T1 nearby pair600/601 needsq601=d and would makeJzero. kappa1q333 is a separate identity/no-admissible-pair control, not an active Hermite test')
(P/'hermite_ORIGINAL_FLOOR.json').write_text(json.dumps(floor,indent=2)+'\n')
ms=sorted(set(z['m']for z in receipts));arrayfiles=[]
for m in ms:
 for w in ['zeta','dh','plant']:
  f=L/'matrices'/f'{w}_m{m}.npz'
  if f.exists():arrayfiles.append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
(P/'hermite_LOCAL_ARRAYS.json').write_text(json.dumps(dict(scope='local owner-authorized unchanged source regeneration; not a full-grid baseline replay',arrays=arrayfiles),indent=2)+'\n')
