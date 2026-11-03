"""Bounded T1-frozen same-multiplicity coordinate pilots; not fullgrid."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,csv
import common
import hermite_pilots as h
import hermite_prepare as prep
P=Path(__file__).resolve().parent
PLAN=[('zeta',16,5,(4,5)),('zeta',80,36,(34,35)),('zeta',120,58,(57,58)),('zeta',200,101,(100,101)),('zeta',300,157,(156,157)),('dh',310,249,(241,242)),('plant',310,167,(165,166)),('zeta',600,333,None)]
for w,m,q,pair in PLAN:
 prep.prepare(m);d=common.dataset()[w,m];cutoff=common.pairs_for(w,m,.75)[0]['original_T']if common.pairs_for(w,m,.75)else None
 if pair:
  candidates=[p for p in common.pairs_for(w,m,.75)if(p['left_ordinal'],p['right_ordinal'])==pair]
  assert len(candidates)==1 and candidates[0]['left_mult']==candidates[0]['right_mult'];assert candidates[0]['split_q']+candidates[0]['right_mult']<=q
 result=h.run(w,m,q,list(pair)if pair else None,cutoff)
 result['original_optimum_q']=d['original_q'];result['is_original_optimum_sector']=q==d['original_q'];result['pair_selection']='frozen T1 nearby equal-multiplicity pair; mandated248 handled separately';result['sector_note']='original optimum'if q==d['original_q']else'additional whole-orbit sector, not a refitted source optimum'
 if m==600:result['sector_note']='resolved kappa1 control; no T1 pair eligible at theta<=.75 in this prefix. Original optimumq600 hasfloor delta; pair600/601 wouldneedq601=d and is inadmissible.'
 (P/f'hermite_{w}_m{m}_q{q}.json').write_text(json.dumps(result,indent=2)+'\n')
rows=[]
for f in sorted(P.glob('hermite_*_m*_q*.json')):
 z=json.load(f.open())
 for r in z['rows']:rows.append({**r,'scope_note':z.get('sector_note',z.get('original_optimum_split_note')or z['scope'])})
keys=list(dict.fromkeys(k for r in rows for k in r))
with(P/'hermite_summary.csv').open('w',newline='')as f:
 wr=csv.DictWriter(f,fieldnames=keys);wr.writeheader();wr.writerows(rows)
print('HERMITE boundedpilotrows',len(rows),'active',sum(r['status']=='TRANSFORM_EXECUTED'for r in rows),flush=True)
