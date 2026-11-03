from pathlib import Path
import sys,json,time,resource
resource.setrlimit(resource.RLIMIT_CPU,(15,15))
sys.path.insert(0,str(Path(__file__).resolve().parent));from real_continuation import isolate_real
from census import isolate,decimal
import mpmath as mp
import numpy as np
from scipy.optimize import linear_sum_assignment
P=Path(__file__).resolve().parent;BASE=P.parent;mp.mp.dps=250;rows=[]
for world in ['zeta','dh','plant']:
 for parity in ['even','odd']:
  current=P/'results'/f'{world}_{parity}_m190.json';previous=P/'results'/f'{world}_{parity}_m189.json'
  if not current.exists() or not previous.exists():continue
  ref=json.loads(current.read_text());src=Path(ref['source_vector_path']);data=json.loads(src.read_text());c=data['v_even0'] if parity=='even' else data['v_odd0'];t=time.monotonic()
  try:
   roots,info=isolate_real(c,190,parity,previous,src);rr=[mp.mpc(decimal(r.real),0) for r in roots];old=[mp.mpc(r['u_re'],r['u_im']) for r in ref['roots'] if r['kind'].startswith('polynomial')];ia,ib=linear_sum_assignment(np.abs(np.array([complex(z) for z in rr])[:,None]-np.array([complex(z) for z in old])[None,:]));err=max(abs(rr[i]-old[j]) for i,j in zip(ia,ib));assert err<mp.mpf('1e-160');row=dict(world=world,parity=parity,m=190,status='PASS',seconds=info['seconds'],cpu_seconds=info['cpu_seconds'],stored_full_isolation_seconds=ref['checks']['seconds'],max_u_distance=mp.nstr(err,40),degree=info['degree'],newton_max_steps=info['newton_max_steps'],info=info)
  except Exception as e:row=dict(world=world,parity=parity,m=190,status='FALLBACK_REQUIRED',error=repr(e),seconds=time.monotonic()-t)
  rows.append(row);print({k:v for k,v in row.items() if k!='info'},flush=True);(P/'pilot_real_continuation.json').write_text(json.dumps(dict(rows=rows,scope='Bounded 30 CPU pilot against stored complete full-isolation root sets. No bulk adoption yet.'),indent=2)+'\n')
old=json.loads((P/'pilot_real_continuation_initial.json').read_text());out=json.loads((P/'pilot_real_continuation.json').read_text());out['fresh_full_timing_control']=old['fresh_full_timing_control'];out['second_repair_budget_cpu_seconds']=15;out['total_initial_plus_repair_cpu_budget']=30;(P/'pilot_real_continuation.json').write_text(json.dumps(out,indent=2)+'\n')
