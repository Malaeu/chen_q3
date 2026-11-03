from pathlib import Path
import sys,json,time,resource
resource.setrlimit(resource.RLIMIT_CPU,(6,6));sys.path.insert(0,str(Path(__file__).resolve().parent));from real_continuation import isolate_real
from census import decimal
import mpmath as mp
import numpy as np
from scipy.optimize import linear_sum_assignment
P=Path(__file__).resolve().parent;mp.mp.dps=250;p=P/'results/dh_even_m190.json';old=json.loads(p.read_text());src=Path(old['source_vector_path']);d=json.loads(src.read_text());start=time.process_time()
try:
 rr,info=isolate_real(d['c'],190,'even',P/'results/dh_even_m189.json',src);z=[mp.mpc(decimal(r.real),0) for r in rr];ref=[mp.mpc(q['u_re'],q['u_im']) for q in old['roots'] if q['kind'].startswith('polynomial')];a,b=linear_sum_assignment(np.abs(np.array([complex(v) for v in z])[:,None]-np.array([complex(v) for v in ref])[None,:]));err=max(abs(z[i]-ref[j]) for i,j in zip(a,b));assert err<mp.mpf('1e-160');out=dict(status='PASS',cpu_seconds=time.process_time()-start,max_u_distance=mp.nstr(err,40),info=info)
except Exception as e:out=dict(status='FALLBACK_REQUIRED',error=repr(e),cpu_seconds=time.process_time()-start)
(P/'pilot_guarded_continuation.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='info'},flush=True)
