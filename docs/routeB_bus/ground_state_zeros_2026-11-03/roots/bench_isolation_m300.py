import sys,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linear_sum_assignment
sys.path.insert(0,str(Path(__file__).resolve().parent));from census import numerator,decimal
from flint import ctx,arb
import mpmath as mp
P=Path(__file__).resolve().parents[1];x=json.loads((P/'spectra/vectors/zeta_m300.json').read_text());old=json.loads((P/'roots/results/zeta_even_m300.json').read_text());pol=numerator(x['c'],'even',300,2000);ctx.prec=160;t=time.monotonic();rr=pol.roots(tol=arb('1e-165'),maxprec=10000);elapsed=time.monotonic()-t;ctx.prec=2000;mp.mp.dps=220
zz=[mp.mpc(decimal(r.real),decimal(r.imag)) for r in rr];target=[mp.mpc(r['u_re'],r['u_im']) for r in old['roots'] if r['kind'].startswith('polynomial')];a,b=linear_sum_assignment(np.abs(np.array([complex(z) for z in zz])[:,None]-np.array([complex(z) for z in target])[None,:]));maxerr=max(abs(zz[i]-target[j]) for i,j in zip(a,b));ans=dict(m=300,start_bits=160,construction_bits=2000,seconds=elapsed,degree=len(rr),max_u_distance_to_prior=mp.nstr(maxerr,40));print(json.dumps(ans),flush=True);assert maxerr<mp.mpf('1e-160')
