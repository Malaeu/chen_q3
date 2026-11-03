import sys,time,importlib.util
sys.path.insert(0,'/workspace/conditioning_deps')
import mpmath as mp
from flint import arb_mat,ctx
spec=importlib.util.spec_from_file_location('q2','/workspace/chen_q3/docs/routeB_bus/lit_quickcheck_2026-11-03/Q2_simple_even/check.py');q2=importlib.util.module_from_spec(spec);spec.loader.exec_module(q2)
m=int(sys.argv[1]);dps=int(sys.argv[2]);mp.mp.dps=dps;ctx.dps=dps
start=time.monotonic();E,O=q2.build(m,m,'zeta',96);print('built',m,time.monotonic()-start,flush=True)
A=arb_mat([[str(E[i,j]) for j in range(E.cols)] for i in range(E.rows)]);t=time.monotonic()
try:
 e,r=A.eig(right=True,algorithm='approx'); print('eig',time.monotonic()-t,flush=True);ix=sorted(range(len(e)),key=lambda i:float(e[i].real));print([(i,str(e[i])[:100]) for i in ix[:4]],flush=True)
except Exception as ex:print(type(ex),ex)
