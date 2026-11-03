import sys,time
sys.path[:0]=['/workspace/conditioning_deps','/workspace/chen_q3/docs/routeB_bus/ground_state_zeros_2026-11-03/inputs']
import gmpy2 as g
from flint import arb_mat,ctx
from analytic_source import build
m=int(sys.argv[1]);bits=int(sys.argv[2]);alg=sys.argv[3] if len(sys.argv)>3 else 'approx';ctx.prec=bits
start=time.monotonic();out,meta=build(m,bits);print('source',m,time.monotonic()-start,flush=True);E=out['zeta'][0]
A=arb_mat([[str(v) for v in row] for row in E]);t=time.monotonic();e,r=A.eig(right=True,algorithm=alg);print('eig',time.monotonic()-t,flush=True);ix=sorted(range(len(e)),key=lambda i:g.mpfr(e[i].real.mid().str(bits//3,radius=False)));print([(i,e[i].str(30)) for i in ix[:3]],flush=True)
