import sys,time,subprocess,json
from pathlib import Path
sys.path[:0]=['/workspace/conditioning_deps','/workspace/chen_q3/docs/routeB_bus/ground_state_zeros_2026-11-03/inputs']
import gmpy2 as g
from analytic_source import build
P=Path(__file__).parent;m=int(sys.argv[1]);bits=int(sys.argv[2]);out,meta=build(m,bits);print('source',meta['seconds'],flush=True)
for world in ['zeta','dh','plant']:
 for parity,A in zip(['even','odd'],out[world]):
  n=len(A);data=f'{n} {bits}\n'+'\n'.join(str(x) for x in A.flat)+'\n';t=time.monotonic();r=subprocess.run([str(P/'loweig')],input=data,text=True,capture_output=True);ans=json.loads(r.stdout);print('solve',world,parity,ans['seconds'],ans['lambda'][0][:28],ans['lambda'][0][-10:],flush=True)
  for k in range(2):
   v=list(map(g.mpfr,ans['v'][k]));la=g.mpfr(ans['lambda'][k]);res=max(abs(sum((a*x for a,x in zip(row,v)),g.mpfr(0))-la*y) for row,y in zip(A,v));print('res',k,str(res),flush=True)
