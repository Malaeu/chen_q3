"""Point-arithmetic replay of three float-floor sectors, no new eigenproblem for A."""
from pathlib import Path
import sys,json,hashlib,argparse
import numpy as np,mpmath as mp,gmpy2 as gp
from scan_separator import events
sys.path.insert(0,str(Path(__file__).resolve().parent/'source_inputs'))
from dh_matrix import build_mp
P=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path('/workspace/conditioning_input'));root=ap.parse_args().input;gp.get_context().precision=768
assert hashlib.sha256((P/'source_inputs/dh_matrix.py').read_bytes()).hexdigest()=='9554c27549fc0970391c06026d8bfb402ab1cfa3b2f1db3c0db6deeb92a39f00'
m=53;d=54;L=gp.log(m);freq=[(2*gp.const_pi()*j/L)**2 for j in range(d)];scale=[gp.mpfr(1)]+[gp.sqrt(2)]*m;B=np.empty((d,d),object);n=0
for h,im,mult in events(root,'dh'):
 if n+mult>=d:break
 t=gp.mpc(h,im);fac=2*t*gp.sin(t*L/2)/gp.sqrt(L)if mult==2 else gp.mpfr(1);row=[fac*scale[j]/(t*t-freq[j])for j in range(d)]
 for comp in range(mult):
  v=np.array([z.real if comp==0 else z.imag for z in row],object)
  for _ in range(2):
   if n:v=v-(B[:n]@v)@B[:n]
  B[n]=v/gp.sqrt(sum(x*x for x in v));n+=1
idx=int(np.argmax([float(1-sum(B[i,j]*B[i,j]for i in range(n)))for j in range(d)]));v=np.array([gp.mpfr(int(j==idx))for j in range(d)],object)
for _ in range(2):v=v-(B[:n]@v)@B[:n]
B[n]=v/gp.sqrt(sum(x*x for x in v))
results=[]
for dps,order in [(120,128),(160,160)]:
 A,_=build_mp(m,dps,order);AA=np.array([[gp.mpfr(str(A[i,j]))for j in range(d)]for i in range(d)],object)
 for q in [50,51,52]:
  AQ=AA@B[q:].T;H=AQ.T@AQ;scaleH=max(abs(x)for x in H.flat);hh=mp.matrix([[mp.mpf(str(x/scaleH))for x in row]for row in H]);ev=mp.eigsy(hh,eigvals_only=True);delta=mp.sqrt(ev[len(ev)-1]*mp.mpf(str(scaleH)))
  results.append(dict(q=q,r=d-q,dps=dps,GL=order,delta=mp.nstr(delta,100)))
(P/'DH53_MP_REPLAY.json').write_text(json.dumps(dict(status='POINT_DIAGNOSTIC_NOT_INTERVAL',recipe='Pinned dh_matrix.build_mp; original cached source file is not published at pinned path; matching recipe plus128/160 order consistency, not byte-identity of original MP A.',results=results),indent=2)+'\n');print(results)
