"""Small independent Python-GMP ordered MGS versus polynomial nullspace."""
import sys,json,time
from pathlib import Path
import numpy as np,scipy.linalg as la,gmpy2 as g
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent))
from scan_extended import events,last_null
out=[];g.get_context().precision=768
for world,m in [('zeta',40),('plant',55),('dh',60)]:
 ev=events(world);d=m+1;L=g.log(m);q=0;chosen=[]
 for h,im,mul in ev:
  if q+mul>=d:break
  q+=mul;chosen.append((h,im,mul))
 basis=[];freq=[(2*g.const_pi()*j/L)**2 for j in range(d)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m
 for h,im,mul in chosen:
  t=g.mpc(h,im);fac=2*t*g.sin(t*L/2)/g.sqrt(L)if mul==2 else g.mpfr(1);raw=[fac*ds[j]/(t*t-freq[j])for j in range(d)]
  for k in range(mul):
   v=np.array([x.real if k==0 else x.imag for x in raw],object)
   for _ in range(2):
    for u in basis:v=v-sum(x*y for x,y in zip(u,v))*u
   v/=g.sqrt(sum(x*x for x in v));basis.append(v)
 uf=np.array(basis,float);W,_=la.qr(uf.T,mode='full');Q=W[:,q:];N=last_null(ev,q,m,768)
 out.append(dict(world=world,m=m,q=q,r=d-q,projector_operator_difference=float(la.norm(Q@Q.T-N@N.T,2)),null_orthogonality=float(la.norm(N.T@N-np.eye(d-q),2)),row_frame_residual=float(la.norm(uf@N,2))))
 print(out[-1],flush=True)
(P/'NULL_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
