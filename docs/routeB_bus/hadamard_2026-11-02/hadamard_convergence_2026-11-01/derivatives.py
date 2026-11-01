import convergence as c
import json
from pathlib import Path
mp=c.mp
out=[]
for m in (8,12,16):
 L=mp.log(m)
 K,Dr=c.matrices(L,44,'right',m)
 _,Dl=c.matrices(L,44,'left',m)
 E=c.even(K,44,44);ER=c.even(Dr,44,44);EL=c.even(Dl,44,44)
 for N in (40,44):
  ev,V=mp.eigsy(E[:N+1,:N+1]);v=V[:,0]
  left=(v.T*EL[:N+1,:N+1]*v)[0];right=(v.T*ER[:N+1,:N+1]*v)[0]
  r=dict(m=m,N=N,dps=mp.mp.dps,lambda0=mp.nstr(ev[0],60),slope_left=mp.nstr(left,60),slope_right=mp.nstr(right,60),r_left=mp.nstr(-left/ev[0],30),r_right=mp.nstr(-right/ev[0],30))
  out.append(r);print(json.dumps(r),flush=True)
  (c.OUT/'anchor_derivatives.json').write_text(json.dumps(out,indent=2)+'\n')
