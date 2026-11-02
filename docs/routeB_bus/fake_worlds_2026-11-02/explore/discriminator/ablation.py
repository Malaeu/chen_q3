"""Altered-source NPP deletion on saved fixed complements; no FE claim."""
from pathlib import Path
import json,sys,time,hashlib
import mpmath as mp
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[1];LEDGER=ROOT/'ledger_diff'
sys.path.insert(0,str(ROOT));from dh_matrix import coeffs
mp.mp.dps=80
fmt=lambda x:mp.nstr(x,60)
rows=[]
for m,q in [(80,41),(120,63),(120,65)]:
 t=time.monotonic();p=LEDGER/'matched_cells'/f'dh_m{m}_q{q}.json';d=json.loads(p.read_text());A=mp.matrix(d['A']);U=mp.matrix(d['U']);f=mp.matrix(d['complement_f']);L=mp.log(m);_,bb=coeffs(m);ss=[mp.mpf(0)]*(m+1);dg=[mp.mpf(0)]*(m+1)
 def npp(n):
  for p in range(2,n+1):
   if n%p==0:
    while n%p==0:n//=p
    return n!=1
 for n in range(2,m):
  if not npp(n):continue
  r=mp.log(n)/L;w=bb[n]/mp.sqrt(n)
  for k in range(m+1):
   sn=mp.sin(2*mp.pi*k*r);ss[k]+=w*sn;dg[k]+=w*(2*(1-r)*mp.cos(2*mp.pi*k*r)-(sn/(mp.pi*k) if k else 0))
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;P=mp.zeros(m+1)
 for i in range(m+1):
  P[i,i]=dg[i]
  for k in range(i+1,m+1):P[i,k]=P[k,i]=ds[i]*ds[k]/mp.pi*(k*ss[k]-i*ss[i])/(i*i-k*k)
 C=U.T*(A+P)*U;C=(C+C.T)/2;ev,V=mp.eigsy(C);y=V[:,0];res=mp.norm(C*y-ev[0]*y);original=mp.mpf(d['complement_minimum']);fixed=mp.fdot(f,(A+P)*f)
 z=dict(m=m,q=q,working_dps=80,original_minimum=fmt(original),ablated_minimum=fmt(ev[0]),original_minimizer_ablated_Rayleigh=fmt(fixed),original_minimizer_NPP=fmt(mp.fdot(f,P*f)),eigen_residual=fmt(res),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),seconds=time.monotonic()-t,positive=bool(ev[0]>0));rows.append(z);print(json.dumps(z),flush=True)
(OUT/'ablation.json').write_text(json.dumps(dict(status='DIAGNOSTIC_ALTERED_SOURCE_NO_FE_CLAIM',prediction_pass=all(x['positive'] for x in rows),rows=rows,code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+'\n')
