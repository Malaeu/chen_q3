"""Finite source screw-kernel diagnostics; never a proof. Signed LDL, no PSD assumption."""
from pathlib import Path
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,json,csv,time,hashlib
from functools import lru_cache
import mpmath as mp
import numpy as np
from scipy.linalg import eigvalsh
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT.parents[1]/'fake_worlds_2026-11-02'))
from dh_matrix import coeffs

def arithmetic(world,end=6):
 M=int(mp.ceil(mp.exp(end))); b=coeffs(M)[1] if world=='dh' else [mp.mpf(0)]*(M+1)
 if world!='dh':
  sieve=[True]*(M+1)
  for p in range(2,M+1):
   if sieve[p]:
    for k in range(2*p,M+1,p):sieve[k]=False
    k=p
    while k<=M:b[k]=mp.log(p);k*=p
 return [(mp.log(n),b[n]/mp.sqrt(n),n) for n in range(2,M+1) if b[n]]

def g_function(world,end=6):
 atoms=arithmetic(world,end);a=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
 c=mp.log(5/mp.pi)+mp.digamma(mp.mpf('.75')) if world=='dh' else -mp.euler-mp.log(8*mp.pi)-mp.pi/2
 trig=mp.polygamma(1,a/2)/4;w=2*mp.pi/mp.log(2)+mp.j/4
 @lru_cache(maxsize=50000)
 def g(t):
  t=abs(t)
  if not t:return mp.mpf(0)
  if t>mp.mpf('.2'):
   q=mp.exp(-2*t); term=mp.exp(-a*t); tail=mp.mpf(0); r=0
   while True:
    v=term/(a+2*r)**2;tail+=v
    if abs(v)/(1-q)<mp.eps*mp.mpf('.01'):break
    term*=q;r+=1
  else:
   x=mp.exp(-t/2)
   tail=mp.polylog(2,x)-mp.polylog(2,-x)+(2 if world!="dh" else -2)*mp.im(mp.polylog(2,mp.j*x))
  smooth=trig-tail
  v=-c*t/2-smooth+mp.fsum(weight*(t-x) for x,weight,n in atoms if x<t)
  if world!='dh':v-=16*mp.sinh(t/4)**2
  if world=='plant':v+=4*mp.re((mp.cos(w*t)-1)/w**2)
  return v
 return g,atoms

def source_controls(world,g):
 a=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
 c=mp.log(5/mp.pi)+mp.digamma(mp.mpf('.75')) if world=='dh' else -mp.euler-mp.log(8*mp.pi)-mp.pi/2
 atoms=arithmetic(world)
 controls=[]
 for m in (2,4,8):
  L=mp.log(m);x=mp.exp(-L/2);tail=mp.atanh(x)+(-1 if world=='dh' else 1)*mp.atan(x)
  arch=2/L*mp.quad(lambda s:s*mp.exp(-a*s)/(-mp.expm1(-2*s)),[0,L])+2*tail
  A=c+arch-2*mp.fsum(weight*(1-t/L) for t,weight,n in atoms if t<L)
  if world!='dh':A+=32*mp.sinh(L/4)**2/L
  if world=='plant':
   w=2*mp.pi/mp.log(2)+mp.j/4;A-=8/L*mp.re((mp.cos(w*L)-1)/w**2)
  controls.append({'m':m,'g_return_error':mp.nstr(abs(g(L)+L*A/2),20)})
 return controls

def run(world,hstr,dps=80,endstr='6',hinges=True):
 mp.mp.dps=dps;start=time.monotonic();h=mp.mpf(hstr);end=mp.mpf(endstr);n=int(mp.floor(end/h));g,atoms=g_function(world,end)
 gs=[g(k*h) for k in range(n+1)];K=mp.matrix(n);LL=mp.eye(n);D=[];rows=[]
 for i in range(n):
  for j in range(n):K[i,j]=gs[abs(i-j)]-gs[i+1]-gs[j+1]
 floats=np.array(K.tolist(),dtype=float);negative=0;stop=None
 for j in range(n):
  # Solve L_old y=b. The Schur defect retains the signs of every D pivot.
  for k in range(j):LL[j,k]=(K[j,k]-mp.fsum(LL[j,l]*D[l]*LL[k,l] for l in range(k)))/D[k]
  schur=K[j,j]-mp.fsum(LL[j,k]**2*D[k] for k in range(j))
  guard=mp.power(10,-dps+20)*max(1,abs(K[j,j]),mp.fsum(abs(LL[j,k]**2*D[k]) for k in range(j)))
  if abs(schur)<=guard:stop={'prefix':j+1,'schur':str(schur),'guard':str(guard),'reason':'nonstructural pivot unresolved; no truncated pseudoinverse'};break
  D.append(schur);negative+=schur<0
  ev=eigvalsh(floats[:j+1,:j+1],check_finite=False);floor=100*np.finfo(float).eps*(j+1)*max(1,float(np.linalg.norm(floats[:j+1,:j+1],ord=np.inf)))
  rows.append({'world':world,'h':hstr,'dps':dps,'prefix':j+1,'t':mp.nstr((j+1)*h,20),'schur':mp.nstr(schur,dps),'schur_guard':mp.nstr(guard,8),'negative_inertia':negative,'positive_inertia':j+1-negative,'structural_zero_inertia':1,'range_guard':'PASS structural zero removed; remaining prefix nonsingular','float_eigen_min':ev[0],'float_eigen_max':ev[-1],'float_floor':floor,'float_resolved_negative':int(sum(ev < -floor)),'float_unresolved':int(sum(abs(ev)<=floor))})
  if (j+1)%40==0:print(world,hstr,dps,'prefix',j+1,'negative',negative,flush=True)
 tag=f'{world}_h{hstr}_dps{dps}'
 with (OUT/f'{tag}.csv').open('w',newline='') as f:wri=csv.DictWriter(f,fieldnames=rows[0]);wri.writeheader();wri.writerows(rows)
 residual=mp.norm(K[:len(D),:len(D)]-LL[:len(D),:len(D)]*mp.diag(D)*LL[:len(D),:len(D)].T)
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':world,'h':hstr,'dps':dps,'end':endstr,'count':len(D),'stop':stop,'first_negative_t':next((r['t'] for r in rows if r['negative_inertia']),None),'first_negative_schur_t':next((r['t'] for r in rows if mp.mpf(r['schur'])<0),None),'LDL_residual_frobenius':mp.nstr(residual,30),'constant_mode_controls':source_controls(world,g),'g_values':[mp.nstr(v,dps) for v in gs],'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256((OUT/'SOURCE.md').read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'all_eigenvalues_float64':[]}
 # Full spectra retained separately; float sign floor is in prefix CSV.
 for j in range(len(D)):result['all_eigenvalues_float64'].append(eigvalsh(floats[:j+1,:j+1],check_finite=False).tolist())
 (OUT/f'{tag}.json').write_text(json.dumps(result,indent=2)+'\n')
 if hinges:
  hr=[];eps=mp.mpf('1e-7')
  for threshold,weight,integer in atoms:
   if threshold>end:continue
   # Keep all old regular-grid samples strictly before a-eps fixed for both sides.
   q=int(mp.floor((threshold-eps)/h));q=min(q,len(D));old=[(i+1)*h for i in range(q)]
   def defect(t):
    b=[g(t-s)-g(t)-gs[i+1] for i,s in enumerate(old)];y=[]
    for i in range(q):y.append(b[i]-mp.fsum(LL[i,k]*y[k] for k in range(i)))
    return -2*g(t)-mp.fsum(y[i]**2/D[i] for i in range(q))
   vals=[defect(threshold+s*eps) for s in (-1,0,1)]
   hr.append({'world':world,'h':hstr,'n':integer,'threshold':mp.nstr(threshold,30),'coefficient':mp.nstr(weight,30),'fixed_history_count':q,'eps':str(eps),'schur_left':mp.nstr(vals[0],40),'schur_at':mp.nstr(vals[1],40),'schur_right':mp.nstr(vals[2],40),'left_slope':mp.nstr((vals[1]-vals[0])/eps,30),'right_slope':mp.nstr((vals[2]-vals[1])/eps,30),'slope_jump':mp.nstr((vals[2]-2*vals[1]+vals[0])/eps,30)})
  with (OUT/f'{tag}_hinges.csv').open('w',newline='') as f:wri=csv.DictWriter(f,fieldnames=hr[0]);wri.writeheader();wri.writerows(hr)
 print('DONE',world,hstr,dps,result['first_negative_t'],time.monotonic()-start,flush=True)
 return result
if __name__=='__main__':run(sys.argv[1],sys.argv[2],int(sys.argv[3]) if len(sys.argv)>3 else 80,hinges='--no-hinges' not in sys.argv)
