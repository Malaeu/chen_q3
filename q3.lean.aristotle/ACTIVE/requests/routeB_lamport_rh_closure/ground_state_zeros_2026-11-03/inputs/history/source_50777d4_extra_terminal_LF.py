"""Literal even source; MP quadrature and shifted LDL diagnostic, not certificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np,gmpy2 as g,time,json,argparse
from pathlib import Path
from scipy.linalg import eigvalsh
P=Path(__file__).resolve().parent;OUT=P.parent/'matrices';g.get_context().precision=400
f=g.mpfr;pi=g.const_pi();one=f(1);zero=f(0)
def gauss(q):
 pairs=[]
 for i in range(1,(q+1)//2+1):
  x=g.cos(pi*f(4*i-1)/f(4*q+2))
  for it in range(20):
   a=one;b=x
   for k in range(2,q+1):a,b=b,((2*k-1)*x*b-(k-1)*a)/k
   der=q*(x*b-a)/(x*x-1);dx=b/der;x-=dx
   if abs(dx)<f('1e-115'):break
  w=2/((1-x*x)*der*der);pairs.extend([(-x,w),(x,w)])
 return sorted(pairs)
def coefficient(M):
 tau=(g.sqrt(10-2*g.sqrt(5))-2)/(g.sqrt(5)-1);a=[zero,one,tau,-tau,-one];bd=[zero]*(M+1);bz=[zero]*(M+1)
 for n in range(2,M+1):
  bd[n]=a[n%5]*g.log(n)-sum((bd[d]*a[(n//d)%5] for d in range(2,n) if n%d==0),zero)
  for p in range(2,n+1):
   if n%p:continue
   k=n
   while k%p==0:k//=p
   if k==1:bz[n]=g.log(p)
   break
 return bz,bd
def build(m,q):
 L=g.log(m);nodes=gauss(q);y=np.array([(f(p)+(z+1)/2)/8 for p in range(8) for z,w in nodes],object);weights=np.array([w/16 for p in range(8) for z,w in nodes],object)
 x=L*y;co=np.array([g.cos(2*pi*v) for v in y],object);si=np.array([g.sin(2*pi*v) for v in y],object);cs=np.array([one]*len(y),object);sn=np.array([zero]*len(y),object)
 j0=np.array([g.exp(-v/2)/(-g.expm1(-2*v)) for v in x],object);wz=L*weights*j0;wd=wz*np.array([g.exp(-v) for v in x],object);mom=[[],[]];diag=[[],[]]
 for n in range(m+1):
  term=2*y+2*(1-y)*(1-cs)+(sn/(pi*n) if n else zero)
  for k,ww in enumerate([wz,wd]):mom[k].append(np.dot(ww,sn));diag[k].append(np.dot(ww,term))
  cs,sn=cs*co-sn*si,sn*co+cs*si
 bs=coefficient(m);r=np.array([g.log(k)/L for k in range(2,m)],object);co=np.array([g.cos(2*pi*v) for v in r],object);si=np.array([g.sin(2*pi*v) for v in r],object);cs=np.array([one]*len(r),object);sn=np.array([zero]*len(r),object);ps=[[],[]];pd=[[],[]];ww=[np.array([b[k]/g.sqrt(k) for k in range(2,m)],object) for b in bs]
 for n in range(m+1):
  term=2*(1-r)*cs-(sn/(pi*n) if n else zero)
  for k in range(2):ps[k].append(np.dot(ww[k],sn));pd[k].append(np.dot(ww[k],term))
  cs,sn=cs*co-sn*si,sn*co+cs*si
 ds=[one]+[g.sqrt(2)]*m;out={};z=g.exp(-L/2)
 for k,world in enumerate(['zeta','dh']):
  c=-g.const_euler()-g.log(8*pi/(5 if k else 1))+ (pi/2 if k else -pi/2);tail=g.atanh(z)+(-g.atan(z) if k else g.atan(z));beta=[mom[k][n]+ps[k][n] for n in range(m+1)];A=np.empty((m+1,m+1),object)
  for i in range(m+1):
   A[i,i]=c+diag[k][i]+2*tail-pd[k][i]
   for j in range(i+1,m+1):A[i,j]=A[j,i]=ds[i]*ds[j]/pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
  if not k:
   pole=np.array([4*g.sqrt(2)*ds[n]*L**f('1.5')*g.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(m+1)],object);A+=np.outer(pole,pole)
  out[world]=A
 w=g.mpc(2*pi/g.log(2),f('.25'));ce=np.array([2*ds[n]*w*g.sin(w*L/2)/(g.sqrt(L)*(w*w-(2*pi*n/L)**2)) for n in range(m+1)],object);out['plant']=out['zeta']+np.array([[4*(a*b).real for b in ce] for a in ce],object)
 return out

def ldl(A,shift):
 n=len(A);L=np.empty((n,n),object);L.fill(zero);D=np.empty(n,object)
 for i in range(n):
  for j in range(i):L[i,j]=(A[i,j]-np.dot(L[i,:j]*D[:j],L[j,:j]))/D[j]
  D[i]=A[i,i]+shift-np.dot(L[i,:i]*D[:i],L[i,:i]);L[i,i]=one
  if not D[i]:return dict(status='ZERO_PIVOT_UNRESOLVED')
 return dict(negative=sum(v<0 for v in D),min_abs_pivot=str(min(abs(v) for v in D)),status='APPROXIMATE_UNPIVOTED_LDL')
def native_counts(M,guard):
 import sys
 sys.path.insert(0,str(P.parent))
 from native_frame import ldl_counts
 result=ldl_counts(M,[-guard,zero,guard],400)
 return {str(s):dict(negative=int(v),status='APPROXIMATE_NATIVE_MPFR_UNPIVOTED_LDL',min_abs_pivot=None,pivot_guard_status='exact-zero pivot traps; minimum nonzero pivot not reported by native helper') for s,v in zip([-1,0,1],result)}
def run(m,q=192,compare=False):
 start=time.monotonic();A=build(m,q);buildsec=time.monotonic()-start;other=build(m,256) if compare else None;res=[]
 for world,M in A.items():
  Af=np.array(M,float);ev=eigvalsh(Af);scale=max(1.,max(abs(ev)));radius=64*np.finfo(float).eps*(m+1)*scale;entrydiff=max(abs(v) for v in (M-other[world]).flat) if other else None
  guard=max(f('1e-70'),f(4*(m+1))*entrydiff) if other else f('1e-70');counts={str(s):ldl(M,s*guard) for s in [-1,0,1]} if not os.environ.get('USE_NATIVE_LDL') else native_counts(M,guard);lower=counts['1'].get('negative');upper=counts['-1'].get('negative');meta=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,N=m,bits=400,GL_order=q,panels=8,source='literal even CCM arch+tail+signed atoms; zeta pole only; plant +4Re(eeT)',source_build_seconds=buildsec,seconds=time.monotonic()-start,guard=str(guard),guard_status='empirical paired-order pilot; NOT interval source bound' if compare else 'provisional 1e-70; must be justified against paired-order pilot',paired_order_entry_difference=str(entrydiff) if compare else None,ldl=counts,negative_count_range=[lower,upper],float_numeric_radius=radius,float_minimum=float(ev[0]),float_maximum=float(ev[-1]))
  np.savez_compressed(OUT/f'{world}_m{m}.npz',A=Af,eigenvalues=ev,lambda_=ev,m=m,numeric_radius=radius)
  (OUT/f'{world}_m{m}.json').write_text(json.dumps(meta,indent=2)+'\n');res.append(meta)
 print(json.dumps(dict(m=m,build_seconds=buildsec,total_seconds=time.monotonic()-start,worlds=[dict(world=r['world'],counts=r['negative_count_range'],difference=r['paired_order_entry_difference']) for r in res])),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--ms',nargs='+',type=int,required=True);p.add_argument('--compare',action='store_true');p.add_argument('--order',type=int,default=192);a=p.parse_args()
 for m in a.ms:run(m,a.order,a.compare)

