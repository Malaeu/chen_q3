"""Literal even source; MP quadrature and shifted LDL diagnostic, not certificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np,gmpy2 as g,time,json,argparse
from pathlib import Path
from scipy.linalg import eigvalsh
P=Path(__file__).resolve().parent;OUT=P;g.get_context().precision=400
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
 bs=coefficient(m);r=np.array([g.log(k)/L for k in range(2,m)],object);co=np.array([g.cos(2*pi*v) for v in r],object);si=np.array([g.sin(2*pi*v) for v in r],object);cs=np.array([one]*len(r),object);sn=np.array([zero]*len(r),object);ps=[[] for _ in range(7)];pd=[[] for _ in range(7)];ww=[np.array([b[k]/g.sqrt(k) for k in range(2,m)],object) for b in bs];ww.extend([np.array([max(v,zero) for v in ww[0]],object),np.array([min(v,zero) for v in ww[0]],object),np.array([max(v,zero) for v in ww[1]],object),np.array([min(v,zero) for v in ww[1]],object),np.array([g.log(2)/g.sqrt(2) if k==2 else zero for k in range(2,m)],object)])
 for n in range(m+1):
  term=2*(1-r)*cs-(sn/(pi*n) if n else zero)
  for k in range(7):ps[k].append(np.dot(ww[k],sn));pd[k].append(np.dot(ww[k],term))
  cs,sn=cs*co-sn*si,sn*co+cs*si
 ds=[one]+[g.sqrt(2)]*m;out={};z=g.exp(-L/2)
 def form(beta,diagonal):
  M=np.empty((m+1,m+1),object)
  for i in range(m+1):
   M[i,i]=diagonal[i]
   for j in range(i+1,m+1):M[i,j]=M[j,i]=ds[i]*ds[j]/pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
  return M
 atom2=form(ps[6],[-v for v in pd[6]])
 for k,world in enumerate(['zeta','dh']):
  c=-g.const_euler()-g.log(8*pi/(5 if k else 1))+ (pi/2 if k else -pi/2);tail=g.atanh(z)+(-g.atan(z) if k else g.atan(z))
  C=form(mom[k],[c+diag[k][i]+2*tail for i in range(m+1)])
  B=form(ps[k],[-v for v in pd[k]])
  if not k:
   pole=np.array([4*g.sqrt(2)*ds[n]*L**f('1.5')*g.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(m+1)],object);C+=np.outer(pole,pole)
  pos=2 if k==0 else 4;Bp=form(ps[pos],[-v for v in pd[pos]]);Bn=form(ps[pos+1],[-v for v in pd[pos+1]])
  residual=max(abs(v)for v in (B-Bp-Bn).flat)
  signs={sign:dict(atom_count=sum((v>0 if sign=='positive_b' else v<0)for v in bs[k][2:m]),signed_weight_sum=str(sum((v for v in ww[k] if (v>0 if sign=='positive_b' else v<0)),zero)),matrix_trace=str(sum((Bp if sign=='positive_b' else Bn)[i,i]for i in range(m+1))),matrix_max_abs=str(max(abs(v)for v in (Bp if sign=='positive_b' else Bn).flat)))for sign in ['positive_b','negative_b']}
  out[world]=dict(C=C,B=B,A1=C+B,atom2=atom2,sign_groups=signs,sign_conservation_max_entry=str(residual))
 out['double2']=dict(C=out['zeta']['C'],B=out['zeta']['B']+atom2,A1=out['zeta']['A1']+atom2,atom2=atom2,sign_groups=out['zeta']['sign_groups'],sign_conservation_max_entry=out['zeta']['sign_conservation_max_entry'])
 out['double2']['sign_groups']=dict(out['zeta']['sign_groups'],extra_integer_2=dict(atom_count=1,signed_weight_sum=str(g.log(2)/g.sqrt(2)),matrix_trace=str(sum(atom2[i,i]for i in range(m+1))),matrix_max_abs=str(max(abs(v)for v in atom2.flat))))
 out['double2']['sign_conservation_max_entry']=str(f(out['zeta']['sign_conservation_max_entry'])+max(abs(v)for v in(out['double2']['B']-out['zeta']['B']-atom2).flat))
 return out
