"""Independent heat-convolved literal source entries, no zero-side positivity input."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np,mpmath as mp,json
from scipy.special import erf
from scipy.integrate import quad
from run import P,carrier,census,matrix
mp.mp.dps=100

def coeff(M,w):
 if w=='zeta':
  b=np.zeros(M+1)
  for p in range(2,M+1):
   if all(p%d for d in range(2,int(p**.5)+1)):
    k=p
    while k<=M:b[k]=np.log(p);k*=p
  return b
 tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);a=[0,1,tau,-tau,-1];b=[mp.mpf(0)]*(M+1)
 for n in range(2,M+1):b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5]for d in range(2,n)if n%d==0)
 return np.array(b,float)
def heatR(s,i,j,L,y):
 def moments(k):
  tot0=0j;tot1=0j
  for t in [s,-s]:
   shift=t+2j*y*k
   I=np.exp(-y*k*k+1j*k*t)*.5*(erf((L-shift)/(2*np.sqrt(y)))-erf(-shift/(2*np.sqrt(y))))
   G=lambda v:np.exp(-v*v/(4*y))/np.sqrt(4*np.pi*y)
   J=shift*I+2*y*(G(t)-G(t-L)*np.exp(1j*k*L));tot0+=I;tot1+=J
  return tot0,tot1
 if i==j:
  I,J=moments(2*np.pi*i/L);return (I-J/L).real-(I.imag/(2*np.pi*i)if i else 0)
 Ii,_=moments(2*np.pi*i/L);Ij,_=moments(2*np.pi*j/L);di=1 if i==0 else np.sqrt(2);dj=1 if j==0 else np.sqrt(2)
 return -di*dj/(2*np.pi)*(i*Ii.imag-j*Ij.imag)/(i*i-j*j)
def entry(m,i,j,y,w):
 L=np.log(m);R=lambda s:heatR(s,i,j,L,y);R0=R(0);alpha=.5 if w=='zeta'else 1.5
 c=-float(mp.euler)-np.log(8*np.pi/(1 if w=='zeta'else 5))+(-1 if w=='zeta'else 1)*np.pi/2
 def fun(s):return 2*np.exp(-alpha*s)/(-np.expm1(-2*s))*(R0-R(s))
 cut=12*np.sqrt(y);knots=sorted(set([1e-7,cut,L-cut,L,L+cut,30.]));knots=[v for v in knots if v>1e-7];lo=1e-7;arch=0.;error=0.
 for hi in knots:
  if hi<=lo:continue
  v,e=quad(fun,lo,hi,epsabs=2e-10,epsrel=2e-10,limit=250);arch+=v;error+=e;lo=hi
 # Outside30 arch tail: R(s)~0, exact tail integrated numerically.
 v,e=quad(lambda s:2*np.exp(-alpha*s)/(-np.expm1(-2*s))*R0,30,200,epsabs=1e-13);arch+=v;error+=e
 M=int(np.ceil(np.exp(L+cut)));b=coeff(M,w);prime=-2*sum(b[n]/np.sqrt(n)*R(np.log(n))for n in range(2,M+1));pole=0
 if w=='zeta':
  ds=lambda n:1 if n==0 else np.sqrt(2)
  F=lambda n:4*ds(n)*L**1.5*np.sinh(L/4)/(L*L+16*np.pi*np.pi*n*n)
  pole=2*np.exp(y/4)*F(i)*F(j)
 return dict(value=c*R0+arch+prime+pole,arch=arch,constant=c*R0,arithmetic=prime,pole=pole,quad_error_estimate=error,prime_n_max=M,prime_tail_distance_sigma=12/np.sqrt(2))
rows=[]
for m in [310,600]:
 for w in ['zeta','dh']:
  z,E=carrier(m,census(w));Om=2*np.pi*m/np.log(m)
  for c in [8.,16.,32.]:
   y=c/Om**2;A=matrix(z,E,y)
   for i,j in [(0,0),(1,1),(m,m),(m-1,m),(0,m)]:
    r=entry(m,i,j,y,w);r.update(m=m,world=w,c=c,i=i,j=j,zero_side=float(A[i,j]),absolute_difference=abs(r['value']-A[i,j]));rows.append(r);print(m,w,c,i,j,r['absolute_difference'],flush=True)
(P/'SOURCE_CHECK.json').write_text(json.dumps(rows,indent=2)+'\n')
