"""Independent mpmath source builder, retained from EDGE_LAW_RELLICH.
No GMP QR/LDL code is reused.
"""
import mpmath as mp
from functools import lru_cache
def mangoldt(n):
 for p in range(2,n+1):
  if n%p==0:
   k=n
   while k%p==0:k//=p
   return mp.log(p) if k==1 else mp.mpf(0)
 return mp.mpf(0)

def coeffs(m,world):
 if world=='zeta':return [mp.mpf(0)]+[mangoldt(n) for n in range(1,m+1)]
 t=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
 a=[mp.mpf(0),mp.mpf(1),t,-t,mp.mpf(-1)];b=[mp.mpf(0)]*(m+1)
 for n in range(2,m+1):b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
 return b

@lru_cache(None)
def nodes(order):
 z,w=mp.gauss_quadrature(order,'legendre')
 return [((mp.mpf(p)+(v+1)/2)/8,ww/16) for p in range(8) for v,ww in zip(z,w)]

def build(m,world,order):
 L=mp.log(m);d=m+1;b=coeffs(m,world);alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5')
 sm=[mp.mpf(0)]*d;di=sm.copy();ps=sm.copy();pd=sm.copy()
 for y,w in nodes(order):
  x=L*y;wt=L*w*mp.exp(-alpha*x)/(-mp.expm1(-2*x));co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   sm[n]+=wt*sn;di[n]+=wt*(2*y+2*(1-y)*(1-cn)+(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 for k in range(2,m):
  if not b[k]:continue
  y=mp.log(k)/L;wt=b[k]/mp.sqrt(k);co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   ps[n]+=wt*sn;pd[n]+=wt*(2*(1-y)*cn-(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;beta=[sm[i]+ps[i] for i in range(d)]
 c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2 if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
 aa=mp.exp(-L/2);tail=mp.atanh(aa)+(mp.atan(aa) if world=='zeta' else -mp.atan(aa));A=mp.zeros(d)
 pole=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(d)])
 for i in range(d):
  A[i,i]=c+di[i]+2*tail-pd[i]
  for j in range(i+1,d):A[i,j]=A[j,i]=ds[i]*ds[j]/mp.pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
 if world=='zeta':A+=pole*pole.T
 return A,c,alpha,tail,pole
