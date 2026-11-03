"""Further split existing pinned C,B; never rebuild their source or quiet frames."""
import math
import numpy as np
import mpmath as mp

def primes(M):return [p for p in range(2,M+1)if all(p%q for q in range(2,math.isqrt(p)+1))]
def make_knobs(m,C,B,world='zeta',mp_mode=False,atom2=None):
 ps=primes(m);d=m+1;lib=mp if mp_mode else np;log=mp.log if mp_mode else math.log;sqrt=mp.sqrt if mp_mode else math.sqrt;sin=mp.sin if mp_mode else math.sin;cos=mp.cos if mp_mode else math.cos;pi=mp.pi if mp_mode else math.pi
 zero=lambda:mp.zeros(d)if mp_mode else np.zeros((d,d))
 L=log(m);ds=[1]+[sqrt(2)]*m
 if world=='dh':P=zero()
 else:
  p=[4*sqrt(2)*ds[n]*L**(mp.mpf('1.5')if mp_mode else 1.5)*lib.sinh(L/4)/(L*L+16*pi*pi*n*n)for n in range(d)]
  P=mp.matrix(p)*mp.matrix(p).T if mp_mode else np.outer(p,p)
 groups={p:zero()for p in ps};nonprime=zero();co=[0]*(m+1)
 if world=='dh':
  tau=(sqrt(10-2*sqrt(5))-2)/(sqrt(5)-1);a=[0,1,tau,-tau,-1]
  for n in range(2,m):co[n]=a[n%5]*log(n)-sum(co[j]*a[(n//j)%5]for j in range(2,n)if n%j==0)
 else:
  for p in ps:
   n=p
   while n<m:co[n]=log(p);n*=p
 if world=='double2':co[2]*=2
 def atom(n):
  M=zero();r=log(n)/L;w=co[n]/sqrt(n);si=[sin(2*pi*i*r)for i in range(d)];cs=[cos(2*pi*i*r)for i in range(d)]
  for i in range(d):
   M[i,i]=-w*(2*(1-r)*cs[i]-(si[i]/(pi*i)if i else 0))
   for j in range(i+1,d):M[i,j]=M[j,i]=ds[i]*ds[j]/pi*w*(i*si[i]-j*si[j])/(i*i-j*j)
  return M
 powers={}
 for p in ps:
  n=p
  while n<m:powers[n]=p;n*=p
 for n in range(2,m):
  if co[n]==0:continue
  if n in powers:groups[powers[n]]+=atom(n)
  else:nonprime+=atom(n)
 labels=['C_Gamma','C_pole']+[f'B_{p}'for p in ps];components=[C-P,P]+[groups[p]for p in ps]
 if world=='dh':labels+=['B_nonprime'];components+=[nonprime]
 return labels,components
