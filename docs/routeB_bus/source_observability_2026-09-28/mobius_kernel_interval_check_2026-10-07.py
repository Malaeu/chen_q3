from fractions import Fraction as F
from math import isqrt
from functools import lru_cache
N=32
S=10**20

def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[1],-a[0])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 v=[x*y for x in a for y in b];return(min(v),max(v))
def point(x):return(F(x),F(x))
def inv(a):
 assert a[0]>0
 return(1/a[1],1/a[0])
def scale(a,k):return mul(a,point(k))
@lru_cache(None)
def sqrt(q):
 q=F(q);k=isqrt(q.numerator*q.denominator*S*S)
 return(F(k,q.denominator*S),F(k+1,q.denominator*S))
def log_unit(q):
 z=(q-1)/(q+1)
 low=2*sum((z**(2*j+1)/F(2*j+1) for j in range(N)),F(0))
 err=2*z**(2*N+1)/((2*N+1)*(1-z*z))
 return(low,low+err)
@lru_cache(None)
def log(q):
 q=F(q);k=0
 while q>=2:q/=2;k+=1
 while q<1:q*=2;k-=1
 return add(log_unit(q),scale(log_unit(F(2)),k))
def mu(n):
 out=1;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;out=-out
   if n%p==0:return 0
  p+=1
 return -out if n>1 else out

def calculate(x):
 total=point(0)
 for d in range(1,x+1):
  m=mu(d)
  if not m:continue
  z=F(x,d);s=log(z);H=point(0)
  for k in range(1,x//d+1):
   H=add(H,mul(mul(log(F(k)),inv(sqrt(F(k)))),sub(s,log(F(k)))))
  H0=add(add(scale(mul(sqrt(z),sub(s,point(4))),4),scale(s,4)),point(16))
  total=add(total,scale(mul(inv(sqrt(F(d))),sub(H0,H)),m))
 return total
for x,lo,hi in [(10,F(16,1000),F(18,1000)),(100,F(-85,1000),F(-83,1000))]:
 a,b=calculate(x)
 assert lo<a<=b<hi
 print(f'x={x}: exact rational enclosure inside ({lo},{hi}); width < 1e-12:',b-a<F(1,10**12))
