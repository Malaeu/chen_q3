"""Outward-rounded rational fixed-point interval certificate, not Arb or Lean.
All transcendental enclosures use finite Taylor sums with a proved remainder sign.
"""
from fractions import Fraction as F
from math import factorial
import json,time,hashlib
from pathlib import Path
P=144; S=1<<P
class I:
 __slots__=('lo','hi')
 def __init__(self,a=0,b=None,raw=False):
  if raw:self.lo=a;self.hi=b;return
  a=F(a);b=a if b is None else F(b)
  self.lo=(a.numerator*S)//a.denominator
  self.hi=-((-b.numerator*S)//b.denominator)
 @staticmethod
 def c(x): return x if isinstance(x,I) else I(x)
 def __add__(self,x):
  x=I.c(x);return I(self.lo+x.lo,self.hi+x.hi,True)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo,True)
 def __sub__(self,x):return self+-I.c(x)
 def __rsub__(self,x):return I.c(x)+-self
 def __mul__(self,x):
  x=I.c(x);a=[self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi]
  return I(min(a)//S,-((-max(a))//S),True)
 __rmul__=__mul__
 def __truediv__(self,x):
  x=I.c(x)
  if x.lo<=0<=x.hi:raise ZeroDivisionError((x.lo,x.hi))
  vv=[F(a*S,b) for a in [self.lo,self.hi] for b in [x.lo,x.hi]]
  ll=min(vv);uu=max(vv)
  return I(ll.numerator//ll.denominator,-((-uu.numerator)//uu.denominator),True)
 def __rtruediv__(self,x):return I.c(x)/self
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  out=I(1);b=self
  while n:
   if n&1:out=out*b
   n//=2
   if n:b=b*b
  return out
 def floats(self):return [float(F(self.lo,S)),float(F(self.hi,S))]
 def exact(self):return [str(F(self.lo,S)),str(F(self.hi,S))]

def exp_endpoint_minus(a):
 assert a>=0
 k=max(0,a.bit_length()-P)
 y=I(F(a,S*(1<<k)))
 assert y.hi<=S
 term=I(1);sm=I(1);low=None
 for j in range(1,41):
  term=term*(-y)/j;sm=sm+term
  if j==39:low=sm.lo
 out=I(max(0,low),sm.hi,True)
 for j in range(k):out=out*out
 return out

def exp_minus(x):
 assert x.lo>=0
 return I(exp_endpoint_minus(x.hi).lo,exp_endpoint_minus(x.lo).hi,True)
N=6

def Jconst(x):return [I.c(x)]+[I(0) for _ in range(N)]
def Jadd(a,b):return [x+y for x,y in zip(a,b)]
def Jscale(a,c):return [x*c for x in a]
def Jmul(a,b):return [sum((a[j]*b[n-j] for j in range(n+1)),I(0)) for n in range(N+1)]
def Jinv(a):
 b=[1/a[0]]
 for n in range(1,N+1):b.append(-sum((a[j]*b[n-j] for j in range(1,n+1)),I(0))/a[0])
 return b
def JexpnegX(x,b):
 a=[-b*x*F(2**j,factorial(j)) for j in range(N+1)]
 e=[exp_minus(x*b)]
 for n in range(1,N+1):e.append(sum((j*a[j]*e[n-j] for j in range(1,n+1)),I(0))/n)
 return e
def Jlog(a):
 # Constant logarithm never used; higher coefficients use only rational arithmetic.
 l=[I(0)]
 for n in range(1,N+1):
  l.append((n*a[n]-sum((j*l[j]*a[n-j] for j in range(1,n)),I(0)))/(n*a[0]))
 return l
BASE=Path(__file__).parent
bounds=json.loads((BASE/'tail_bounds.json').read_text())
tail=[F(a) for a in bounds['tail_n4']]

POLYS=json.loads((BASE/'source_polys.json').read_text())
def horner(coeff,z):
 out=I(0)
 for c in coeff:out=out*z+F(c)
 return out
def rat_eval(data,z):return horner(data[0],z)/horner(data[1],z)
def source(x):
 z=x-3
 es={m:exp_minus(x*(m-1)) for m in [4,9]}
 ej=[]
 for j in range(N+1):
  v=sum((rat_eval(POLYS['eps'][str(m)][j],z)*es[m] for m in [4,9]),I(0))
  v=v+(I(0,tail[j]) if j%2==0 else I(-tail[j],0))
  ej.append(v/factorial(j))
 ej[0]=ej[0]+1
 L=Jlog(ej)
 vals=[]
 for j in [0,1,2,4]:vals.append(rat_eval(POLYS['qone'][str(j)],z)-L[j+2]*factorial(j+2))
 return tuple(vals)
names=['q-18','3q-qp','3q+qp','qpp','10q-qpp','q4+200q']
mins=[None]*6;fails=[];rows=[]
start=F(31,10);end=F(8);cells=2048;t0=time.time()
for i in range(cells):
 l=start+(end-start)*F(i,cells);u=start+(end-start)*F(i+1,cells)
 q,qp,qpp,q4=source(I(l,u))
 margins=[q-18,3*q-qp,3*q+qp,qpp,10*q-qpp,q4+200*q]
 vals=[x.lo for x in margins]
 for j,val in enumerate(vals):mins[j]=val if mins[j] is None else min(mins[j],val)
 if min(vals)<=0:fails.append({'cell':i,'x':[str(l),str(u)],'lower':[float(F(z,S)) for z in vals]})
 rows.append([str(l),str(u)]+[str(z) for z in vals])
# Semi-infinite x >= 8: all omitted epsilon derivatives are sign-alternating.
eb=[F(a) for a in bounds['tail_x8']]
eps=[I(0,a/factorial(j)) if j%2==0 else I(-a/factorial(j),0) for j,a in enumerate(eb)]
eps[0]=eps[0]+1
Lg=Jlog(eps)
Labs={j:max(abs(Lg[j].lo),abs(Lg[j].hi))*F(factorial(j),S) for j in [2,3,4,6]}
outer=[14-Labs[2],32-3*Labs[2]-Labs[3],32-3*Labs[2]-Labs[3],128-Labs[4],64-10*Labs[2]-Labs[4],6400-200*Labs[2]-Labs[6]]
report={'verifier':'exact outward-rounded dyadic intervals + rational Taylor bounds; not Arb or Lean','precision_bits':P,'domain':'[31/10,8] plus analytic tail x>=8','cells':cells,'finite_pass':not fails,'failed_cells':fails,'finite_min_lower_bounds':dict(zip(names,[float(F(z,S)) for z in mins])),'outer_log_derivative_abs':{str(k):str(v) for k,v in Labs.items()},'outer_positive_margins':dict(zip(names,[str(v) for v in outer])),'outer_pass':all(v>0 for v in outer),'elapsed_seconds':time.time()-t0}
(BASE/'source_cert_results.json').write_text(json.dumps(report,indent=2)+'\n')
(BASE/'source_cert_rows.json').write_text(json.dumps(rows)+'\n')
print(json.dumps(report,indent=2))
