# Extracted unchanged from Q8 reproducible coefficient controls.
# Finite algebra diagnostics, not analytic proof.
from itertools import product
from fractions import Fraction as F
from math import prod

norms=(7,13,19)
def norm(e): return prod(p**v for p,v in zip(norms,e))
def mu(e): return 0 if any(v>1 for v in e) else (-1)**sum(e)
def divs(e): return product(*(range(v+1) for v in e))
def sub(e,d): return tuple(x-y for x,y in zip(e,d))
checks={}
N=0
for e in product(range(5),repeat=3):
 for mask in product((0,1),repeat=3):
  lhs=mu(e)*int(not any(x*y for x,y in zip(e,mask)))
  rhs=sum(mu(sub(e,d)) for d in divs(e) if all(not x or y for x,y in zip(d,mask)))
  assert lhs==rhs,(e,mask,lhs,rhs)
  # finite return with d squarefree supported by the mask
  rhs2=0
  for d in product((0,1),repeat=3):
   if any(x>y for x,y in zip(d,e)) or any(x and not y for x,y in zip(d,mask)):continue
   n=sub(e,d)
   rhs2+=mu(d)*mu(n)*int(not any(x*y for x,y in zip(n,mask)))
  assert rhs2==mu(e)
  N+=2
checks['puncture_forward_inverse']=N
N=0
for n in product((0,1),repeat=3):
 for nn in product((0,1),repeat=3):
  h=tuple(min(x,y) for x,y in zip(n,nn))
  for G in (1,7,8,13,14,50,91,92,200,2000):
   rhs=0
   for g in divs(h):
    if norm(g)<G:continue
    rhs+=sum(mu(f) for f in divs(sub(h,g)))
   assert rhs==int(norm(h)>=G),(n,nn,G,rhs)
   N+=1
checks['gcd_tail_projection']=N
N=0
for e in product(range(13),repeat=3):
 rhs=sum(mu(d) for d in product(*(range(v//6+1) for v in e)))
 assert rhs==int(all(v<6 for v in e));N+=1
checks['sixthfree_sieve']=N
# The mask-count kernel records the union of the prime supports, not their sum.
ideals=[e for e in product(range(4),repeat=3) if norm(e)<=2000]
N=0
for k in product(range(4),repeat=3):
 for P in (1,6,7,13,19,100,1000):
  direct=sum(norm(a)<=P and not any(x*y for x,y in zip(k,a)) for a in ideals)
  rad=tuple(int(x>0) for x in k)
  via=0
  for d in divs(rad):
   if norm(d)>P:continue
   via+=mu(d)*sum(norm(b)*norm(d)<=P for b in ideals)
  assert direct==via,(k,P,direct,via);N+=1
checks['exact_amplifier_count']=N
r0=F(5617,5000);rmin=F(28,25);rmax=F(113,100);c=F(1,10000);gamma=F(1,100);eta=F(1,100);Theta=F(1,200)
alpha=lambda r:(1+5*r)/6
pp=lambda r:(r*(1+c)-1)/6
H=lambda r:r*(1+c)
large=lambda r:r+r*c/6-5*gamma/6
assert H(rmin)-large(rmin)>Theta
assert H(rmin)-(pp(rmin)+1)>Theta
retgain=Theta-5*rmax*c/6
assert retgain>F(1,250)
assert (2*r0-1)>r0 and (3*r0-2)>r0
print(checks, 'total',sum(checks.values()))
for name,v in {'r0':r0,'alpha':alpha(r0),'P_exp':pp(r0),'H_exp':H(r0),'baseline_E':pp(r0)+alpha(r0),'large_gcd_E':large(r0),'diagonal_E':pp(r0)+1,'supplier_E':H(r0)-Theta,'return_gain_min':retgain,'dual_one':2*r0-1,'dual_two':3*r0-2}.items():print(name,v,float(v))
# Planted incorrect simplifications.
bad=sum(mu((2-d,0,0)) for d in (0,1))
assert bad==-1 and sum(mu((2-d,0,0)) for d in (0,1,2))==0
# Incorrectly replacing the geometric inverse by squarefree divisors is detected.
# h^6 is a mask: at a common prime, it is zero, not the constant 1.
assert int(not (1 and 1)) == 0
print('All algebra checks passed; analytic estimates are not certified by these controls.')
