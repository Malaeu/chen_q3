import importlib.util
from fractions import Fraction as F
from math import gcd
spec=importlib.util.spec_from_file_location('q54','docs/literature/openai_math_2026-10-07/q54_replay/check_q54.py'); q=importlib.util.module_from_spec(spec); spec.loader.exec_module(q)
count=0
for m in (2,6,12,24):
 U=q.mobius_matrix(m)
 distances=[[q.padd(q.pscale(q.padd(q.logp(n),q.logp(k)),F(1,2)),q.pscale(q.logp(gcd(n,k)),-1)) for k in range(1,m+1)] for n in range(1,m+1)]
 actual=q.ptr([[q.pmul(d,d) for d in row] for row in distances],U)
 for n in range(1,m+1):
  for k in range(1,m+1):
   fn,fk=q.fac(n),q.fac(k); primes=set(fn)|set(fk); expected={}
   if len(primes)==1:
    p=next(iter(primes)); a,b=fn.get(p,0),fk.get(p,0)
    val=F(2*max(a,b)-1,4) if min(a,b)==0 else -F(1,2)
    expected={(p,p):q.Q(val)}
   elif len(primes)==2:
    val=F(2)
    for p in primes:
     a,b=fn.get(p,0),fk.get(p,0)
     val*=(-F(1,2) if min(a,b)==0 else (1 if a==b else 0))
    if val: expected={tuple(sorted(primes)):q.Q(val)}
   assert actual[n-1][k-1]==expected,(n,k)
   count+=1
print('exact second derivative entries checked:',count)
