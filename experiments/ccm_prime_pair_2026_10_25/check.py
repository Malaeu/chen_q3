import math,json
from collections import Counter
from pathlib import Path
def factors(n):
 c=Counter();p=2
 while p*p<=n:
  while n%p==0:c[p]+=1;n//=p
  p+=1
 if n>1:c[n]+=1
 return c
def d(n,m):
 return Counter({p:sum(p**j<=m for j in range(1,e+1)) for p,e in factors(n).items()})
def signed(items):
 out=Counter()
 for sign,v in items:
  for p,c in v.items():out[p]+=sign*c
 return {p:c for p,c in out.items() if c}
checks=0
for m in range(1,65):
 for a in range(1,33):
  for p,q in [(2,3),(2,5),(3,7),(5,11)]:
   if math.gcd(a,p*q)>1:continue
   assert not signed([(1,d(a*p*q,m)),(-1,d(a*p,m)),(-1,d(a*q,m)),(1,d(a,m))]);checks+=1
   for n,prime in [(a*p,p),(a*q,q)]:
    assert signed([(1,d(n,m)),(-1,d(a,m)),(-1,Counter({prime:int(prime<=m)}))])=={};checks+=1
# Exact coefficient-vector algebra checks include a and apq > m, no tail deletion.
out={'status':'PASS_EXACT_PRIME_LOG_COEFFICIENTS','checks':checks,'m_range':[1,64],'a_range':[1,32],'source_CCM_evaluations':0,'interval_runs':0,'scope':'finite divisor coefficient only; theta weighted defect is retained analytically'}
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
