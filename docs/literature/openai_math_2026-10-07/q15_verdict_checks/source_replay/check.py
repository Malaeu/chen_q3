from pathlib import Path
import json
from collections import Counter
N=128
fac=[Counter() for _ in range(N+1)]
for n in range(2,N+1):
 x=n
 for p in range(2,n+1):
  while x%p==0:fac[n][p]+=1;x//=p
mu=[0]+[(-1)**len(fac[n]) if all(e==1 for e in fac[n].values()) else 0 for n in range(1,N+1)]
lam=[Counter({next(iter(fac[n])):1}) if len(fac[n])==1 else Counter() for n in range(N+1)]
def add(out,v,k=1):
 for p,e in v.items():out[p]+=k*e
cases=0;missing_K=0;missing_II=0
for U in range(1,9):
 for V in range(1,9):
  for n in range(1,N+1):
   I=Counter();J=lam[n] if n<=V else Counter();K=Counter();II=Counter()
   for d in range(1,n+1):
    if n%d:continue
    v=n//d
    if d<=U:
     add(I,fac[v],mu[d])
     for k in range(1,min(V,v)+1):
      if v%k==0:add(K,lam[k],mu[d])
    else:
     for k in range(V+1,v+1):
      if v%k==0:add(II,lam[k],mu[d])
   out=Counter();add(out,I);add(out,J);add(out,K,-1);add(out,II);add(out,lam[n],-1)
   assert all(x==0 for x in out.values()),(n,U,V,out)
   missing_K+=any(K.values());missing_II+=any(II.values());cases+=1
assert missing_K and missing_II
result={'status':'PASS_EXACT_FORMAL_LOG_COEFFICIENTS','cases':cases,'n_max':N,'U_V_range':[1,8],'omitted_K_detected_cases':missing_K,'omitted_II_detected_cases':missing_II,'full_CCM_spectrum_computed':False,'new_arithmetic_exponent':None}
Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
