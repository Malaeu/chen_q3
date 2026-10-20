from fractions import Fraction as Q
from collections import Counter
from math import gcd
from pathlib import Path
import json, hashlib

def mu(n):
    s=1;p=2
    while p*p<=n:
        if n%p==0:
            n//=p;s=-s
            if n%p==0:return 0
            while n%p==0:n//=p
        p+=1
    return -s if n>1 else s

def faclog(n):
    out=Counter();p=2
    while p*p<=n:
        while n%p==0:out[p]+=1;n//=p
        p+=1
    if n>1:out[n]+=1
    return out

def normc(x):return {k:v for k,v in x.items() if v}
def smat(A,B):return tuple(tuple(a+b for a,b in zip(x,y)) for x,y in zip(A,B))
def cmat(s,A):return tuple(tuple(s*a for a in row) for row in A)
def mmat(A,B):return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(len(A))) for j in range(len(A))) for i in range(len(A)))
def zmat(n=2):return tuple(tuple(Q(0) for _ in range(n)) for _ in range(n))
def summ(A):
    out=zmat()
    for a in A:out=smat(out,a)
    return out

def psd2(A):
    return A[0][1]==A[1][0] and A[0][0]>=0 and A[1][1]>=0 and A[0][0]*A[1][1]-A[0][1]**2>=0

stats=Counter()
# Exact log coefficients: each atom carries log(p) as formal independent symbol.
for m in (12,17,24,31,48,64):
 for R in (2,3,5):
  if R>=m:continue
  direct={n:Counter() for n in range(1,m+1)}
  blocked={n:Counter() for n in range(1,m+1)}
  for d in range(R+1,m+1):
   for k in range(1,m//d+1):
    for p,e in faclog(k).items():direct[d*k][p]+=mu(d)*e
  D=R
  while D<m:
   K=1
   while K<=m:
    for d in range(D+1,min(2*D,m)+1):
     for k in range(K,min(2*K-1,m//d)+1):
      for p,e in faclog(k).items():blocked[d*k][p]+=mu(d)*e
    K*=2
   D*=2
  for n in range(1,m+1):
   assert normc(direct[n])==normc(blocked[n]);stats['atom_reassemblies']+=1
# Actual mu gcd identity including all common-prime square obstructions.
for d in range(1,81):
 for e in range(1,81):
  g=gcd(d,e);a=d//g;b=e//g
  rhs=mu(g)**2*mu(a)*mu(b)*(gcd(g,a*b)==1)
  assert mu(d)*mu(e)==rhs;stats['mu_gcd_checks']+=1
# Noncommuting symmetric matrix Fejer identity for all endpoints.
for D in range(1,10):
 X=[]
 for i in range(1,D+1):
  B=((Q(i, i+2),Q((-1)**i, i+1)),(Q((-1)**i,i+1),Q(2*i-3,i+3)))
  X.append(cmat(mu(D+i),B))
 windows=[]
 for j in range(2-D,D+1):
  windows.append(summ(X[n-1] for n in range(1,D+1) if j<=n<=j+D-1))
 assert summ(windows)==cmat(D,summ(X));stats['window_sum_checks']+=1
 G=cmat(Q(1,D),summ(mmat(C,C) for C in windows))
 expanded=summ(cmat(Q(D-abs(i-j),D),mmat(X[i],X[j])) for i in range(D) for j in range(D))
 assert G==expanded;stats['matrix_fejer_identities']+=1
 T=summ(X);bound=smat(cmat(Q(2*D-1,D),G),cmat(-1,mmat(T,T)))
 assert psd2(bound);stats['matrix_cs_psd_controls']+=1
# A concrete generic diagonal-discard failure: uses actual mu but not CCM B_d.
# D=4: mu(5)=-1, mu(6)=1; choose B5=-1, B6=1, B7=B8=0 -> both X=1.
D=4;a=[Q(1),Q(1),Q(0),Q(0)]
c0=sum(x*x for x in a)
G=c0+2*sum(Q(D-h,D)*sum(a[i]*a[i+h] for i in range(D-h)) for h in range(1,D))
assert G==Q(7,2) and c0==2 and G>c0
assert mu(2)*mu(4)==0 and mu(2)**2*mu(1)*mu(2)==-1
stats['planted_failures_detected']=2
# Original source proper-power coefficient: n=27,R=2 -> -2log3, not zero.
ell=Counter()
for d in range(3,28):
 if 27%d==0:
  for p,e in faclog(27//d).items():ell[p]+=mu(d)*e
assert normc(ell)=={3:-2};stats['proper_power_control']=1
# The naive-k diagonal cost balancing is algebraic, not a proved source estimate.
for eps in (Q(1,1000),Q(1,100),Q(1,32)):
 theta=Q(1,2)-eps
 assert eps+theta/2==(1-theta)/2==Q(1,4)+eps/2
 stats['conditional_exponent_controls']+=1
# Actual Mu does not force off-diagonal Fejer sign for a general positive weight.
positive_generic=[];negative_generic=[]
for D in range(2,80):
 a=[Q(mu(d)) for d in range(D+1,2*D+1)]
 off=2*sum(Q(D-h,D)*sum(a[i]*a[i+h] for i in range(D-h)) for h in range(1,D))
 if off>0 and not positive_generic:positive_generic=[D,str(off)]
 if off<0 and not negative_generic:negative_generic=[D,str(off)]
# Exploration is reported as observed; no sign is imposed as a passing test.
# The deliberately weighted exact control above is the only generic sign refutation.

out={"status":"PASS", "counts":dict(stats),"total_checks":sum(stats.values()),
     "generic_mu_constant_weight_first_positive":positive_generic,
     "generic_mu_constant_weight_first_negative":negative_generic,
     "not_ccm_sign_certificates":True,"arb_runs":0,"lean_runs":0,
     "exploratory_constant_weight_note":"No positive off-diagonal was found for D=2..79; a first run wrongly asserted both signs and stopped. That unsupported assertion is removed, not counted as a theorem or test.",
     "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
