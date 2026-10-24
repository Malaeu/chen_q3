"""Exact finite controls for the Q15 paper calculation; not CCM sign certificates."""
from fractions import Fraction as F
from collections import Counter
from math import gcd, isqrt
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent
stats = Counter()
N = 160
fac = [Counter() for _ in range(N+1)]
for n in range(2,N+1):
    z=n
    for p in range(2,isqrt(n)+2):
        while z%p==0:
            fac[n][p]+=1; z//=p
    if z>1: fac[n][z]+=1
mu = [0]+[0 if any(e>1 for e in fac[n].values()) else (-1)**len(fac[n]) for n in range(1,N+1)]
phi=[0]+[sum(gcd(j,n)==1 for j in range(1,n+1)) for n in range(1,N+1)]
lam = [Counter({next(iter(fac[n])):1}) if len(fac[n])==1 else Counter() for n in range(N+1)]

def clean(c): return {k:v for k,v in c.items() if v}
def add(out, c, a=1):
    for p,e in c.items(): out[p]+=a*e

def nu(n,U): return sum(mu[d] for d in range(U+1,n+1) if n%d==0)
def sig(n,U): return sum(mu[d] for d in range(1,min(U,n)+1) if n%d==0)
def lcm(a,b): return a*b//gcd(a,b)
def harm(n): return sum((F(1,j) for j in range(1,n+1)), F())

# Complete actual arithmetic and both Type-II parenthesizations.
for U in range(1,9):
    for n in range(1,N+1):
        assert nu(n,U)==(1 if n==1 else 0)-sig(n,U)
        if n<=U: assert nu(n,U)==0
        stats['short_inverse_coefficients']+=1
    for V in range(1,9):
        for n in range(1,97):
            left=Counter();right=Counter()
            for d in range(U+1,n+1):
                if n%d: continue
                v=n//d
                for k in range(V+1,v+1):
                    if v%k==0:add(left,lam[k],mu[d])
            for a in range(U+1,n+1):
                if n%a==0 and n//a>V:add(right,lam[n//a],nu(a,U))
            assert clean(left)==clean(right)
            stats['two_typeII_coefficients']+=1

# Exact LCM energy, signed floor error and harmonic energy.
for U in range(1,17):
    Q=sum((F(mu[d]*mu[e],lcm(d,e)) for d in range(1,U+1) for e in range(1,U+1)),F())
    y={r:sum((F(mu[d],d) for d in range(r,U+1,r)),F()) for r in range(1,U+1)}
    G=sum((F(mu[r]**2,phi[r]) for r in range(1,U+1)),F())
    assert Q==sum((phi[r]*y[r]**2 for r in y),F())
    assert sum((mu[r]*y[r] for r in y),F())==1
    assert Q*G>=1 and G<=3*harm(U) and Q<=harm(U)**3
    stats['totient_diagonalization_and_bounds']+=1
    for X in (U,2*U,3*U,5*U):
        exact=sum(nu(a,U)**2 for a in range(U+1,X+1))
        count=sum(mu[d]*mu[e]*(X//lcm(d,e)) for d in range(1,U+1) for e in range(1,U+1))-1
        assert exact==count and abs(F(exact+1)-X*Q)<=U**2
        zh=sum((F(nu(a,U)**2,a) for a in range(U+1,X+1)),F())
        rhs=sum((F(mu[d]*mu[e],lcm(d,e))*harm(X//lcm(d,e)) for d in range(1,U+1) for e in range(1,U+1)),F())-1
        assert zh==rhs and zh<=harm(X)*harm(U)**3
        stats['floor_and_harmonic_LCM']+=1

# Algebraic matrix controls use rational matrices, NOT numerical CCM matrices.
def zero():return ((F(0),F(0)),(F(0),F(0)))
def plus(A,B):return tuple(tuple(A[i][j]+B[i][j] for j in range(2)) for i in range(2))
def times(s,A):return tuple(tuple(s*x for x in row) for row in A)
def prod(A,B):return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def total(xs):
    o=zero()
    for x in xs:o=plus(o,x)
    return o

def psd(A):return A[0][1]==A[1][0] and A[0][0]>=0 and A[1][1]>=0 and A[0][0]*A[1][1]>=A[0][1]**2
for z in range(1,17):
    mats=[((F(j+z,3),F((-1)**j,2)),(F((-1)**j,2),F(2*j-z,5))) for j in range(1,5)]
    alpha=[F((-1)**(z+j)*(j+1),j+2) for j in range(4)]
    tau=[F(j+z+1,j+2) for j in range(4)]
    T=total(times(a,A) for a,A in zip(alpha,mats))
    Z=sum(a*a/t for a,t in zip(alpha,tau))
    G=total(times(t,prod(A,A)) for t,A in zip(tau,mats))
    gap=plus(times(Z,G),times(-1,prod(T,T)))
    squares=[]
    for i in range(4):
        for j in range(i+1,4):
            R=plus(times(alpha[i]/tau[i],mats[j]),times(-alpha[j]/tau[j],mats[i]))
            squares.append(times(tau[i]*tau[j],prod(R,R)))
    assert gap==total(squares) and psd(gap)
    expansion=total(times(alpha[i]*alpha[j],prod(mats[i],mats[j])) for i in range(4) for j in range(4))
    assert expansion==prod(T,T)
    stats['full_noncommutative_weighted_square']+=1
    B=[F(j+z+2,j+1) for j in range(4)]
    opttau=[abs(a)/b for a,b in zip(alpha,B)]
    cost=sum(abs(a)*b for a,b in zip(alpha,B))
    assert sum(a*a/t for a,t in zip(alpha,opttau))*sum(t*b*b for t,b in zip(opttau,B))==cost**2
    assert sum(a*a/t for a,t in zip(alpha,tau))*sum(t*b*b for t,b in zip(tau,B))>=cost**2
    stats['optimal_row_weight_certificate']+=1

# Exact prime-composite cancellation and all higher powers.
primes=[p for p in range(2,N+1) if fac[p]==Counter({p:1})]
for U in range(1,6):
  V=U
  for p in primes:
    if p<=U:continue
    for q in primes:
      if q<=V or p*q>N:continue
      n=p*q;co=Counter()
      for a in range(U+1,n+1):
        if n%a==0 and n//a>V:add(co,lam[n//a],nu(a,U))
      expected=Counter()
      if p==q:expected[p]=-1
      else:expected[p]-=1;expected[q]-=1
      assert clean(co)==clean(expected)
      totalcoef=Counter();add(totalcoef,fac[n]);add(totalcoef,co)
      assert clean(totalcoef)==clean(lam[n])
      stats['actual_rough_semiprime_and_square']+=1
  for p in primes:
    if p<=U:continue
    n=p*p;k=2
    while n<=N:
      co=Counter()
      for a in range(U+1,n+1):
        if n%a==0 and n//a>V:add(co,lam[n//a],nu(a,U))
      assert clean(co)=={p:-(k-1)}
      stats['proper_power_multiplicity']+=1
      n*=p;k+=1

# Planted errors must be rejected. No positive/negative actual CCM assertion.
I=((F(1),F(0)),(F(0),F(1)))
assert not psd(plus(times(2,I),times(-4,I)))
stats['planted_missing_mixed_row']=1
P=((F(1),F(0)),(F(0),F(0))); A=((F(0),F(1)),(F(1),F(0)))
assert prod(prod(P,prod(A,A)),P)!=prod(prod(prod(P,A),P),prod(A,P))
stats['planted_missing_intermediate_projection']=1
assert sig(6,2)==0 and sig(6,2)**2!=sum(mu[d]**2 for d in (1,2))
stats['planted_discarded_Mobius_cross']=1
assert lcm(2,2)!=2*2
stats['planted_wrong_LCM']=1
# m=20,U=V=2 contains (a,b)=(3,3), not (a,b)=(3,9).
assert 3*3<=20 and not 3*9<=20 and nu(3,2)*lam[9][3]!=0
stats['planted_rectangular_cutoff']=1
assert nu(6,3)==1 and nu(9,2)==-1 and nu(4,2)==0
stats['planted_missing_threshold_and_power']=1

out={"status":"PASS_EXACT_LOCAL_CONTROLS_NOT_CCM_SIGN", "counts":dict(stats),
     "total_checks":sum(stats.values()),"source_spectrum_computed":False,
     "arb_runs":0,"lean_runs":0,
     "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     "registration_sha256":hashlib.sha256((ROOT/'registration.json').read_bytes()).hexdigest()}
(ROOT/'exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
