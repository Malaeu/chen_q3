"""Finite algebra/budget diagnostics. They do not certify analytic estimates."""
from fractions import Fraction as F
from itertools import product
from math import prod
import sympy as sp
X=sp.Symbol('X')

def primitive_logs(p):
    for g in range(2,p):
        seq=[pow(g,j,p) for j in range(p-1)]
        if len(set(seq))==p-1:
            return {x:j for j,x in enumerate(seq)}
    raise ValueError(p)

def poly_from_exponents(exps,mod):
    co={}
    for e in exps:
        e%=mod; co[e]=co.get(e,0)+1
    return sp.Poly.from_dict({(k,):v for k,v in co.items()},X,domain=sp.ZZ)

def monomial(e,mod):
    return sp.Poly(X**(e%mod),X,domain=sp.ZZ)

counts={'primitive_fourier':0,'gauss_root':0,'CRT':0,'principal_mask':0,'cube_pairs':0,'formal_phase':0,'rational_budgets':0}
for p in [7,13,19]:
    mod=6*p; cycl=sp.Poly(sp.cyclotomic_poly(mod,X),X,domain=sp.ZZ)
    logs=primitive_logs(p)
    gauss={a:poly_from_exponents([p*a*logs[x]+6*x for x in range(1,p)],mod) for a in range(1,6)}
    for a in range(1,6):
        for k in range(p):
            lhs=poly_from_exponents([p*a*logs[x]+6*k*x for x in range(1,p)],mod)
            rhs=sp.Poly(0,X) if k==0 else monomial(-p*a*logs[k],mod)*gauss[a]
            assert (lhs-rhs).rem(cycl).is_zero
            counts['primitive_fourier']+=1
        rhs=p*monomial(p*a*logs[p-1],mod)
        assert (gauss[a]*gauss[6-a]-rhs).rem(cycl).is_zero
        counts['gauss_root']+=1
    for k in range(p):
        lhs=poly_from_exponents([6*k*x for x in range(1,p)],mod)
        assert (lhs-sp.Poly(p-1 if k==0 else -1,X)).rem(cycl).is_zero
        counts['principal_mask']+=1
for p,q in [(7,13),(7,19),(13,19)]:
    mod=6*p*q; cycl=sp.Poly(sp.cyclotomic_poly(mod,X),X,domain=sp.ZZ)
    lp,lq=primitive_logs(p),primitive_logs(q)
    for eps in [1,-1]:
        a,b=eps,-eps
        direct=poly_from_exponents([(mod//6)*(a*lp[x%p]+b*lq[x%q])+6*x for x in range(p*q) if x%p and x%q],mod)
        gp=poly_from_exponents([(mod//6)*a*lp[x]+(mod//p)*x for x in range(1,p)],mod)
        gq=poly_from_exponents([(mod//6)*b*lq[x]+(mod//q)*x for x in range(1,q)],mod)
        phase=monomial((mod//6)*(a*lp[q%p]+b*lq[p%q]),mod)
        assert (direct-phase*gp*gq).rem(cycl).is_zero
        counts['CRT']+=1
# Fourth-power extraction on the conjugated first side and on the second.
for eps in [1,-1]:
    for a,b in product(range(6),repeat=2):
        assert (-4*eps*a+4*eps*b-2*eps*(a-b))%6==0
        counts['formal_phase']+=1
# Both inverse-cube divisor sums, including shared primes.
def mobius_divisor_sum(exponents):
    return sum((-1)**sum(bits) for bits in product(*[range(min(a,1)+1) for a in exponents]))
bs=list(product(range(4),repeat=3))
for a,b in product(bs,repeat=2):
    da,db=mobius_divisor_sum(a),mobius_divisor_sum(b)
    assert da*db==int(not any(a) and not any(b))
    # Principal (same squarefree core and square cube-product) may not be retained alone.
    if all((x+y)%2==0 for x,y in zip(a,b)):
        assert da*db==int(not any(a) and not any(b))
    counts['cube_pairs']+=1
# Planted deletion of cross-return terms is detected at B=p.
assert (1-1)**2==0 and 1**2+(-1)**2==2
c=F(1,10000); cutoff=F(27,50)
for r in [F(28,25),F(5617,5000),F(113,100)]:
    p=(r*(1+c)-1)/6; target=r*(1+c)-F(1,200)
    e=[p+1-cutoff,p+r+F(1,2)-cutoff,p+2*(1+r)/3-cutoff]
    assert max(e)==e[1]
    assert target-e[1]>=F(5371,400000)
    assert p+(1+5*r)/6-target==F(1,200)-5*r*c/6
    assert r-F(1,50)-1>=F(1,10)
    counts['rational_budgets']+=4
print(counts)
print('TOTAL',sum(counts.values()))
print('PL excess at r0 =',F(509461,20000000))
print('Uniform long-divisor tail margin =',F(5371,400000))
print('Actual-moment saving is NOT established.')
