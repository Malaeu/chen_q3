"""Q03 finite algebra/budget diagnostics; no analytic moment certification."""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
from collections import Counter
from math import prod

checks = Counter()
PS = (7, 13)
ZERO, ONE, ZETA = (F(0), F(0)), (F(1), F(0)), (F(0), F(1))
def add(x, y): return (x[0] + y[0], x[1] + y[1])
def neg(x): return (-x[0], -x[1])
def scale(x, c): return (x[0] * c, x[1] * c)
def mul(x, y):
    return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]+x[1]*y[1])
def cpow(x, k):
    ans = ONE
    for _ in range(k): ans = mul(ans, x)
    return ans

def conj(x): return (x[0]+x[1], -x[1])
def norm2(x):
    ans = mul(x, conj(x))
    assert ans[1] == 0
    return ans[0]

def csum(xs):
    ans = ZERO
    for x in xs: ans = add(ans, x)
    return ans

def mu_e(e): return 1 if e == 0 else -1 if e == 1 else 0
def mu2_e(e): return 1 if e in (0, 2) else -2 if e == 1 else 0
def norm(es): return prod(p**e for p,e in zip(PS,es))
def mu(es): return prod(mu_e(e) for e in es)

@lru_cache(None)
def A(cutoff, es):
    return sum(prod(mu2_e(d) for d in ds)
               for ds in product(*(range(e+1) for e in es))
               if norm(ds) <= cutoff)

def j(cutoff, es): return mu(es) - A(cutoff, es)

def W(x): return (2*x-1)*(2-x) if F(1,2) <= x <= 2 else F(0)

# Coefficient recurrence, including cutoff equalities and every k>=2 branch.
for i, cutoff, k, e in product(range(2), map(F,(1,6,7,13,49,91,169,300)), range(6), range(6)):
    es = [0,0]; es[i]=k; es[1-i]=e; es=tuple(es)
    ms = list(es); ms[i]=0; ms=tuple(ms); q=PS[i]
    rhs = (mu_e(k)*mu(ms) - A(cutoff,ms)
           + 2*int(k>=1)*A(cutoff/q,ms)
           - int(k>=2)*A(cutoff/(q*q),ms))
    assert j(cutoff,es) == rhs
    checks['long_coefficient_prime_power_recurrence'] += 1

for es, (b,c) in product(product(range(6),repeat=2), ((F(6),F(20)),(F(20),F(100)))):
    assert j(b,es) == A(c,es)-A(b,es)+j(c,es)
    checks['exact_new_long_slab'] += 1

# Full normalized identity multiplied by sqrt(L), so all arithmetic is exact.
PHASES = [ZERO] + [cpow(ZETA,k) for k in range(6)]
IDEALS = [(es, norm(es)) for es in product(range(5),repeat=2) if norm(es)<=500]

def phase(es, values): return mul(cpow(values[0],es[0]),cpow(values[1],es[1]))

def poly(kind, cutoff, mask, L, values):
    if L <= 0: raise ValueError('Scale must be positive')
    terms=[]
    for es,n in IDEALS:
        if any(e and blocked for e,blocked in zip(es,mask)): continue
        w=W(F(n)/L)
        if not w: continue
        coefficient = mu(es) if kind=='M' else A(cutoff,es) if kind=='K' else j(cutoff,es)
        terms.append(scale(phase(es,values),coefficient*w))
    return csum(terms)

for values, cutoff, L, i, blocked_other in product(
        product(PHASES,repeat=2), map(F,(6,20,100)), map(F,(10,50,250)), range(2), (0,1)):
    q=PS[i]; mask=[0,0]; mask[1-i]=blocked_other; mask=tuple(mask)
    newmask=list(mask);newmask[i]=1;newmask=tuple(newmask)
    lhs=add(poly('J',cutoff,newmask,L,values),neg(poly('J',cutoff,mask,L,values)))
    N=L/q
    bracket=add(poly('M',cutoff,newmask,N,values),
                add(poly('K',cutoff,newmask,N,values),scale(poly('K',cutoff/q,newmask,N,values),-2)))
    rhs=mul(values[i],bracket)
    k=2
    while q**k <= 2*L:
        N=L/(q**k)
        bracket=add(poly('K',cutoff,newmask,N,values),
                    add(scale(poly('K',cutoff/q,newmask,N,values),-2),
                        poly('K',cutoff/(q*q),newmask,N,values)))
        rhs=add(rhs,mul(cpow(values[i],k),bracket));k+=1
    assert lhs==rhs
    checks['all_power_long_mask_increment_with_zero_branches'] += 1

# Deliberately false Mobius-only increment fails on an actual square coefficient.
assert j(F(6),(1,0)) == -2 and j(F(6),(2,0)) == -1
assert mu((2,0)) == 0 and j(F(6),(2,0)) != mu((2,0))
checks['planted_mobius_only_square_defect_detected'] += 1

# Exact amplifier compression, preserving prime squares and distinct-prime pairs.
primes=(7,13,19)
for y,pmax in ((6,200),(10,500),(15,1000),(21,5000)):
    assert pmax < y**3
    original=[]; weights=Counter()
    for es in product(range(6),repeat=3):
        n=prod(p**e for p,e in zip(primes,es))
        if n>pmax: continue
        small=tuple(e if p<=y else 0 for p,e in zip(primes,es))
        rough=tuple(e if p>y else 0 for p,e in zip(primes,es))
        assert sum(rough)<=2
        assert tuple(a+b for a,b in zip(small,rough))==es
        original.append(es);weights[small]+=1
        checks['amplifier_factorization_all_powers'] += 1
    assert sum(weights.values())==len(original)
    for small,multiplicity in weights.items():
        qb=prod(p**e for p,e in zip(primes,small))
        direct=0
        for es in product(range(3),repeat=3):
            if any(e and p<=y for p,e in zip(primes,es)): continue
            if qb*prod(p**e for p,e in zip(primes,es))<=pmax: direct+=1
        assert multiplicity==direct
        checks['rough_multiplicity_exact_not_density'] += 1

# A high-value selector does not automatically preserve the full unit projector.
vals=[add(cpow(ZETA,k),cpow(ZETA,2*k)) for k in range(6)]
assert [norm2(x) for x in vals]==list(map(F,(4,3,1,0,1,3)))
full=csum(cpow(ZETA,(-k)%6) for k in range(6))
selected=csum(cpow(ZETA,(-k)%6) for k,x in enumerate(vals) if norm2(x)>2)
assert full==ZERO and selected==scale(ONE,2)
checks['selected_unit_projector_planted_defect_detected']+=1

# Entire parameter polytope: affine extrema occur at these four vertices.
c0,eta,c,y,b=F(1,10000),F(1,200),F(3,32),F(1,100),F(1,32)
mins={}
for r in (F(28,25),F(113,100)):
    h=r*(1+c0);p=(h-1)/6
    for ell in (r-y,r):
        margins={
            'new_slab_gain':5*p-c,
            'new_slab_margin':5*p-c-eta,
            'rough_short_gain':5*p-c+y,
            'rough_inverse_gain':h-p-F(1,6)-F(5,6)*ell+F(11,6)*y,
            'P_below_Y_cubed':3*y-p,
            'old_short_gain_new_mapping':5*p-b,
            'clipped_gain':F(3,500),
            'inverse_gain_if_remaining_bound':eta-F(5,6)*r*c0,
        }
        for key,value in margins.items():
            assert value>0
            mins[key]=min(mins.get(key,value),value)
            checks['affine_budget_vertex_inequalities']+=1
assert mins['new_slab_gain']==F(1903,300000)
assert mins['new_slab_margin']==F(403,300000)
assert mins['rough_short_gain']==F(4903,300000)
assert mins['rough_inverse_gain']==F(691,37500)
checks['named_budget_equalities']+=4

print('EXACT_FINITE_DIAGNOSTICS_ONLY')
for name,count in checks.items():print(name,count)
print('TOTAL',sum(checks.values()))
print('MARGINS',{k:str(v) for k,v in mins.items()})
print('NO_ANALYTIC_CERTIFICATION; NO_LEAN; NO_ARB; NO_COMPARATOR')
