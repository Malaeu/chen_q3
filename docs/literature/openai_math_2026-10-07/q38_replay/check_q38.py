#!/usr/bin/env python3
"""Q38 exact finite algebra controls. No production CCM spectral computation.

The common factor n**(-sigma) is symbolic and multiplicative. Prime logarithms
are independent formal variables. The PAPER proof, not this finite panel,
establishes the uniform norm and cofinal certificate-price estimates.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from math import comb, gcd, isqrt, lcm
from pathlib import Path
import json

checks = Counter()
planted = []
def check(name, condition):
    if not condition:
        raise AssertionError(name)
    checks[name] += 1

def reject(name, false_claim):
    if false_claim:
        raise AssertionError('Planted error survived: ' + name)
    planted.append(name)

@lru_cache(None)
def factors(n):
    out = []
    p = 2
    while p*p <= n:
        a = 0
        while n % p == 0:
            a += 1
            n //= p
        if a:
            out.append((p, a))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)

@lru_cache(None)
def divisors(n):
    out = [1]
    for p, a in factors(n):
        out = [d*p**j for d in out for j in range(a+1)]
    return tuple(sorted(out))

def mu(n):
    fs = factors(n)
    return 0 if any(a > 1 for p, a in fs) else (-1)**len(fs)

def phi(n):
    for p, a in factors(n):
        n = n//p*(p-1)
    return n

def prime(n):
    return len(factors(n)) == 1 and factors(n)[0][1] == 1

def ram(q, n):
    return sum(d*mu(q//d) for d in divisors(gcd(q, n)))

def model(Z):
    CZ = sum((F(mu(q)**2, phi(q)) for q in range(1, Z+1)), F(0))
    u = {}
    for d in range(1, Z+1):
        inner = sum((F(mu(k)**2, phi(k)) for k in range(1, Z//d+1)
                     if gcd(k, d) == 1), F(0))
        u[d] = F(mu(d)*d, phi(d))*inner/CZ
    g = defaultdict(F)
    for d, ud in u.items():
        for e, ue in u.items():
            g[lcm(d, e)] += ud*ue
    return CZ, u, {n:v for n,v in g.items() if v}

def conv(a, b, N):
    return {n:sum((a.get(d, 0)*b.get(n//d, 0) for d in divisors(n)), F(0))
            for n in range(1, N+1)}

def lp(n, q=F(1)):
    return {p:F(a)*q for p,a in factors(n) if q}

def ladd(*terms):
    out = defaultdict(F)
    for scale, term in terms:
        for p, x in term.items():
            out[p] += scale*x
    return {p:v for p,v in out.items() if v}

def derivative(a):
    return {n:lp(n,v) for n,v in a.items()}

def conv_log(a, b, N):
    return {n:ladd(*[(b.get(n//d,0), a.get(d,{})) for d in divisors(n)])
            for n in range(1,N+1)}

records = []
cases = {}
for Z,N in ((2,128),(3,420),(5,512),(8,320)):
    CZ,u,g = model(Z)
    a = {n:sum((v for d,v in g.items() if n%d == 0),F(0))
         for n in range(1,N+1)}
    direct = {n:(sum((F(mu(q)*ram(q,n),phi(q)) for q in range(1,Z+1)),F(0))/CZ)**2
              for n in range(1,N+1)}
    check('actual_mixed_Ramanujan_model', a == direct)
    check('squarefree_support_and_constant_term', all(mu(d)**2 == 1 for d in g) and a[1] == 1)
    ep = {n:mu(n)**2*a[n] for n in a}
    em = {n:mu(n)*a[n] for n in a}
    K = conv(ep,em,N)
    expanded = defaultdict(F)
    for ell,gl in g.items():
        for k,gk in g.items():
            h = gcd(ell,k)
            for ra in divisors(ell//h):
                for rb in divisors(k//h):
                    base = ell*k*ra*rb
                    for d in range(1,isqrt(N//base)+1):
                        if gcd(d,ell*k) == 1:
                            expanded[base*d*d] += gl*gk*mu(k)*mu(ra)*mu(d)
    check('complete_mixed_channel_product', K == {n:expanded[n] for n in K})
    dp,dm = derivative(ep), derivative(em)
    left, right = conv_log(dp,em,N), conv_log(dm,ep,N)
    Q = {n:ladd((1,left[n]),(1,right[n])) for n in K}
    check('whole_differentiated_product', Q == derivative(K))
    ep0,em0 = dict(ep),dict(em)
    ep0[1] = em0[1] = 0
    left0, right0 = conv_log(dp,em0,N), conv_log(dm,ep0,N)
    mixed = {n:ladd((1,left0[n]),(1,right0[n])) for n in K}
    check('exact_cross_return', all(ladd((1,dp[n]),(1,dm[n]),(1,mixed[n])) == Q[n] for n in K))
    odd = {n:lp(n,a[n]) if mu(n)**2 and len(factors(n)) >= 3 and len(factors(n))%2 else {}
           for n in K}
    small = {n:lp(n,a[n]) if 1<n<=Z and mu(n)**2 and not prime(n) else {} for n in K}
    R = {n:ladd((F(-1,2),mixed[n]),(1,odd[n]),(-1,small[n])) for n in K}
    target = {n:lp(n,a[n]) if Z<n and mu(n)**2 and not prime(n) else {} for n in K}
    check('full_signed_composite_reconstruction', all(ladd((F(1,2),Q[n]),(1,R[n])) == target[n] for n in K))
    odd_large = [n for n in K if any(p>Z and j%2 for p,j in factors(n))]
    check('odd_large_prime_exponent_cancels', all(K[n] == 0 and Q[n] == {} for n in odd_large))
    rough_sf = [n for n in K if n>1 and mu(n)**2 and min(p for p,j in factors(n))>Z]
    check('rough_squarefree_partner_restores_all_composites',
          all(R[n] == ({} if prime(n) else lp(n)) for n in rough_sf))
    # Exact original A + C_sf = U_sf at every coefficient, including proper powers.
    prime_total = {n:({factors(n)[0][0]:F(1)} if len(factors(n))==1 else {}) for n in K}
    U = {}
    for n in K:
        low_D = dp[n] if n<=Z else {}
        low_P = lp(n) if prime(n) and n<=Z else {}
        pp = {factors(n)[0][0]:F(1)} if len(factors(n))==1 and factors(n)[0][1]>=2 else {}
        U[n] = ladd((1,dp[n]),(-1,low_D),(1,low_P),(1,pp))
    check('original_A_return_with_all_prime_powers',
          all(ladd((1,prime_total[n]),(1,target[n])) == U[n] for n in K))
    cases[Z] = {'N':N, 'a':a, 'K':K, 'Q':Q, 'R':R, 'mixed':mixed, 'target':target}
    records.append({'Z':Z,'N':N,'verified_coefficients':N,'rough_squarefree_count':len(rough_sf),
                    'rough_composite_count':sum(not prime(n) for n in rough_sf),
                    'rough_odd_composite_count':sum(len(factors(n))>=3 and len(factors(n))%2==1 for n in rough_sf),
                    'odd_large_exponent_count':len(odd_large)})

# One exact full model: a_Z is NOT a freely multiplicative rough mask.
CZ,u,g = model(3)
def az(n):
    return sum((v for d,v in g.items() if n%d==0),F(0))
check('actual_model_is_not_multiplicative', az(6) != az(2)*az(3))
check('actual_nonrough_atoms_are_retained', az(2) == F(1,25) and az(6) == F(4,25))

# Whole causal product differs from a Gram/adjoint product, exact finite algebra.
# T is a 2-state nilpotent shift. This only guards the map, not an actual-P no-go.
one=((F(1),F(0)),(F(0),F(1)))
plus=((F(1),F(0)),(F(1),F(1)))
minus=((F(1),F(0)),(F(-1),F(1)))
def mm(A,B):
    return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def tr(A): return tuple(zip(*A))
check('causal_pair_not_adjoint_pair', mm(plus,minus)==one and mm(plus,tr(minus))!=one)

# Classical binomial estimate used only for the lower coefficient-price proof.
check('binomial_lcm_divisibility_and_count_bound',
      all(lcm(*range(1,2*n+1)) % comb(2*n,n) == 0 and (2*n+1)*comb(2*n,n)>=4**n
          for n in range(1,65)))
check('eventual_Chebyshev_threshold_constants', 2*64**2/F(2**32)<F(1,8) and 2**21>16*64)
check('rough_semiprime_price_constant', F(1,256)*F(2,3)==F(1,384))

# Coefficient controls for the genuinely earlier, unsieved rollback.
N=160
sf={n:F(mu(n)**2) for n in range(1,N+1)}
liouville={n:F((-1)**sum(j for p,j in factors(n))) for n in sf}
check('finite_squarefree_inverse_is_Liouville',conv(sf,liouville,N)=={n:F(n==1) for n in sf})
logder=conv_log(derivative(sf),liouville,N)
alt={n:({factors(n)[0][0]:F((-1)**(factors(n)[0][1]+1))} if len(factors(n))==1 else {}) for n in sf}
check('full_logarithmic_derivative_return',logder==alt)

reject('drop_mixed_g_channels', az(6)==sum(u[d]**2 for d in u if 6%d==0))
reject('replace_nonrough_model_by_zero', az(2)==0)
reject('make_model_multiplicative', az(6)==az(2)*az(3))
reject('replace_partner_by_adjoint', mm(plus,tr(minus))==one)
reject('delete_square_term_from_parity_product',conv(sf,{n:F(mu(n)) for n in sf},N)[4]==0)
reject('drop_semiprime_mixed_return', cases[3]['target'][35] == ladd((F(1,2),cases[3]['Q'][35])))
reject('drop_odd_composite_return', cases[3]['target'][385] == ladd((F(1,2),cases[3]['Q'][385]),(F(-1,2),cases[3]['mixed'][385])))
reject('identify_log_derivative_and_full_derivative', derivative(sf)[6]==logder[6])
reject('use_Mobius_as_squarefree_inverse',conv(sf,{n:F(mu(n)) for n in sf},N)[4]==0)
# At a physical top, the operator vanishes; its formal arithmetic coefficient need not.
CZtop,utop,gtop = model(3)
atop = sum((v for d,v in gtop.items() if 35%d==0),F(0))
formal_top = lp(35, atop)
physical_top_overlap = F(0)
check('top_support_is_distinct_from_arithmetic_coefficient', formal_top != {} and physical_top_overlap == 0)
reject('make_top_arithmetic_coefficient_zero', formal_top == {})

out={'status':'FINITE_EXACT_ALGEBRA_CONTROLS_ONLY','groups':dict(checks),
     'total_groups':sum(checks.values()),'parameter_cases':records,
     'planted_errors_detected':planted,'planted_count':len(planted),
     'scope':'Formal prime-log coefficients and exact rational arithmetic. Not a numerical original-P cell or an asymptotic signed-form certification.',
     'independent_audit':False,'lean':False,'arb':False,'production_spectrum':False}
Path('q38_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'total_groups':out['total_groups'],'planted_count':len(planted)},indent=2))
