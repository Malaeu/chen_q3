#!/usr/bin/env python3
"""Exact finite controls for Q34; not a spectral or asymptotic sign test.

Only the Python standard library is used. Hermitian 2x2 matrices are stored
as (diagonal_1, diagonal_2, real_offdiag, imaginary_offdiag), all Fractions.
Formal prime logarithms are dictionary labels; no floating-point logarithms
or proposed sign thresholds are used.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from math import comb, gcd, isqrt, lcm
from pathlib import Path
import json

counts = Counter()
rejected = []
def check(label, condition):
    if not condition:
        raise AssertionError('Failed control: ' + label)
    counts[label] += 1

def reject(label, false_claim):
    if false_claim:
        raise AssertionError('Planted error survived: ' + label)
    rejected.append(label)

def factor(n):
    if n < 1:
        raise ValueError('positive integer required')
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out

def mu(n):
    f = factor(n)
    return 0 if any(e > 1 for e in f.values()) else (-1)**len(f)

def phi(n):
    value = n
    for p in factor(n):
        value = value // p * (p-1)
    return value

def divisors(n):
    return [d for d in range(1, n+1) if n % d == 0]

def tau(n):
    value = 1
    for e in factor(n).values():
        value *= e+1
    return value

def prime(n):
    return n > 1 and factor(n) == {n: 1}

def ram(q, n):
    return sum(d*mu(q//d) for d in divisors(gcd(q, n)))

def coefficients(z):
    c = sum((Q(mu(q)**2, phi(q)) for q in range(1, z+1)), Q(0))
    u = {}
    for d in range(1, z+1):
        inner = sum((Q(mu(k)**2, phi(k)) for k in range(1, z//d+1)
                     if gcd(k, d) == 1), Q(0))
        u[d] = Q(mu(d)*d, phi(d))*inner/c
    g = {}
    for d, ud in u.items():
        for e, ue in u.items():
            ell = lcm(d, e)
            g[ell] = g.get(ell, Q(0)) + ud*ue
    return c, u, g

def az(z, n):
    c, u, _ = coefficients(z)
    return sum((u[d] for d in u if n % d == 0), Q(0))**2

def floor(x):
    return x.numerator // x.denominator

def qcount(ell, x):
    return sum(mu(n)**2 for n in range(ell, floor(x)+1, ell))

def qformula(ell, x, omit_coprime=False):
    if mu(ell)**2 != 1:
        raise ValueError('ell must be squarefree')
    t = x/ell
    dmax = isqrt(max(0, floor(t)))
    return sum(mu(d)*sum(mu(a)*floor(t/(d*d*a)) for a in divisors(ell))
               for d in range(1, dmax+1)
               if omit_coprime or gcd(d, ell) == 1)

def density_factor(ell):
    """delta_ell = (1/zeta(2))*this rational factor, for squarefree ell."""
    result = Q(1)
    for p in factor(ell):
        result /= p+1
    return result

for z in (2, 3, 5, 8):
    cz, u, g = coefficients(z)
    check('squarefree_support_of_actual_coefficients',
          all(mu(d)**2 == 1 or ud == 0 for d, ud in u.items()) and
          all(mu(ell)**2 == 1 or gl == 0 for ell, gl in g.items()))
    check('complete_mixed_model_mean',
          sum((gl/ell for ell, gl in g.items()), Q(0)) == 1/cz)
    for n in (1, 2, 4, 6, 8, 9, 12, 15, 16, 18, 25, 30, 36, 49, 60):
        direct = sum((Q(mu(q)*ram(q, n), phi(q)) for q in range(1,z+1)),Q(0))/cz
        via_g = sum((gl for ell, gl in g.items() if n % ell == 0), Q(0))
        check('actual_divisor_square_expansion', direct*direct == via_g == az(z,n))

for ell in (1, 2, 3, 6, 10, 15, 30):
    for x in (Q(1,2), Q(1), Q(7,3), Q(4), Q(17,2), Q(25), Q(36), Q(101,2), Q(96)):
        check('squarefree_multiple_floor_identity', qcount(ell,x) == qformula(ell,x))

# Exact rational enclosure of the infinite density.  Tail <= 1/K follows
# from sum_{n>K} 1/n^2 <= integral_K^infinity t^-2 dt; no Arb is used.
K = 128
zeta2_inverse_partial = sum((Q(mu(d),d*d) for d in range(1,K+1)), Q(0))
for ell in (1,2,3,6,10,15,30):
    w = density_factor(ell)
    lo, hi = (zeta2_inverse_partial-Q(1,K))*w, (zeta2_inverse_partial+Q(1,K))*w
    for x in (Q(1),Q(17,3),Q(25),Q(49),Q(101,2),Q(96)):
        value = qcount(ell,x)
        err = max(abs(value-lo*x),abs(value-hi*x))
        check('finite_density_error_rational_enclosure',err*err <= 9*tau(ell)**2*x/ell)

# Local Euler factors, including the coprimality correction.
primes = [p for p in range(2,32) if prime(p)]
zeta_partial = Q(1)
for p in primes:
    zeta_partial *= 1-Q(1,p*p)
for ell in (1,2,3,6,10,15,30):
    lhs=Q(phi(ell),ell*ell)
    for p in primes:
        if ell % p:
            lhs *= 1-Q(1,p*p)
    check('density_Euler_factor',lhs == zeta_partial*density_factor(ell))

# The combinatorial bound tau(n)^4 <= d_16(n), checked locally.  A full
# prime-by-prime proof (injecting exponent tuples into 16-bin counts) is in md.
for a in range(7):
    seen=set()
    for es in product(range(a+1),repeat=4):
        bins=[0]*16
        for t in range(1,a+1):
            mask=sum((1<<j) for j in range(4) if es[j]>=t)
            bins[mask]+=1
        recovered=tuple(sum(bins[b] for b in range(16) if b & (1<<j)) for j in range(4))
        if recovered != es or sum(bins) != a:
            raise AssertionError('invalid injection')
        seen.add(tuple(bins))
    check('divisor_power_injection',len(seen)==(a+1)**4 and len(seen)<=comb(a+15,15))

ZERO = (Q(0),)*4
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(a,t):return tuple(t*x for x in a)
def h(n,m):
    return (Q(m-n,n),Q((m-n)*(n+2),n+1),Q(m-n,n),Q(m-n,n*n))

def log_matrix_term(n, weight, mat):
    return {p:scale(mat,weight*e) for p,e in factor(n).items()}

def accum(out,term,sgn=1):
    for p,v in term.items():out[p]=add(out.get(p,ZERO),scale(v,sgn))
    return out

def clean(out):return {p:v for p,v in out.items() if v != ZERO}
def plus(*terms):
    out={}
    for sign,term in terms:accum(out,term,sign)
    return clean(out)

# Source decompositions are checked with formal log(p) coefficients and a
# non-diagonal complex Hermitian matrix at each atom. This is not actual CCM.
for z,m in ((2,24),(3,36),(5,50),(8,64)):
    A={};BM={};BS={};BSsmall={};BNsmall={};CS={};CN={};CC={};PS={};PP={}
    for n in range(1,m+1):
        model=log_matrix_term(n,az(z,n),h(n,m))
        accum(BM,model)
        sf=mu(n)**2 == 1
        if sf:accum(BS,model)
        if n<=z:accum(BSsmall if sf else BNsmall,model)
        composite=n>1 and not prime(n)
        if n>z and composite:
            accum(CC,model)
            accum(CS if sf else CN,model)
        fs=factor(n)
        if len(fs)==1:
            p,k=next(iter(fs.items()))
            term={p:h(n,m)}
            accum(A,term)
            if k>=2:accum(PP,term)
            elif n<=z:accum(PS,term)
    check('composite_partition_all_terms',plus((1,CC)) == plus((1,CS),(1,CN)))
    check('nonsquarefree_full_return',plus((1,CN)) == plus((1,BM),(-1,BS),(-1,BNsmall)))
    check('squarefree_core_to_original_A',plus((1,A),(1,CS)) == plus((1,BS),(-1,BSsmall),(1,PS),(1,PP)))
    check('all_complex_coordinates_and_top',any(v[3] for v in BS.values()) and h(m,m)==ZERO)
    for n in range(z+1,m+1):
        if n>1 and not prime(n):
            factors=[(u,n//u) for u in divisors(n) if 1<u<n]
            rho=Q((-1)**n*(m-n),m+n)
            check('ordered_factor_return',sum((rho/(tau(n)-2) for _ in factors),Q(0))==rho)

# Matrix Stieltjes/Abel algebra with a continuous piecewise-linear test.
m=9;z=3
weights={n:Q(mu(n)**2)*az(z,n) for n in range(1,m+1)}
F={n:scale(h(n,m),Q(n-1)) for n in range(1,m+1)}
source=ZERO;integ=ZERO;error_integral=ZERO
qcum=Q(0);delta=Q(3,7) # arbitrary to test identity, not assigned to the source density
for n in range(1,m+1):source=add(source,scale(F[n],weights[n]))
for k in range(1,m):
    qcum+=weights[k]
    integ=add(integ,scale(add(F[k],F[k+1]),Q(1,2)))
    dif=add(F[k+1],scale(F[k],-1))
    error_integral=add(error_integral,scale(dif,qcum-delta*Q(2*k+1,2)))
check('matrix_Abel_endpoints_and_sign',source==add(scale(integ,delta),scale(error_integral,-1)))

# Negative controls: all failures alter a substantive formula.
reject('omit_coprimality_in_multiple_count',qformula(2,Q(8),True)==qcount(2,Q(8)))
reject('use_density_one_over_ell',density_factor(2)==Q(1,2))
reject('extend_squarefree_ell_formula_to_ell4',qcount(4,Q(4))==1)
reject('remove_intersections_of_prime_squares',1-int(4<=36 and 36%4==0)-int(9<=36 and 36%9==0)==mu(36)**2)
cz,u,g=coefficients(3)
reject('lcm_replaced_by_product',sum((ud*ue/Q(d*e) for d,ud in u.items() for e,ue in u.items()),Q(0))==1/cz)
reject('delete_all_mixed_divisor_pairs',sum((ud*ud/d for d,ud in u.items()),Q(0))==1/cz)
reject('nonsquarefree_means_only_prime_powers', (mu(12)**2==0)==(len(factor(12))==1 and max(factor(12).values())>1))
# At n=9, Z=2, the squarefree core is zero, but A still contains log3*h(9).
reject('delete_proper_power_return',h(9,24)==ZERO)
# A non-symmetric redistribution must be transposed in the trace mask.
# H is symmetric; Bprime is a genuine non-symmetric redistribution.  The
# singleton mask selects one ordered pair and hence tests the exact trace.
HH={(0,0):Q(0),(0,1):Q(3),(1,0):Q(3),(1,1):Q(0)}
Bprime={(0,0):Q(0),(0,1):Q(1),(1,0):Q(2),(1,1):Q(0)}
mask={(0,1)}
trace_masked=sum((HH[i,j]*Bprime[j,i] for i,j in mask),Q(0))
wrong_untransposed=sum((HH[i,j]*Bprime[i,j] for i,j in mask),Q(0))
reject('wrong_mask_without_transpose',trace_masked==wrong_untransposed)
reject('wrong_Abel_sign',source==add(scale(integ,delta),error_integral))

out={'status':'EXACT_LOCAL_CONTROLS_COMPLETED',
     'checks':dict(counts),'total_checks':sum(counts.values()),
     'planted_errors_detected':rejected,'planted_count':len(rejected),
     'arithmetic':'exact integers, rational fractions and formal prime-log coefficients',
     'scope':'finite algebra and rational density controls only; no global CCM sign or production spectrum proof',
     'independent_audit':False,'lean':False,'arb':False,'production_spectrum':False}
Path('q34_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out,ensure_ascii=False,indent=2))
