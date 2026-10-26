#!/usr/bin/env python3
"""Exact finite Q35 controls; not a CCM spectral or asymptotic sign proof.

Standard-library rational enclosures certify only the displayed finite
coefficient-law counterexamples. No hypothetical zeta zero is assigned.
"""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, isqrt, lcm
from pathlib import Path
import json

counts = Counter()
rejected = []
def check(label, condition):
    if not condition:
        raise AssertionError(label)
    counts[label] += 1

def reject(label, false_claim):
    if false_claim:
        raise AssertionError('Planted claim survived: ' + label)
    rejected.append(label)

@lru_cache(None)
def factor(n):
    if n < 1:
        raise ValueError('positive integer required')
    out = []
    d = 2
    while d*d <= n:
        k = 0
        while n % d == 0:
            n //= d
            k += 1
        if k:
            out.append((d, k))
        d += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)

def mu(n):
    ff = factor(n)
    return 0 if any(k > 1 for _, k in ff) else (-1)**len(ff)

def phi(n):
    ans = n
    for p, _ in factor(n):
        ans = ans//p*(p-1)
    return ans

def divisors(n):
    return [d for d in range(1,n+1) if n % d == 0]

def ram(q,n):
    return sum(d*mu(q//d) for d in divisors(gcd(q,n)))

@lru_cache(None)
def coeff(z):
    cz = sum((Q(mu(q)**2,phi(q)) for q in range(1,z+1)),Q(0))
    u = {}
    for d in range(1,z+1):
        inner = sum((Q(mu(k)**2,phi(k)) for k in range(1,z//d+1)
                     if gcd(k,d)==1),Q(0))
        u[d] = Q(mu(d)*d,phi(d))*inner/cz
    g = {}
    for d,ud in u.items():
        for e,ue in u.items():
            ll = lcm(d,e)
            g[ll] = g.get(ll,Q(0))+ud*ue
    return cz,u,g

def az(z,n):
    cz,_,_ = coeff(z)
    return (sum((Q(mu(q)*ram(q,n),phi(q))
                 for q in range(1,z+1)),Q(0))/cz)**2

for z in (2,3,5,8):
    cz,u,g=coeff(z)
    for n in (1,2,6,15,30,77,143):
        check('all_mixed_lcm_channels',az(z,n)==
              sum((gl for ll,gl in g.items() if n%ll==0),Q(0)))
    for n in (11*13,11*13*17):
        check('actual_rough_coefficient_equals_one',az(z,n)==1)
    check('model_mean',sum((gl/ll for ll,gl in g.items()),Q(0))==1/cz)

# Covariance of the full conditional polynomial at all variables equal one.
# u*x+v*y+w*x*y+sum d_r*z_r; every r-state is distinct but excludes p and q.
for k in range(1,17):
    u,v,w = Q(k+1,3),Q(k+2,5),Q(k+3,7)
    ds = [Q(k+1,11),Q(k+4,13),Q(k+7,17)]
    d=sum(ds,Q(0)); G=u+v+w+d
    ep=(u+w)/G; eq=(v+w)/G; epq=w/G
    cov=epq-ep*eq
    check('full_conditional_covariance',cov==(w*d-u*v)/(G*G))
    # Rayleigh determinant, including all mixed x*y terms, is independent of x,y.
    x,y=Q(k+2,9),Q(k+4,10)
    val=u*x+v*y+w*x*y+d
    det=(u+w*y)*(v+w*x)-w*val
    check('rayleigh_cancellation_before_moduli',det==u*v-w*d)

# Logarithm and square-root interval primitives, all arithmetic rational.
# No float logarithm or desired-sign rounding is used.
BITS=64
SCALE=1<<BITS
TERMS=32

def log_unit_interval(x):
    if not (Q(1)<=x<=Q(2)):
        raise ValueError('range-reduced input required')
    z=(x-1)/(x+1)
    zz=z*z; term=z; ans=Q(0)
    for k in range(TERMS):
        ans += 2*term/(2*k+1)
        term *= zz
    tail=2*term/((2*TERMS+1)*(1-zz))
    return ans,ans+tail

LOG2=log_unit_interval(Q(2))

@lru_cache(None)
def log_interval(n):
    if n<1:
        raise ValueError('positive input required')
    e=n.bit_length()-1
    lo,hi=log_unit_interval(Q(n,1<<e))
    return e*LOG2[0]+lo,e*LOG2[1]+hi

def sqrt_interval(n):
    k=isqrt(n*SCALE*SCALE)
    lo=Q(k,SCALE)
    if k*k==n*SCALE*SCALE:
        return lo,lo
    return lo,Q(k+1,SCALE)

def down(x):
    return Q((x.numerator*SCALE)//x.denominator,SCALE)

def up(x):
    return Q(-((-x.numerator*SCALE)//x.denominator),SCALE)

@lru_cache(None)
def weight_interval(n):
    ll,lh=log_interval(n); sl,sh=sqrt_interval(n)
    return down(ll/sh),up(lh/sl)

def sieve(n):
    ok=bytearray(b'\1')*(n+1)
    ok[:2]=b'\0\0'
    for p in range(2,isqrt(n)+1):
        if ok[p]:
            ok[p*p:n+1:p]=b'\0'*(((n-p*p)//p)+1)
    return [p for p in range(2,n+1) if ok[p]]

finite=[]
for m,z,a,p,q in ((20000,2,3,23,43),(50000,3,5,29,53),(100000,5,7,31,61)):
    primes=sieve(m//(2*a))
    rs=[r for r in primes if a*r*r>16*m and 2*a*r<=m]
    check('true_prime_anchor_and_pair',all(factor(n)==((n,1),) for n in (a,p,q)))
    check('root_selection_intervals',
          a>z and 16*a*p*p>m and 9*a*p*p<=m and
          4*a*q*q>m and 9*a*q*q<=4*m)
    check('nonempty_actual_large_prime_set',bool(rs))
    check('interior_edges',max(a*p,a*q,a*p*q,max(a*r for r in rs))<m)
    check('all_forbidden_mixed_products_retained_as_zero',
          all(a*p*r>m and a*q*r>m for r in rs) and a*min(rs)**2>m)
    expected={a*p,a*q,a*p*q}|{a*r for r in rs}
    allowed={a,p,q}|set(rs)
    # Exhaust the actual integer source in this finite diagnostic, not 2^|allowed| subsets.
    observed=set()
    for n in range(a,m+1,a):
        ff=factor(n)
        ps={r for r,_ in ff}
        if len(ff)>=2 and mu(n)**2==1 and n>z and ps<=allowed:
            observed.add(n)
    check('complete_conditioned_integer_support',observed==expected)
    check('all_conditioned_model_coefficients',all(az(z,n)==1 for n in expected))
    ul,uh=weight_interval(a*p);vl,vh=weight_interval(a*q)
    wl,wh=weight_interval(a*p*q)
    dints=[weight_interval(a*r) for r in rs]
    dl=sum((v[0] for v in dints),Q(0));dh=sum((v[1] for v in dints),Q(0))
    gl=ul+vl+wl+dl;gh=uh+vh+wh+dh
    det_upper=uh*vh-wl*dl
    cov_lower=(wl*dl-uh*vh)/(gh*gh)
    cov_upper=(wh*dh-ul*vl)/(gl*gl)
    check('certified_actual_negative_Rayleigh_determinant',det_upper<0)
    check('certified_actual_positive_conditional_covariance',0<cov_lower<=cov_upper)
    check('finite_bounds_are_not_missing_normalization',gl>0 and gh>=gl)
    finite.append({'m':m,'Z':z,'anchor':a,'p':p,'q':q,'large_prime_count':len(rs),
                   'support_count':len(expected),'Delta_upper':str(det_upper),
                   'covariance_lower':str(cov_lower),'covariance_upper':str(cov_upper),
                   'scope':'actual finite coefficient law at auxiliary parameters, NOT a production-epsilon spectral cell'})

# Exact causal multiplicative-semigroup coefficient map (formal log labels).
def conv(a,b,m):
    ans={}
    for n,x in a.items():
        for k,y in b.items():
            if n*k<m:
                ans[n*k]=ans.get(n*k,Q(0))+x*y
    return {n:x for n,x in ans.items() if x}

for m in (30,31,105,106):
    x={2:Q(1),3:Q(2)};y={5:Q(3),7:Q(-1)};z={2:Q(2),11:Q(1)}
    check('uncompressed_forward_associativity',conv(conv(x,y,m),z,m)==conv(x,conv(y,z,m),m))
    check('endpoint_is_zero_in_causal_evaluation',conv({1:Q(1)},{m:Q(1)},m)=={})

# Rational complex Hermitian quadratic form: off-diagonal imaginary terms matter.
def cmul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cadd(a,b):return (a[0]+b[0],a[1]+b[1])
def conj(a):return (a[0],-a[1])
def qform(mat,c):
    ans=(Q(0),Q(0))
    for i in range(len(c)):
        for j in range(len(c)):
            ans=cadd(ans,cmul(cmul(conj(c[i]),mat[i][j]),c[j]))
    return ans
I=(Q(0),Q(1));O=(Q(0),Q(0));ONE=(Q(1),Q(0))
mat=[[ONE,I],[conj(I),(Q(2),Q(0))]]
c=[ONE,I]
full=qform(mat,c);diag=qform([[ONE,O],[O,(Q(2),Q(0))]],c)
check('complex_mixed_form_real',full[1]==0)

# Exact power bookkeeping: each fixed epsilon leaves the old half-power debt.
for eps in (Q(1,64),Q(1,128),Q(1,256)):
    kap=eps/4
    check('source_hierarchy',0<kap<Q(1,128) and 3*kap<1)
    check('auxiliary_fees_below_half',5*eps/4< Q(1,2) and 3*eps/2<Q(1,2))
    check('conditional_block_price_not_vanishing_family',Q(1,2)-kap>Q(49,100))

# Planted failures: none is promoted to a counterexample for actual CCM.
cz,u,g=coeff(3)
reject('erase_mixed_divisor_channels',sum((ud*ud/d for d,ud in u.items()),Q(0))==1/cz)
reject('all_weights_are_rough_one',az(3,6)==1)
reject('squarefree_mask_includes_prime_square',mu(9)**2==1)
U,V,W,D=Q(2),Q(3),Q(5),Q(7);GG=U+V+W+D
correct=(W*D-U*V)/(GG*GG)
reject('reverse_covariance_sign',correct==(U*V-W*D)/(GG*GG))
reject('omit_joint_pq_from_normalizer',correct==(W*D-U*V)/(U+V+D)**2)
reject('rectangularize_hyperbolic_support',3*23*331<=20000)
reject('drop_complex_cross_terms',full==diag)
reject('remove_probability_mass_in_physical_return',Q(7)*Q(2,3)==Q(2,3))
# Full product derivative vs logarithmic derivative, in the exact squarefree
# algebra x^2=y^2=0. Logs of two distinct primes are independent formal labels.
def sfmul(f,g):
    out={}
    for a,x in f.items():
        for b,y in g.items():
            if a & b:
                continue
            out[a|b]=out.get(a|b,Q(0))+x*y
    return {k:v for k,v in out.items() if v}
product_poly={0:Q(1),1:Q(1),2:Q(1),3:Q(1)}
inverse_poly={0:Q(1),1:Q(-1),2:Q(-1),3:Q(1)}
# Coefficient of log(p) in minus sigma derivative: x+xy.
derivative_p={1:Q(1),3:Q(1)}
log_derivative_p=sfmul(inverse_poly,derivative_p)
check('literal_product_vs_log_derivative',log_derivative_p=={1:Q(1)})
reject('product_derivative_equals_logarithmic_derivative_on_distinct_product',
       derivative_p==log_derivative_p)

out={'status':'FINITE_ALGEBRA_AND_RATIONAL_ENCLOSURES_COMPLETED',
     'counts':dict(counts),'total_controls':sum(counts.values()),
     'planted_errors_detected':rejected,'planted_count':len(rejected),
     'finite_actual_law_controls':finite,
     'precision':'integer arithmetic and rational outward enclosures; not Arb',
     'scope':'No finite check proves the asymptotic CCM sign. Cofinal law obstruction is the PAPER proof.',
     'independent_audit':False,'lean':False,'arb':False,'production_spectrum':False}
Path('q35_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'total_controls':out['total_controls'],'planted_count':len(rejected),
                  'finite_support_sizes':[r['support_count'] for r in finite]},indent=2))
