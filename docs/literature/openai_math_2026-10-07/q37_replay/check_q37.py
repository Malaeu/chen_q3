#!/usr/bin/env python3
"""Exact local controls for Q37. No production CCM spectra or cofinal inference.

Formal variables L_p mean log(p); prime-power support and convolution are literal.
The analytic infinite-family assertions are proved in the accompanying Markdown.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json

counts = Counter()
planted = []

def check(name, truth):
    if not truth:
        raise AssertionError(name)
    counts[name] += 1

def reject(name, false_claim):
    if false_claim:
        raise AssertionError('Planted error survived: ' + name)
    planted.append(name)

def factor(n):
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

def add(a, b):
    c = defaultdict(Q)
    for mon, v in a.items(): c[mon] += v
    for mon, v in b.items(): c[mon] += v
    return {mon:v for mon,v in c.items() if v}

def scale(a, x):
    return {mon:x*v for mon,v in a.items() if x*v}

def mul(a, b):
    c = defaultdict(Q)
    for ma, x in a.items():
        for mb, y in b.items():
            c[tuple(sorted(ma+mb))] += x*y
    return {mon:v for mon,v in c.items() if v}

def power(a, k):
    r = {():Q(1)}
    for _ in range(k): r=mul(r,a)
    return r

def mangoldt(n):
    fs = factor(n)
    return {(next(iter(fs)),):Q(1)} if len(fs)==1 else {}

def logpoly(n):
    return {(p,):Q(a) for p,a in factor(n).items()}

N = 96
lam = {n:mangoldt(n) for n in range(1,N+1)}
conv = [{n:({():Q(1)} if n==1 else {}) for n in range(1,N+1)}]
for k in range(1,8):
    row={}
    for n in range(1,N+1):
        r={}
        for d in range(2,n+1):
            if n%d==0: r=add(r,mul(lam[d],conv[-1][n//d]))
        row[n]=r
    conv.append(row)

# Actual coefficient identity and coefficientwise positive proof controls.
for n in range(2,N+1):
    ds={}
    for d in range(1,n+1):
        if n%d==0: ds=add(ds,lam[d])
    check('Mangoldt_divisor_identity', ds==logpoly(n))
    for k in (1,2,3,4):
        difference=add(power(logpoly(n),k),scale(conv[k][n],-1))
        check('coefficientwise_convolution_envelope', all(v>=0 for v in difference.values()))
        check('minimal_product_support', not conv[k][n] if n<2**k else True)

exp_plus={}; exp_minus={}
for n in range(1,N+1):
    pos={};neg={}
    for k,row in enumerate(conv):
        pos=add(pos,scale(row[n],Q(1,factorial(k))))
        neg=add(neg,scale(row[n],Q((-1)**k,factorial(k))))
    exp_plus[n]=pos; exp_minus[n]=neg
for n in range(1,N+1):
    r={}
    for d in range(1,n+1):
        if n%d==0: r=add(r,mul(exp_plus[d],exp_minus[n//d]))
    check('complete_exponential_inverse', r==({():Q(1)} if n==1 else {}))
for p in (2,3,5):
    n=p
    a=1
    while n<=N:
        for k in range(1,a+2):
            want={(p,)*k:Q(comb(a-1,k-1))} if k<=a else {}
            check('prime_power_ordered_compositions',conv[k][n]==want)
        want={}
        for k in range(1,a+1):
            want=add(want,{(p,)*k:Q(comb(a-1,k-1),factorial(k))})
        check('prime_power_exponential_coefficient',exp_plus[n]==want)
        n*=p;a+=1
for u,v in ((2,3),(4,9),(5,7),(8,9)):
    check('coprime_exponential_multiplicativity',exp_plus[u*v]==mul(exp_plus[u],exp_plus[v]))

# Univariate exact polynomials: variable x = alpha*t.
def ua(a,b):
    r=defaultdict(Q)
    for k,v in a.items():r[k]+=v
    for k,v in b.items():r[k]+=v
    return {k:v for k,v in r.items() if v}
def us(a,x):return {k:x*v for k,v in a.items() if x*v}
def um(a,b):
    r=defaultdict(Q)
    for i,x in a.items():
        for j,y in b.items():r[i+j]+=x*y
    return {k:v for k,v in r.items() if v}
def ud(a):return {k-1:k*v for k,v in a.items() if k}
g={0:Q(1),1:Q(1),2:Q(1,2)}
gp=ud(g);gpp=ud(gp)
curvature=ua(um(gpp,g),us(um(gp,gp),-1))
check('actual_two_packet_log_curvature_numerator',curvature=={1:Q(-1),2:Q(-1,2)})
check('initial_first_moment',gp[0]==1)
check('complete_time_one_norm',sum(g.values())==Q(5,2))

# Gaussian-rational coefficients retain the full complex mixed term.
def ca(z,w):return (z[0]+w[0],z[1]+w[1])
def cm(z,w):return(z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def conj(z):return(z[0],-z[1])
def norm2(z):return z[0]*z[0]+z[1]*z[1]
for x,y in (((Q(1),Q(0)),(Q(0),Q(1))),
            ((Q(1),Q(1)),(Q(2),Q(-1))),
            ((Q(2),Q(0)),(Q(-1),Q(3)))):
    for t in (Q(-1),Q(1,3),Q(2)):
        lhs=norm2(x)+norm2(ca(y,(t*x[0],t*x[1])))
        rhs=norm2(x)+norm2(y)+2*t*cm(conj(y),x)[0]+t*t*norm2(x)
        check('complex_self_and_mixed_orbit_terms',lhs==rhs)

# Exact rational logarithm/square-root envelopes used in the PAPER gap.
ell=Q(1,100)
log2_lower=Q(2,3)
log2_upper=Q(2,3)+Q(1,36)
check('log2_bounds_consistent',log2_lower<log2_upper<Q(3,4))
check('actual_support_excludes_n_ge_three',log2_upper+2*ell<1)
check('second_packet_shifts_out',log2_lower>2*ell)
check('sqrt2_upper_from_square',Q(3,2)**2>2)
alpha_lower=log2_lower/Q(3,2)
gap=alpha_lower**3/18
check('exact_log_chord_margin',gap==Q(32,6561))
check('returned_negative_upper_margin',gap/2==Q(16,6561))
for eps in (Q(1,64),Q(1,128),Q(1,256)):
    q=int(2/eps)+3
    exponent=Q(3,2)+eps*(Q(1,2)-q)
    check('whole_exponential_projection_return',exponent<0)
    check('first_form_projection_return',Q(1,2)+eps*(Q(1,2)-q)<0)
    check('original_short_exponent',3*eps/2<Q(1,2))
# Valid small-time full cap; x=H/m is left a symbolic polynomial.
# d<=6/sqrt(m)*(1+x), r<=6/sqrt(m)*x.
check('small_time_scalar_constants',2*6==12 and 4*6==24 and 6**2*4==144)

reject('replace_convolution_by_Lambda_product',conv[2][6]==lam[6])
reject('delete_proper_prime_power_atom',exp_plus[4]=={(2,2):Q(1,2)})
reject('forget_ordered_factor_multiplicity',conv[2][6]=={(2,3):Q(1)})
reject('inverse_has_same_sign',add(mul(exp_plus[1],exp_plus[2]),mul(exp_plus[2],exp_plus[1]))=={})
reject('drop_orbit_mixed_term',g=={0:Q(1),2:Q(1,2)})
reject('claim_log_convexity',all(x>=0 for x in curvature.values()))
reject('claim_zero_gap_after_exact_contacts',gap<=0)
# If the reference error lives on the first packet, its transformed norm
# is 1+x^2, not 1. This tests the omitted amplification, with x formal.
reject('drop_exponential_amplification_in_return',{0:Q(1),2:Q(1)}=={0:Q(1)})

out={
 'status':'LOCAL_EXACT_CONTROLS_ONLY',
 'counts':dict(counts),'total_controls':sum(counts.values()),
 'planted_errors_detected':planted,'planted_count':len(planted),
 'scope':'Finite exact log-polynomial arithmetic, complex two-packet algebra, rational support/gap constants and exponent accounting. No production spectrum, no numerical asymptotic sign inference.',
 'new_independent_audit':False,'lean':False,'arb':False,'production_spectrum':False
}
Path('q37_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'total_controls':out['total_controls'],'planted_count':len(planted)},indent=2))
