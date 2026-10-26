#!/usr/bin/env python3
"""Exact, finite local controls for Q36. Not a production CCM sign proof.

Uses only Python's standard library. Formal Fourier coefficients stand for
actual prime-power frequency labels; rational amplitudes test algebra, not
transcendental signs or the universal analytic estimates.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from math import comb, gcd
from pathlib import Path
import json

counts = Counter()
planted = []

def check(label, ok):
    if not ok:
        raise AssertionError(label)
    counts[label] += 1

def reject(label, statement):
    if statement:
        raise AssertionError('Planted error survived: ' + label)
    planted.append(label)

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

def valuation(n, p):
    a = 0
    while n % p == 0:
        n //= p
        a += 1
    return a

# Proof ingredients for psi(m) >= (m-1)log(2)-log(m+1):
# binomial(2n,n) divides lcm(1,...,2n), and is the largest binomial term.
for n in range(1, 33):
    lcm = 1
    for j in range(1, 2*n+1):
        lcm = lcm*j//gcd(lcm, j)
    b = comb(2*n,n)
    check('central_binomial_divides_full_lcm', lcm % b == 0)
    check('central_binomial_maximum_lower_mass', (2*n+1)*b >= 4**n)
    for p in factor(lcm):
        v = 0
        q = p
        while q <= 2*n:
            digit = (2*n)//q - 2*(n//q)
            if digit not in (0,1):
                raise AssertionError('bad Legendre digit')
            v += digit
            q *= p
        if v != valuation(b,p):
            raise AssertionError('Legendre mismatch')
    check('all_prime_power_binomial_digits_retained', True)

# Laurent frequency algebra on positive rational ratios: e^{i xi log(r)}.
# Rational coefficients are arbitrary probes of the exact joint algebra.
def add(a,b):
    c=defaultdict(Q)
    for k,v in a.items():c[k]+=v
    for k,v in b.items():c[k]+=v
    return {k:v for k,v in c.items() if v}

def scale(a,s):
    return {k:s*v for k,v in a.items() if s*v}

def mul(a,b):
    c=defaultdict(Q)
    for n,x in a.items():
        for k,y in b.items():c[n*k]+=x*y
    return {k:v for k,v in c.items() if v}

def prime_powers(m):
    return [n for n in range(2,m+1) if len(factor(n))==1]

def symbol(weights):
    out={}
    for n,w in weights.items():
        out=add(out,{Q(n):w,Q(1,n):w})
    return out

for m in (8,16,30,64):
    ns=prime_powers(m)
    w={n:Q(n%7+1,n+1) for n in ns}
    a=symbol(w)
    check('true_prime_power_frequency_support', set(a)=={Q(n) for n in ns}|{Q(1,n) for n in ns})
    check('zero_full_frequency_mean', a.get(Q(1),0)==0)
    a2=mul(a,a)
    check('diagonal_long_mean_square', a2.get(Q(1),0)==2*sum((v*v for v in w.values()),Q(0)))
    byprime={}
    for n in ns:
        p,k=next(iter(factor(n).items()))
        byprime.setdefault(p,{})[n]=w[n]
    rebuilt={}
    for block in byprime.values():rebuilt=add(rebuilt,symbol(block))
    check('all_powers_within_same_prime_coordinate', rebuilt==a)
    # Arbitrary second measure stands for a quadrature of the continuum;
    # cancellation is an exact algebraic test, not a continuum approximation proof.
    g=symbol({2:Q(3,4),3:Q(2,5),5:Q(7,6)})
    b=add(a,scale(g,-1))
    check('full_discrete_continuous_square',mul(b,b)==add(add(a2,scale(mul(a,g),-2)),mul(g,g)))
    check('continuous_control_exact_zero',mul(add(g,scale(g,-1)),add(g,scale(g,-1)))=={})

for p,q in ((5,7),(11,13),(17,19),(29,31)):
    a={Q(p):Q(1,2),Q(1,p):Q(1,2)}
    b={Q(q):Q(1,2),Q(1,q):Q(1,2)}
    check('mixed_cosines_product_and_ratio',mul(a,b)=={Q(p*q):Q(1,4),Q(1,p*q):Q(1,4),Q(p,q):Q(1,4),Q(q,p):Q(1,4)})
    check('haar_mixed_character_is_zero',mul(a,b).get(Q(1),0)==0)

# Exact rational gap selection on genuine finite prime sets.
# These are combinatorial diagnostics, not verification of a late-m asymptotic.
for m in (256,1024,4096):
    ps=[p for p in range(m//64+1,m+1) if factor(p)=={p:1}]
    gaps=[ps[j+1]-ps[j] for j in range(len(ps)-1)]
    k=min(range(len(gaps)),key=gaps.__getitem__)
    p,q=ps[k],ps[k+1]
    check('finite_true_prime_gap_pigeonhole',min(gaps)*(len(ps)-1)<=m)
    check('ratio_log_upper_uses_positive_gap',Q(q-p,p)>0 and p<q<=m)

# Constant bookkeeping is exact; pi is left formal in the PAPER proof.
check('original_P_ratio_loss_constant', Q(1024**2,2)==524288)
check('cosine_mixed_loss_constant', Q(1024**2,4)==262144)
check('long_phase_tail_chernoff_optimization', Q(1,4)-2*Q(1,16)==Q(1,8))
check('prime_power_diagonal_lower',Q(1,2)**2/2==Q(1,8))
check('finite_certificate_saturation_coefficient',Q(8,1)*Q(1,8)/256==Q(1,256))
for e in (Q(1,64),Q(1,128),Q(1,256)):
    check('pair_ratio_error_decays_on_original_schedule',2*e-2<0)
    check('full_frequency_tail_exponent',Q(1,2)+3*e-3*(Q(1,6)+e+Q(1,100))==-Q(3,100))
    check('short_fee_has_vanishing_exponent',3*e/2<Q(1,2))

# Intentionally broken identities or hypothesis substitutions.
w={2:Q(2),4:Q(3),8:Q(5),3:Q(7),9:Q(11)}
a=symbol(w);a2=mul(a,a)
reject('delete_proper_prime_powers',symbol({n:v for n,v in w.items() if factor(n)=={n:1}})==a)
reject('give_each_power_an_independent_prime_phase',a2.get(Q(4),0)==Q(0))
g=symbol({2:Q(1),3:Q(2)})
reject('omit_discrete_continuous_mixed_sector',mul(add(a,scale(g,-1)),add(a,scale(g,-1)))==add(mul(a,a),mul(g,g)))
reject('nonzero_continuous_price_is_exact_background',add(mul(g,g),mul(g,g))=={})
# For x=log(3/2), 0<x<1/2, so the alternating sine estimate gives
# sinc(x)>=1-x^2/6>23/24. This is a finite-time, actual integer-ratio
# control; neither x nor its sign is evaluated with floating point.
sinc_lower = 1-Q(1,2)**2/6
check('finite_sinc_certified_lower',sinc_lower==Q(23,24))
reject('finite_frequency_sinc_is_kronecker_delta',sinc_lower<=0)
# At m=64 the true prime labels 11,13 have product>m, but their ratio is
# inside the physical support. This tests support algebra, not the value
# of a production quadratic form.
prod=mul({Q(11):Q(1,2),Q(1,11):Q(1,2)},
         {Q(13):Q(1,2),Q(1,13):Q(1,2)})
retained={r:v for r,v in prod.items() if Q(1,64)<r<64}
check('retain_ratio_after_product_support_cut',retained=={Q(11,13):Q(1,4),Q(13,11):Q(1,4)})
reject('discard_ratio_channel_when_product_exceeds_m',retained=={})

out={
 'status':'LOCAL_EXACT_CONTROLS_ONLY',
 'counts':dict(counts),'total_controls':sum(counts.values()),
 'planted_errors_detected':planted,'planted_count':len(planted),
 'scope':'Integer/binomial, rational Laurent-algebra and exponent bookkeeping. No production CCM spectrum, no transcendental sign inference, no cofinal inference from tests.',
 'new_independent_audit':False,'lean':False,'arb':False,'production_spectrum':False
}
Path('q36_checks.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'total_controls':out['total_controls'],'planted_count':len(planted)},indent=2))
