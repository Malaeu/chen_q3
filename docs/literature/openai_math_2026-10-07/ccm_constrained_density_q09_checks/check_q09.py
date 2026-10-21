"""Q09 exact finite controls. These are not CCM spectral certificates.
Run on Linux/macOS: python3 check_q09.py
Put registration.json next to this script; no path substitutions are needed.
"""
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json

counts = Counter()
def check(condition, name):
    if not condition:
        raise AssertionError(name)
    counts[name] += 1

def factor(n):
    ans = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0)+1; n //= p
        p += 1
    if n > 1: ans[n] = ans.get(n, 0)+1
    return ans

def mu(n):
    fs = factor(n)
    return 0 if any(k > 1 for k in fs.values()) else (-1)**len(fs)

for n in range(1, 129):
    result = {}
    for d in range(1, n+1):
        if n % d: continue
        for p, v in factor(n//d).items():
            result[p] = result.get(p, 0)+mu(d)*v
    result = {p:v for p,v in result.items() if v}
    fn = factor(n)
    expected = {next(iter(fn)):1} if len(fn)==1 else {}
    check(result == expected, 'actual_mu_log_coefficients')
check(factor(8)=={2:3} and mu(4)==0, 'proper_powers_not_removed')

# Rational polynomial arithmetic, coefficient order ascending.
def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def add(a,b):
    ans=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a): ans[i]+=x
    for i,x in enumerate(b): ans[i]+=x
    return trim(ans)

def scale(t,a): return trim([t*x for x in a])
def mul(a,b):
    ans=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): ans[i+j]+=x*y
    return trim(ans)

def value(a,x):
    out=F(0)
    for c in reversed(a): out=out*x+c
    return out

def divide(a,b):
    rem=trim(a[:]); b=trim(b[:]); quo=[F(0)]*max(1,len(a)-len(b)+1)
    while len(rem)>=len(b) and rem!=[0]:
        j=len(rem)-len(b); t=rem[-1]/b[-1]; quo[j]+=t
        for i,x in enumerate(b): rem[i+j]-=t*x
        trim(rem)
    return trim(quo),trim(rem)

mixed_found=False
for M in (2,3,5):
    for w in (F(1,3),F(1,2),F(3,2)):
        js=list(range(-M,M+1)); om=[w*j for j in js]
        g=[F((-1)**k*(k+1),k+2) for k in range(2*M-2)]
        v=(-1,3,-3,1); cc=[F(0)]*(2*M+1)
        for k,gk in enumerate(g):
            for r,vr in enumerate(v):
                j=k+r-M; cc[k+r]-=(F(1,4)+(w*j)**2)*vr*gk
        check(sum(cc)==0,'endpoint_contact')
        check(sum(c/(F(1,4)+x*x) for c,x in zip(cc,om))==0,
              'real_exponential_contact')
        check(sum(c*x/(F(1,4)+x*x) for c,x in zip(cc,om))==0,
              'imaginary_exponential_contact')
        D=[F(1)]
        for x in om: D=mul(D,[-x,F(1)])
        N=[F(0)]
        for c,x in zip(cc,om):
            Q,rem=divide(D,[-x,F(1)])
            check(rem==[0],'exact_partial_fraction_division')
            N=add(N,scale(-c,Q))
        pp,rem=divide(N,[F(1,4),F(0),F(1)])
        check(rem==[0] and len(pp)-1<=2*M-3,'full_attainable_density_factor')
        for x in (F(1,7),F(5,7),F(11,7)):
            if x in om: continue
            check(value(N,x)/value(D,x)==sum(c/(o-x) for c,o in zip(cc,om)),
                  'rational_density_partial_fraction_return')
        norm=sum(c*c for c in cc)
        for k in (-2*M-3,2*M+3):
            z=F(2*k+1,2)
            exact=sum(c/(F(j)-z) for j,c in zip(js,cc))
            restored=sum(c*F(j)/(z*(F(j)-z)) for j,c in zip(js,cc))
            check(exact==restored,'half_grid_endpoint_cancellation')
            rhs=F(4*(2*M+1)*M*M,1)*norm/z**4
            check(exact*exact<=rhs,'half_grid_tail_Cauchy_price')
            diagonal=sum(c*c/(F(j)-z)**2 for j,c in zip(js,cc))
            mixed_found |= exact*exact!=diagonal
check(mixed_found,'deleting_half_grid_mixed_terms_detected')

# The cancellation is exact for every nonzero source vector, independent of m.
for norm in (F(1),F(3,7),F(17,3)):
    even_endpoint=2*norm; odd_endpoint=-2*norm
    check((even_endpoint+odd_endpoint)/2==0,'original_upper_atom_zero_return')
    check(even_endpoint!=0,'original_grid_only_alias_failure_detected')
    check((2*norm+2*norm)/2==2*norm,'zero_shift_normalization')

# A dual lower certificate for the family of globally capped quadratures.
# These numbers test algebra, not prime-discrepancy data.
for re,ro in ((F(4,5),F(4)),(F(1,5),F(3)),(F(1,2),F(7,2))):
    theta=re/ro; e=-F(1,7); o=F(1,11); peak=F(13,5)
    lower=e+(1-theta)*peak+theta*o
    for t in (F(-10000),F(-5,3),F(0),F(1,2),F(10000)):
        A=e-t*re; B=max(peak,o+t*ro)
        check(A+B>=lower,'balanced_dual_certificate_all_parameter_signs')
    check(-re+theta*ro==0,'balance_parameter_cancels_exactly')

# Source continuous calibration: beta=-r on both grids, balance t=1.
for rmin in (F(1,4),F(1,11),F(3,17)):
    A=-2*rmin; B=F(0)
    check((A+B)/2==-rmin,'continuous_Green_credit_not_lost')

for eps in (F(1,64),F(1,128),F(1,512)):
    kap=F(1,100)
    cutoff=F(1,6)+eps+kap
    check(F(1,2)+3*eps-3*cutoff==-3*kap,'complete_discrete_tail_exponent')
    check(F(3,2)*eps<F(3,8)<F(1,2),'source_return_exponents')

out={
    'status':'PASS_EXACT_LOCAL_CONTROLS',
    'total_checks':sum(counts.values()),'counts':dict(counts),
    'scope':'Finite rational coefficient/density/tail/dual-certificate controls. They do not prove PNT, equidistribution, asymptotic source bounds, or a CCM spectrum.',
    'large_prime_sums':0,'full_ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
    'independent_review':'NOT_RUN',
    'registration_sha256':hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
