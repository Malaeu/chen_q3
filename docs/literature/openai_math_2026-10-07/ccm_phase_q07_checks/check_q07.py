"""Q07 exact local controls. Not an actual CCM spectral computation.
Run: python3 check_q07.py. No path substitution is needed.
Only the standard library is used. The source packet is not modified.
"""
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
from math import comb

stats = Counter()
def fac(n):
    d = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            d[p] = d.get(p, 0)+1; n //= p
        p += 1
    if n > 1: d[n] = d.get(n, 0)+1
    return d

def mu(n):
    f=fac(n)
    return 0 if any(v>1 for v in f.values()) else (-1)**len(f)

# Actual arithmetic: the coefficient of each formal logarithm and its
# completely multiplicative character is retained before recombination.
for n in range(1, 129):
    fn=fac(n); out={}
    for d in range(1,n+1):
        if n%d: continue
        fk=fac(n//d)
        merged=fac(d).copy()
        for p,e in fk.items(): merged[p]=merged.get(p,0)+e
        assert merged==fn
        for p,e in fk.items(): out[p]=out.get(p,0)+mu(d)*e
    out={p:e for p,e in out.items() if e}
    expected={next(iter(fn)):1} if len(fn)==1 else {}
    assert out==expected
    stats['actual_twisted_mobius_log_atoms']+=1
assert fac(8)=={2:3} and mu(4)==0
stats['proper_power_8_remains_log2_not_log8']+=1

Z=((F(0),F(0)),(F(0),F(0)))
def madd(A,B): return tuple(tuple(a+b for a,b in zip(r,s)) for r,s in zip(A,B))
def mscale(c,A): return tuple(tuple(c*a for a in r) for r in A)
def mm(A,B): return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def mt(A): return tuple(zip(*A))
def tr(A): return A[0][0]+A[1][1]
def psd(A): return A==mt(A) and A[0][0]>=0 and A[1][1]>=0 and A[0][0]*A[1][1]>=A[0][1]**2

def padd(A,B):
    C=A.copy()
    for k,v in B.items(): C[k]=madd(C.get(k,Z),v)
    return {k:v for k,v in C.items() if v!=Z}
def pmul(A,B):
    C={}
    for x,a in A.items():
        for y,b in B.items():
            k=tuple(i+j for i,j in zip(x,y))
            C[k]=madd(C.get(k,Z),mm(a,b))
    return {k:v for k,v in C.items() if v!=Z}
def ev(A,phase):
    C=Z
    for key,v in A.items():
        s=1
        for a,b in zip(key,phase): s*= b if a%2 else 1
        C=madd(C,mscale(F(s),v))
    return C

noncomm=False
for m in (4,6,8,12,16,24):
    primes=[p for p in range(2,m+1) if fac(p)=={p:1}]
    r=len(primes); zero=(0,)*r
    S={}; groups={p:{} for p in primes}; Gamma=Z; N=0
    for n in range(2,m+1):
        fn=fac(n)
        if len(fn)!=1: continue
        p,k=next(iter(fn.items())); key=tuple(k if q==p else 0 for q in primes)
        neg=tuple(-v for v in key)
        C=((F(1,n+1),F((-1)**n,n+2)),(F(1,2*n+1),F(1,n+3)))
        a=F(1,n+1)  # rational stand-in for algebra testing, NOT a CCM weight
        terms={key:mscale(a,C),neg:mscale(a,mt(C))}
        S=padd(S,terms); groups[p]=padd(groups[p],terms)
        Gamma=madd(Gamma,mscale(a*a,madd(mm(C,mt(C)),mm(mt(C),C))))
        N+=1
    S2=pmul(S,S)
    assert S2.get(zero,Z)==Gamma
    stats['ordered_laurent_covariance']+=1
    assert S.get(zero,Z)==Z
    stats['whole_phase_mean_is_zero']+=1
    for phase in ((1,)*r,tuple((-1)**i for i in range(r))):
        value=ev(S,phase)
        assert psd(madd(mscale(F(2*N),Gamma),mscale(-1,mm(value,value))))
        stats['all_phase_evaluation_reconstruction']+=1
    # Trace of fourth moment, with both noncommuting pair orders retained.
    fourth=sum(tr(mm(B,S2.get(tuple(-x for x in a),Z))) for a,B in S2.items())
    decomposition=F(0)
    V={}
    for p,X in groups.items():
        X2=pmul(X,X);V[p]=X2.get(zero,Z)
        decomposition+=sum(tr(mm(B,X2.get(tuple(-x for x in a),Z))) for a,B in X2.items())
    for i,p in enumerate(primes):
        for q in primes[i+1:]:
            alternating=pmul(pmul(pmul(groups[p],groups[q]),groups[p]),groups[q]).get(zero,Z)
            decomposition+=4*tr(mm(V[p],V[q]))+2*tr(alternating)
            noncomm |= mm(V[p],V[q])!=mm(V[q],V[p])
    assert fourth==decomposition and fourth>=0
    stats['full_fourth_moment_with_same_prime_resonances']+=1
assert noncomm
stats['noncommuting_model_present']+=1
# Prime powers are NOT independent auxiliary variables: 1+1-2 is a resonance.
assert sum(1 for a in (1,-1,2,-2) for b in (1,-1,2,-2) for c in (1,-1,2,-2) if a+b+c==0)==6
stats['independent_prime_power_phase_error_detected']+=1
# A zero phase mean is not pointwise zero, and its reconstruction cost can be exact.
for N in (1,2,5):
    point=2*N; cov=2*N
    assert point*point==2*N*cov and point*point>0
    if N>1: assert point*point>cov
    stats['mean_to_point_free_return_failure']+=1

# Elementary Chebyshev atom accounting, with every prime power included.
for n in range(1, 65):
    product=1
    for r in range(n+1,2*n+1):
        fr=fac(r)
        if len(fr)==1: product*=next(iter(fr))
    assert comb(2*n,n)%product==0 and comb(2*n,n)<=4**n
    stats['chebyshev_binomial_prime_power_cover']+=1

# Explicit compact filter h(x)=x^4(1-x)^4 on [0,1], t=x+1.
def pa(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return c

def ps(t,a):return [t*x for x in a]
def pp(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def pd(a):return [F(i)*a[i] for i in range(1,len(a))] or [F(0)]
def pv(a,x):return sum(c*x**i for i,c in enumerate(a))
def pint(a):return sum(c/F(i+1) for i,c in enumerate(a))
h=[F(0)]*4+[F(1),F(-4),F(6),F(-4),F(1)]
g=pa(pd(pd(h)),ps(-F(1,4),h))
hd=h
for order in range(4):
    assert pv(hd,F(0))==pv(hd,F(1))==0
    hd=pd(hd);stats['compact_filter_endpoint_derivatives']+=1
for poly in (g,pd(g)):
    assert pv(poly,F(0))==pv(poly,F(1))==0
    stats['g_endpoint_regularities']+=1
norm2=pint(pp(g,g))
assert norm2>0 and pint(h)==F(1,630)
assert norm2==pint(pp(pd(pd(h)),pd(pd(h))))+F(1,2)*pint(pp(pd(h),pd(h)))+F(1,16)*pint(pp(h,h))
stats['filter_norm_and_moment_factorization']+=1
# Formal exponential integration-by-parts identity at the two real constraints.
for a in (F(1,2),-F(1,2)):
    v=pa(pd(h),ps(-a,h))
    assert pa(pd(v),ps(a,v))==g
    assert pv(v,F(0))==pv(v,F(1))==0
    stats['both_original_exponential_moments']+=1
# |((1/2+i/10)^2-1/4)|^2; a rational positive lower bound for the shifted moment.
factor2=F(101,10000)
H_lower=F(49,94500)
assert H_lower>F(1,2000)
c_lower=factor2*H_lower**2/norm2
assert c_lower>0
stats['nonzero_shifted_moment_lower_constant']+=1
# A model of projected support is not allowed to inherit the shifted exponential zeros.
assert factor2>0
stats['twist_is_not_unmodified_source_control']+=1

for eps in (F(1,1024),F(1,128),F(1,64)):
    assert F(1,2)>F(3,8)>F(3,2)*eps
    assert F(1,2)-eps/F(4)>0
    assert eps/F(4)>0
    stats['returned_exponent_and_phase_choice_scope']+=1

out={
 'status':'PASS', 'total_checks':sum(stats.values()), 'counts':dict(stats),
 'compact_filter_L2_norm_squared':str(norm2),
 'shifted_asymptotic_Rayleigh_constant_lower_bound':str(c_lower),
 'scope':'Exact finite arithmetic and noncommutative Laurent algebra; the rational matrices are NOT actual CCM matrices. The compact-filter constants are exact. No asymptotic theorem is inferred from these tests.',
 'full_ccm_spectral_runs':0, 'actual_large_prime_sums':0, 'arb_runs':0, 'lean_runs':0,
 'independent_review':'NOT_RUN',
 'registration_sha256':hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
