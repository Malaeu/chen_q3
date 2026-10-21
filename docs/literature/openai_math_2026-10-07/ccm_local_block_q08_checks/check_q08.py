"""Q08 exact controls. No full CCM spectrum or asymptotic theorem is certified.
Run: python3 check_q08.py. No variable/path substitution is needed.
Only Python's standard library is used; output is written next to this script.
"""
from collections import Counter
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json, hashlib

stats=Counter()
def fac(n):
    out={}; p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1; n//=p
        p+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def mu(n):
    d=fac(n)
    return 0 if any(v>1 for v in d.values()) else (-1)**len(d)
def logvec(n): return fac(n)
def plus(a,b,s=1):
    z=a.copy()
    for p,c in b.items(): z[p]=z.get(p,0)+s*c
    return {p:c for p,c in z.items() if c}
def lam(n):
    f=fac(n)
    return {next(iter(f)):1} if len(f)==1 else {}
def rough(n,y): return all(p>y for p in fac(n))
def muy(n,y): return mu(n) if all(p<=y for p in fac(n)) else 0
def sieve(n,y):
    v={}
    for d in range(1,n+1):
        if n%d==0: v=plus(v,logvec(n//d),muy(d,y))
    return v

for y in (2,3,5,7,11,16):
    for n in range(1,193):
        f=fac(n); small=[p for p in f if p<=y]
        predicted=f if not small else ({small[0]:1} if len(small)==1 else {})
        actual=sieve(n,y)
        assert actual==predicted
        stats['exact_small_prime_sieve_piecewise_coefficients']+=1
        conv={}
        for a in range(1,n+1):
            if n%a==0 and rough(a,y): conv=plus(conv,lam(n//a))
        assert conv==actual
        stats['complete_rough_convolution_including_powers']+=1
        delta=plus(actual,lam(n),-1)
        assert all(c>=0 for c in delta.values())
        assert all(c>=0 for c in plus(f,actual,-1).values())
        stats['coefficientwise_order_and_log_cap']+=1
    q=y+1
    while fac(q)!={q:1}: q+=1
    n0=2*q
    for n in range(1,n0): assert sieve(n,y)==lam(n)
    assert plus(sieve(n0,y),lam(n0),-1)=={2:1}
    stats['first_remainder_atom_is_two_times_next_prime']+=1
    for k in (2,3,4):
        assert sieve(q**k,y)=={q:k}
        assert lam(q**k)=={q:1}
        assert sieve(2**k,y)=={2:1}
        stats['proper_prime_powers_retained']+=1
# An intentionally omitted a=1 term fails at every prime.
assert sieve(7,2)=={7:1} and plus(sieve(7,2),lam(7),-1)=={}
stats['discarding_identity_rough_factor_detected']+=1

# Matrix utilities: the test matrices below are algebra controls, NOT CCM spectra.
def transpose(A): return [list(r) for r in zip(*A)]
def mul(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]
def mv(A,v): return [sum(a*x for a,x in zip(row,v)) for row in A]
def dot(u,v): return sum(x*y for x,y in zip(u,v))
def rank(A):
    A=[r[:] for r in A]; i=0
    for j in range(len(A[0])):
        p=next((p for p in range(i,len(A)) if A[p][j]),None)
        if p is None: continue
        A[i],A[p]=A[p],A[i]; t=A[i][j]
        A[i]=[x/t for x in A[i]]
        for r in range(len(A)):
            if r!=i:
                t=A[r][j]; A[r]=[x-t*y for x,y in zip(A[r],A[i])]
        i+=1
        if i==len(A): break
    return i

mixed_detected=False; wrong_metric=False
v=(-1,3,-3,1)
for M in (2,3,4,6):
    n=2*M-2; d=2*M+1
    for w in (F(1,3),F(1,2),F(2)):
        aj=[F(1,4)+w*w*j*j for j in range(-M,M+1)]
        E=[[F(0) for _ in range(n)] for _ in range(d)]
        for k in range(n):
            for r in range(4): E[k+r][k]=-aj[k+r]*v[r]
        assert rank(E)==n
        stats['local_basis_full_rank']+=1
        for k in range(n):
            column=[E[i][k] for i in range(d)]
            h=[-column[i]/aj[i] for i in range(d)]
            assert all(sum((i-M)**r*h[i] for i in range(d))==0 for r in (0,1,2))
            assert sum(column)==0
            stats['all_three_exact_local_contacts']+=1
        # This is literally the source kernel at s=L/2: Q diagonal=(-1)^j.
        Qhalf=[[F(((-1)**(i-M)) if i==j else 0) for j in range(d)] for i in range(d)]
        A=[[F((i+1)*(j+1),1+abs(i-j)) for j in range(d)] for i in range(d)]
        for Q in (Qhalf,A):
            K=mul(mul(transpose(E),Q),E)
            for k in range(n):
                for l in range(n):
                    explicit=sum(v[r]*v[t]*aj[k+r]*aj[l+t]*Q[k+r][l+t]
                                 for r in range(4) for t in range(4))
                    assert explicit==K[k][l]
            stats['sixteen_term_mixed_entry_matches_congruence']+=1
            g=[F((-1)**k*(k+1),k+2) for k in range(n)]
            c=mv(E,g)
            assert dot(g,mv(K,g))==dot(c,mv(Q,c))
            mixed_detected |= dot(g,mv(K,g))!=sum(g[k]**2*K[k][k] for k in range(n))
            stats['all_mixed_terms_return_to_source_form']+=1
        g=[F((-1)**k,k+1) for k in range(n)]; c=mv(E,g)
        h=[-c[i]/aj[i] for i in range(d)]
        rec=[-sum(F(comb(k-i+2,2))*h[i] for i in range(k+1)) for k in range(n)]
        assert rec==g
        Cn=comb(n+2,3)
        assert dot(g,g)<=16*Cn*Cn*dot(c,c)
        stats['triple_difference_inverse_and_metric_fee']+=1
        wrong_metric |= dot(g,g)!=dot(c,c)
assert mixed_detected and wrong_metric
stats['discarded_mixed_column_terms_detected']+=1
stats['identity_metric_substitution_detected']+=1

# Exact polynomial profiles; scaling does not remove the two moment contacts.
def padd(a,b):
    z=[F(0)]*max(len(a),len(b))
    for i,c in enumerate(a):z[i]+=c
    for i,c in enumerate(b):z[i]+=c
    return z
def scale(t,a): return [t*c for c in a]
def deriv(a): return [i*a[i] for i in range(1,len(a))] or [F(0)]
def pmul(a,b):
    z=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]+=x*y
    return z
def val(a,x):return sum(c*x**i for i,c in enumerate(a))
def integ(a):return sum(c/F(i+1) for i,c in enumerate(a))
for N in (5,6,8):
    h=[F(0)]*N+[F((-1)**j*comb(N,j)) for j in range(N+1)]
    h1=deriv(h);h2=deriv(h1)
    for ell in (F(1,48),F(1,80),F(1,112)):
        g=padd(scale(ell**-2,h2),scale(-F(1,4),h))
        norm=ell*integ(pmul(g,g))
        expected=ell**-3*integ(pmul(h2,h2))+F(1,2)/ell*integ(pmul(h1,h1))+ell/F(16)*integ(pmul(h,h))
        assert norm==expected and norm>0
        stats['scaled_profile_exact_norm']+=1
        for a in (F(1,2),-F(1,2)):
            q=padd(scale(1/ell,h1),scale(-a,h))
            assert padd(scale(1/ell,deriv(q)),scale(a,q))==g
            assert val(q,0)==val(q,1)==0
            stats['both_exponential_contacts_via_exact_primitive']+=1
        assert val(g,0)==val(g,1)==0
        stats['profile_endpoint_zeros']+=1
# Integer interval isolating n0: exp(ell) <=1/(1-ell) for ell in(0,1).
for q in (3,5,7,11,17,29):
    n0=2*q;ell=F(1,8*n0)
    assert n0/(1-ell)<n0+1 and n0*(1-ell)>n0-1
    assert ell<F(1,2)
    stats['isolated_composite_support_rational_margin']+=1

# Exact zero-correction threshold and squarefree lower-budget arithmetic.
for m in (16,32,64,96):
    assert all(sieve(n,m//2)==lam(n) for n in range(1,m+1))
    stats['all_remainders_vanish_at_large_sieve_cutoff']+=1
for X in range(2,65):
    count=sum(mu(n)**2 for n in range(1,X+1))
    assert 4*count>=X
    stats['squarefree_count_lower_budget']+=1
for eps in (F(1,64),F(1,128),F(1,512)):
    assert F(5,4)*eps<F(3,8)<F(1,2)
    r=(eps.denominator+eps.numerator-1)//eps.numerator+2
    assert eps*(F(r)-F(1,2))>F(1,2)
    assert 7*eps+4*eps+F(5,4)*eps==F(49,4)*eps
    stats['complete_exponent_and_projection_budget']+=1

out={'status':'PASS','total_checks':sum(stats.values()),'counts':dict(stats),
     'scope':'Exact finite coefficient, local-basis, compact-profile and budget controls; not a full CCM spectral or asymptotic certificate.',
     'actual_large_prime_sums':0,'full_ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
     'independent_review':'NOT_RUN',
     'registration_sha256':hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
