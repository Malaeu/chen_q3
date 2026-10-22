"""Q11 exact finite algebra controls; not a CCM spectral/asymptotic certificate.
Run on Linux/macOS: python3 check_q11.py
Put registration.json beside this file. No variable/path substitution is needed.
Only the Python standard library is used.
"""
from fractions import Fraction as F
from collections import Counter
from itertools import product
from pathlib import Path
from math import comb
import json, hashlib

C = Counter()
def ck(v, name):
    if not v:
        raise AssertionError(name)
    C[name] += 1

def fac(n):
    ans = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: ans[n] = ans.get(n, 0) + 1
    return ans

def lam_prime(n):
    z = fac(n)
    return next(iter(z)) if len(z) == 1 else None

def mu(n):
    z = fac(n)
    return 0 if any(e > 1 for e in z.values()) else (-1)**len(z)

def fadd(a, b, scale=F(1)):
    out = a.copy()
    for p, x in b.items(): out[p] = out.get(p, F(0)) + scale*x
    return {p: x for p, x in out.items() if x}

def term(p, x): return {} if p is None or not x else {p: F(x)}

# Gaussian rationals, and finite vectors thereof.
def zadd(a, b): return (a[0]+b[0], a[1]+b[1])
def zsub(a, b): return (a[0]-b[0], a[1]-b[1])
def zscale(a, x): return (a[0]*x, a[1]*x)
def zinner(a, b): return (a[0]*b[0]+a[1]*b[1], a[0]*b[1]-a[1]*b[0])
def inner(a, b):
    z=(F(0), F(0))
    for x,y in zip(a,b): z=zadd(z,zinner(x,y))
    return z

def norm(a): return inner(a,a)[0]
def sub(a,b): return [zsub(x,y) for x,y in zip(a,b)]

# Exact graph identity in coordinates v_n=x_n/sqrt(n).
# Every coefficient below is rational times a formal log(p).
def data(N, kind):
    x={}
    for n in range(1,N+1):
        if kind == 0:
            x[n]=[(F(1),F(0)),(F(n%3,3),F(0))]
        elif kind == 1:
            x[n]=[(F((-1)**n,n+1),F(n%3-1,5)),(F(2-n%4,7),F((-1)**n,3))]
        else:
            x[n]=[(F(n%5,4),F(1-n%3,6)),(F(n%2,3),F(2-n%5,9))]
    return x

def graph_parts(N,x,ratio_cap=None):
    inc={};out={};g={};energy={}
    for n in range(1,N+1):
        for d in range(2,N//n+1):
            if ratio_cap is not None and d > ratio_cap: continue
            p=lam_prime(d)
            if p is None: continue
            den=F(1,n*d)
            inc=fadd(inc,term(p,den*norm(x[n*d])))
            out=fadd(out,term(p,den*norm(x[n])))
            g=fadd(g,term(p,2*den*inner(x[n],x[n*d])[0]))
            energy=fadd(energy,term(p,den*norm(sub(x[n*d],x[n]))))
    return inc,out,g,energy

for n in range(1,97):
    z={}
    for d in range(1,n+1):
        if n%d == 0:
            z=fadd(z,{p:F(e*mu(d)) for p,e in fac(n//d).items()})
    ck(z==term(lam_prime(n),1),'actual_Mobius_log_identity_including_powers')

for N in range(1,33):
    for kind in range(3):
        x=data(N,kind); mass=sum(norm(x[n])/n for n in x)
        ck(mass>0,'nonzero_exact_seed_mass')
        inc,out,g,en=graph_parts(N,x)
        logdiag={}
        for n in x:
            logdiag=fadd(logdiag,{p:F(e)*norm(x[n])/n for p,e in fac(n).items()})
        ck(inc==logdiag,'incoming_divisor_diagonal_equals_log_n')
        ck(fadd(fadd(inc,out),g,-1)==en,'full_Hilbert_graph_energy_identity')
        ck(all(v>=0 for v in en.values()),'energy_positive_in_each_formal_prime_log')
        coherent={}
        for d in range(2,N+1):
            t=(F(0),F(0))
            for n in range(1,N//d+1):
                t=zadd(t,zscale(inner(x[n],x[n*d]),F(1,n)))
            k2=(t[0]*t[0]+t[1]*t[1])/(d*mass*mass)
            multiples=sum(norm(x[j])/j for j in range(d,N+1,d))/mass
            ck(k2<=multiples<=1,'edge_coherence_paid_by_incoming_divisibility_mass')
            coherent=fadd(coherent,term(lam_prime(d),k2))
        upper={p:v/mass for p,v in logdiag.items()}
        ck(all(coherent.get(p,F(0))<=upper.get(p,F(0)) for p in set(coherent)|set(upper)),
           'joint_Mangoldt_coherence_energy_bound')
        # No square roots needed for the p=2 real-part gap test.
        t2=F(0)
        for n in range(1,N//2+1):t2+=inner(x[n],x[2*n])[0]/n
        K=N.bit_length() # 2^K>N, exactly floor(log_2 N)+1
        ck(t2<=0 or t2*t2<=2*mass*mass*(1-F(1,K*K))**2,
           'finite_support_fixed_prime_coherence_gap')
        for cap in (1,2,5,11):
            ai,ao,ag,ae=graph_parts(N,x,cap)
            extra=fadd(fadd(inc,out),fadd(ai,ao),-1)
            ck(fadd(fadd(inc,out),ag,-1)==fadd(ae,extra),
               'truncated_source_graph_retains_both_extra_diagonals')
            ck(all(v>=0 for v in extra.values()),'extra_graph_edges_have_paid_diagonals')

# Deliberate coefficient errors: proper powers and doubled edge.
x={1:[(F(1),F(0))],2:[(F(1),F(0))]}
i,o,g,en=graph_parts(2,x)
ck(en=={} and g=={2:F(1)},'source_Lean_calibration_energy_zero')
ck(fadd(fadd(i,o),g,-2)=={2:F(-1)},'doubled_edge_has_strict_negative_log2_margin')
x=data(16,1);i,o,g,en=graph_parts(16,x)
wrong_inc={}
for n in x:
    # Wrong: count only prime divisors once, omit p^2,p^3,...
    wrong_inc=fadd(wrong_inc,{p:norm(x[n])/n for p in fac(n)})
ck(i!=wrong_inc,'omitted_proper_prime_power_detected')

# A literal finite translation representation for algebra checks only.
# Multiplicative primes have additive integer lengths; this is not a physical CCM cell.
def length(n): return sum((p-1)*e for p,e in fac(n).items())
def shift(f,s): return {t-s:v for t,v in f.items()}
def fi(f,g): return sum(f.get(t,F(0))*g.get(t,F(0)) for t in set(f)|set(g))
def fnorm(f):return fi(f,f)
def fdiff(f,g):return {t:f.get(t,F(0))-g.get(t,F(0)) for t in set(f)|set(g)}
for N in (2,4,8,12):
    for f in ({0:F(1),1:F(-2),3:F(1)}, {0:F(1,2),2:F(1),5:F(-1,3)}):
        a={n:F(n%3+1,n+1) for n in range(1,N+1)}
        mass=sum(a[n]**2/n for n in a)
        lifted={n:{t:a[n]*v for t,v in shift(f,length(n)).items()} for n in a}
        ck(sum(fnorm(lifted[n])/n for n in a)==mass*fnorm(f),
           'translated_source_lift_preserves_norm_exactly')
        direct={};compressed={};en={};diag={}
        for n in a:
            for d in range(2,N//n+1):
                p=lam_prime(d)
                if p is None:continue
                direct=fadd(direct,term(p,2*fi(lifted[n],lifted[n*d])/(n*d)))
                compressed=fadd(compressed,term(p,2*a[n]*a[n*d]*fi(f,shift(f,length(d)))/(n*d)))
                en=fadd(en,term(p,fnorm(fdiff(lifted[n*d],lifted[n]))/(n*d)))
                diag=fadd(diag,term(p,(fnorm(lifted[n*d])+fnorm(lifted[n]))/(n*d)))
        ck(direct==compressed,'all_edge_correlations_match_the_nondiagonal_lift')
        ck(fadd(diag,direct,-1)==en,'complete_lifted_energy_keeps_physical_mixed_terms')
        if N==4:
            wrong={}
            for d in range(2,N+1):
                p=lam_prime(d)
                if p is not None:
                    # Free factor kappa_d=1 cannot be substituted; rational comparison
                    # uses deliberately incorrect copied graph overlaps instead.
                    wrong=fadd(wrong,term(p,2*mass*fi(f,shift(f,length(d)))/d))
            ck(wrong!=direct,'free_edge_recovery_detected')

# Complete multiplicative boxes, including prime powers above the depth.
primes=(2,3,5)
for K in (2,3,4,5):
    box={tuple(e) for e in product(range(K), repeat=3)}
    q=F(len(box))
    ck(len(box)==K**3,'divisor_box_exact_normalization')
    for i in range(3):
        ck(sum(F(e[i]) for e in box)/q==F(K-1,2),'divisor_box_incoming_log_budget')
    for a in range(K+2):
        e=(a,0,0)
        got=sum(tuple(n[j]+e[j] for j in range(3)) in box for n in box)/q
        ck(got==max(F(0),1-F(a,K)),'all_prime_powers_share_one_box_coordinate')
    for e in ((1,1,0),(1,2,1),(2,0,2),(K,1,0)):
        got=sum(tuple(n[j]+e[j] for j in range(3)) in box for n in box)/q
        expected=F(1)
        for a in e:expected*=max(F(0),1-F(a,K))
        ck(got==expected,'mixed_prime_box_intersections_retained')

# Compact physical profile: exponential contacts verified by exact primitives.
def padd(a,b):
    z=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):z[i]+=x
    for i,x in enumerate(b):z[i]+=x
    return z

def scale(a,x):return [x*v for v in a]
def deriv(a):return [i*a[i] for i in range(1,len(a))] or [F(0)]
def val(a,x):return sum(c*x**i for i,c in enumerate(a))
def mul(a,b):
    z=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]+=x*y
    return z

def integ(a):return sum(c/F(i+1) for i,c in enumerate(a))
for r in (4,7,10):
    h=[F(0)]*r+[F((-1)**j*comb(r,j)) for j in range(r+1)]
    ell=F(1,16); hp=deriv(h);hpp=deriv(hp)
    g=padd(scale(hpp,ell**-2),scale(h,-F(1,4)))
    n=ell*integ(mul(g,g))
    ck(n>0,'compact_constraint_profile_nonzero_norm')
    for a in (F(1,2),-F(1,2)):
        u=padd(scale(hp,1/ell),scale(h,-a))
        ck(padd(scale(deriv(u),1/ell),scale(u,a))==g and val(u,0)==val(u,1)==0,
           'both_original_exponential_moments_exact')
    ck(val(g,0)==val(g,1)==0,'physical_endpoint_contact_exact')
ck(2/(1-F(1,16))<3 and 2*(1-F(1,16))>1 and 1/(1-F(1,16))<2,
   'two_packet_overlap_isolates_only_actual_prime2')
for eps in (F(1,64),F(1,128),F(1,257)):
    r=(eps.denominator+eps.numerator-1)//eps.numerator+3
    ck(F(1,2)-eps*(F(r)-F(1,2))<0,
       'full_source_projection_error_smaller_than_any_log_gap')

out={'status':'PASS_EXACT_LOCAL_CONTROLS','total_checks':sum(C.values()),'counts':dict(C),
     'scope':'Finite Hilbert/divisor identities, actual formal prime logs and powers, lift norms, edge-correlation prices, multiplicative boxes and compact-profile contacts. Not a full CCM sign, asymptotic or RH certificate.',
     'lean_runs':0,'arb_runs':0,'full_ccm_spectral_runs':0,'large_prime_sum_runs':0,
     'independent_review':'NOT_RUN',
     'registration_sha256':hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
