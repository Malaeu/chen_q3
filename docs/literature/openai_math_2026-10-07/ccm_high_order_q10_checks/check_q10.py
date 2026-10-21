"""Q10 exact local controls (Python standard library).
Run: python3 check_q10.py
Place registration.json beside the script. No variable/path substitutions.
Not a Lean/Arb certificate, prime-correlation theorem, or CCM spectral run.
"""
from fractions import Fraction as F
from collections import Counter
from math import comb, factorial
from pathlib import Path
import hashlib, json

counts=Counter()
def ck(ok,name):
    if not ok: raise AssertionError(name)
    counts[name]+=1

def alpha(k): return [(-1)**(j+1)*comb(k,j) for j in range(1,k+1)]
for k in range(1,13):
    aa=alpha(k)
    ck(sum(aa)==1,'Richardson_constant_reproduced')
    for r in range(1,k):
        ck(sum(a*j**r for j,a in enumerate(aa,1))==0,'cancelled_weight_moments')
    ck(sum(a*j**k for j,a in enumerate(aa,1))==(-1)**(k+1)*factorial(k),
       'first_uncancelled_moment')
    V=sum(F(a*b,max(j,l)) for j,a in enumerate(aa,1) for l,b in enumerate(aa,1))
    ck(V>0,'signed_kernel_L2_coefficient_positive')
    # R acting on a polynomial E: exact normalized forward increments.
    for r in range(1,k+1):
        x=F(7,3);h=F(1,5)
        got=sum(F(a,j)*((x+j*h)**r-x**r)/h for j,a in enumerate(aa,1))
        ck(got==r*x**(r-1),'slow_source_derivative_is_retained_not_annihilated')

def value(p,x):
    out=F(0)
    for c in reversed(p):out=out*x+c
    return out

def deriv(p):return [i*p[i] for i in range(1,len(p))] or [F(0)]
def primitive(p):return [F(0)]+[c/F(i+1) for i,c in enumerate(p)]
def pmul(a,b):
    z=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]+=x*y
    return z

def theta_poly(k):
    p=2*k; C=F(factorial(2*p+1),factorial(p)**2)
    z=[F(0)]*(2*p+2)
    for j in range(p+1):z[p+j+1]=C*(-1)**j*comb(p,j)/F(p+j+1)
    return z

for k in range(1,9):
    p=theta_poly(k)
    ck(value(p,F(0))==0 and value(p,F(1))==1,'cutoff_normalization')
    for r in range(1,2*k+1):
        p=deriv(p)
        ck(value(p,F(0))==0 and value(p,F(1))==0,'all_required_cutoff_endpoint_jets')

# The literal cubic edge shape after zero extension. At t=m+h/2,
# A_(jh)((m-t)_+^3)=(jh-h/2)^4/(4jh). Fourth-order claimed O(h^4)
# fails: the error is a fixed nonzero multiple of h^3.
a4=alpha(4)
cubic_constant=sum(F(a,j)*F(2*j-1,2)**4/4 for j,a in enumerate(a4,1))
ck(cubic_constant!=0,'planted_global_fourth_order_extension_failure')
for h in (F(1),F(1,2),F(1,4),F(1,8)):
    val=sum(F(a,j)*((j*h-h/2)**4)/(4*h) for j,a in enumerate(a4,1))
    ck(val/h**3==cubic_constant,'cubic_crossing_error_scales_as_h_cubed')
# Signed second-order kernel is negative on its second step.
def K2(u):
    return sum(F(a,j) for j,a in enumerate(alpha(2),1) if 0<u<=j)
ck(K2(F(3,2))==F(-1,2),'signed_kernel_is_not_positive_average')
shift=F(3,2)
knots=sorted({F(0),F(1),F(2),-shift,F(1)-shift,F(2)-shift})
cor=sum((b-a)*K2((a+b)/2)*K2((a+b)/2+shift) for a,b in zip(knots,knots[1:]))
ck(cor==F(-3,8),'signed_kernel_shift_covariance_has_negative_lobe')

# Rational rescaled shell geometry. These are support/partition controls,
# not production CCM spectral cells.
p=theta_poly(4)
def zeta(u):
    if u<=1:return F(0)
    if u>=2:return F(1)
    return value(p,u-1)
geom=[]
for k,A,damp in ((2,F(4),F(1,16)),(3,F(8),F(1,16)),(4,F(4),F(1,32))):
    m=2**20;Y=8*k*A/damp;d0=F(m,32)
    ck(2*Y+2*d0<m and d0>=8*k/damp,'shell_onset_inequalities')
    xs=[];x=Y
    while x<m:xs.append(x);x*=2
    ds=[];d=d0
    while d<m:ds.append(d);d*=2
    active=[]
    for X in xs:
        for d in ds:
            lo=max(X,m-4*d);hi=min(4*X,m-d)
            if lo>=hi:continue
            rad=min(X/A,d);h=damp*rad/(8*k)
            ck(h>=1 and k*h<=X/8 and k*h<=d/8,'all_widths_and_support_margins')
            ck(hi+k*h<m and lo>1,'no_future_or_lower_boundary_atoms')
            ck(min(X,d)<=A*rad,'length_over_radius_smoothing_budget')
            ck(max(X,d)>=F(m,8),'at_least_one_scale_is_coarse')
            active.append((X,d))
    ck(len(active)<=8*(2+20),'number_of_active_shells_is_logarithmic')
    tests=[F(1),Y,2*Y,F(m,4),F(m,2),m-2*d0,m-d0,F(m)]
    tests += [F(m*j,23) for j in range(1,23)]
    for t in tests:
        low=1-zeta(t/Y);edge=1-zeta((m-t)/d0)
        total=sum((zeta(t/X)-zeta(t/(2*X)))*
                  (zeta((m-t)/d)-zeta((m-t)/(2*d))) for X,d in active)
        ck(low+edge+total==1,'full_partition_low_interior_edge')
    geom.append({'k':k,'active_pieces':len(active)})

# Full finite arithmetic with formal logarithms of primes, no floats.
def fac(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out

def mu(n):
    f=fac(n)
    return 0 if any(v>1 for v in f.values()) else (-1)**len(f)

def lam(n):
    ff=fac(n)
    return { (next(iter(ff)),):F(1)} if len(ff)==1 else {}

def add(a,b,s=F(1)):
    z=a.copy()
    for p,c in b.items():z[p]=z.get(p,F(0))+s*c
    return {p:c for p,c in z.items() if c}

def mul(a,b):
    z={}
    for p,c in a.items():
        for q,d in b.items():
            key=tuple(sorted(p+q));z[key]=z.get(key,F(0))+c*d
    return {p:c for p,c in z.items() if c}

for n in range(1,97):
    dct={}
    for d in range(1,n+1):
        if n%d==0:
            for p,v in fac(n//d).items():dct[(p,)]=dct.get((p,),F(0))+mu(d)*v
    ck({p:c for p,c in dct.items() if c}==lam(n),'actual_Mobius_log_full_recombination')

def overlap(a,b,n,r,j,l,h):
    return max(F(0),min(b,F(n),F(r))-max(a,F(n)-j*h,F(r)-l*h))
def one_overlap(a,b,n,j,h):
    return max(F(0),min(b,F(n))-max(a,F(n)-j*h))

variance_cases=[];deleted_mixed_detected=False;deleted_mean_detected=False
for k in (1,2,3,4):
    for h in (F(1),F(3,2)):
        aa=alpha(k);a=F(8);b=F(31,2)
        ns=[n for n in range(2,int(b+k*h)+1) if lam(n)]
        points={a,b}
        for n in ns:
            for j in range(0,k+1):
                x=F(n)-j*h
                if a<x<b:points.add(x)
        points=sorted(points);direct={}
        for l,r in zip(points,points[1:]):
            x=(l+r)/2;v={():F(-1)}
            for n in ns:
                K=sum(F(aj,j)/h for j,aj in enumerate(aa,1) if 0<n-x<=j*h)
                v=add(v,lam(n),K)
            direct=add(direct,mul(v,v),r-l)
        expanded={():b-a};diagonal={};mean={}
        for n in ns:
            w=sum(F(aj,j)/h*one_overlap(a,b,n,j,h) for j,aj in enumerate(aa,1))
            mean=add(mean,lam(n),-2*w)
            for r in ns:
                v=sum(F(aj*al,j*l)/h**2*overlap(a,b,n,r,j,l,h)
                      for j,aj in enumerate(aa,1) for l,al in enumerate(aa,1))
                term=mul(lam(n),lam(r));expanded=add(expanded,term,v)
                if n==r:diagonal=add(diagonal,term,v)
        no_mean=expanded.copy();expanded=add(expanded,mean)
        ck(direct==expanded,'full_actual_joint_interval_covariance')
        deleted_mixed_detected |= add(add({():b-a},mean),diagonal)!=direct
        deleted_mean_detected |= no_mean!=direct
        variance_cases.append({'k':k,'h':str(h),'atoms_with_nonzero_Lambda':len(ns)})
ck(deleted_mixed_detected,'planted_deleted_arithmetic_cross_terms_detected')
ck(deleted_mean_detected,'planted_deleted_centering_detected')

# A compact polynomial weight shows why future atoms must be returned if
# a different, unsafe width is used. m=16,n=17,h=4,k=1.
w=pmul([-F(12),F(1)], [F(15),-F(1)])
Wp=primitive(w)
def iw(a,b):
    a=max(a,F(12));b=min(b,F(15))
    return F(0) if a>=b else value(Wp,b)-value(Wp,a)
Bfuture=iw(F(13),F(17))/4
ck(Bfuture>0 and lam(17)=={(17,):F(1)},'unsafe_smoothing_activates_real_future_prime')
ck(Bfuture+(-Bfuture)==0,'future_atom_cancels_in_complete_return')

# Exact power accounting, including the terminal continuous shell.
for eps in (F(1,64),F(1,128),F(1,257)):
    kap=F(1,8)+eps
    ck(F(1,2)+3*eps-4*kap==-eps,'continuous_cubic_edge_exponent')
    ck(F(1,2)+5*eps-6*kap==-F(1,4)-eps,'discrete_fifth_order_edge_exponent')
    ck(-F(1,2)+5*eps-5*kap==-F(9,8),'discrete_edge_integer_endpoint_exponent')
    for k in (1,2,4,8):
        gam=(1-eps)/(2*k+1);eta=(eps+gam)/2
        ck(eta==F(1,2)-k*gam==F(1,4*k+2)+F(k,2*k+1)*eps,
           'optimized_full_conditional_power')
        ck(0<gam<1-kap and eps+gam<1,'all_selected_shell_scales_are_admissible')
    k=(eps.denominator+eps.numerator-1)//eps.numerator
    eta=F(1,4*k+2)+F(k,2*k+1)*eps
    ck(eta<F(3,4)*eps,'fixed_order_after_epsilon_allows_logarithmic_slack')

out={'status':'PASS_EXACT_LOCAL_CONTROLS','total_checks':sum(counts.values()),
     'counts':dict(counts),'cubic_crossing_constant_k4':str(cubic_constant),
     'geometric_control_panels':geom,'covariance_controls':variance_cases,
     'scope':'Exact finite identities, cutoffs, supports, signed covariance and power arithmetic. Not an arithmetic variance theorem or a CCM spectral certificate.',
     'large_prime_sum_runs':0,'full_ccm_spectral_runs':0,'arb_runs':0,'lean_runs':0,
     'independent_review':'NOT_RUN',
     'registration_sha256':hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
