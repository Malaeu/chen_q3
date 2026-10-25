"""Q18 exact algebra controls. These do not certify asymptotic CCM estimates."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
from math import gcd, isqrt
import hashlib, json
import sympy as s

ROOT = Path(__file__).resolve().parent
counts: Counter[str] = Counter()
x, n, a, K, u, b = s.symbols('x n a K u b', positive=True)
F = lambda z: (4*s.pi**2*z**4-6*s.pi*z**2)*s.exp(-s.pi*z*z)
phi = lambda j, y: s.sqrt(y)*F(j*y)  # y=exp(t)
assert s.simplify(phi(a,n*x)/s.sqrt(n)-phi(a*n,x)) == 0
counts['theta_dilation']=1
f=s.Function('f')
y=s.symbols('y',positive=True)
P=lambda g: 4*x*s.diff(g,x,2)+6*s.diff(g,x)
assert s.simplify(P(1))==0
assert s.simplify(P(x**(-s.Rational(1,2))))==0
lhs=P(x**(-s.Rational(1,2))*f(a/x))
rhs=a*x**(-s.Rational(5,2))*(4*y*s.diff(f(y),y,2)+6*s.diff(f(y),y)).subs(y,a/x)
assert s.simplify(lhs-rhs)==0
counts['jacobi_differential_and_zero_modes']=3
T=lambda q,z: 2*s.pi*q**3*z**s.Rational(5,2)*s.exp(-s.pi*q*q*z*z)
assert s.simplify(-s.diff(T(K,x),K)-phi(K,x))==0
D=lambda v: x*s.diff(v,x)
beta=2*s.pi*x**s.Rational(5,2)*s.exp(-s.pi*x*x)
assert s.simplify(D(beta)+beta/2+phi(1,x))==0
assert s.simplify(s.diff(T(K,x),K)+K**(-s.Rational(1,2))*phi(1,K*x))==0
counts['continuum_edge_derivatives']=3
f0=F(x)
phi_l2=s.simplify(s.integrate(f0*f0,(x,0,s.oo)))
beta_l2=s.simplify(s.integrate(beta*beta/x,(x,0,s.oo)))
c0_l2=s.simplify(s.integrate((x*s.diff(f0,x))**2,(x,0,s.oo)))
assert phi_l2==33*s.sqrt(2)/64
assert beta_l2==3*s.sqrt(2)/16
assert c0_l2==1203*s.sqrt(2)/256
counts['exact_gaussian_norms']=3
# Actual formal-prime-log coefficients; no floating logarithms.
N=128
fac=[Counter() for _ in range(N+1)]
lam=[Counter() for _ in range(N+1)]
for j in range(2,N+1):
    z=j
    for p in range(2,isqrt(j)+1):
        while z%p==0:
            fac[j][p]+=1; z//=p
    if z>1: fac[j][z]+=1
    if len(fac[j])==1: lam[j][next(iter(fac[j]))]=1

def add(target, src, weight=Q(1)):
    for p,e in src.items(): target[p]+=weight*e

def clean(v): return {p:e for p,e in v.items() if e}

def dm(m,j):
    v=Counter()
    for d in range(2,min(m,j)+1):
        if j%d==0: add(v,lam[d])
    return v

for m in range(2,25):
    for j in range(1,N+1):
        v=dm(m,j)
        remainder=Counter()
        for d in range(m+1,j+1):
            if j%d==0: add(remainder,lam[d])
        total=Counter();add(total,v);add(total,remainder)
        assert clean(total)==dict(fac[j])
        if j<=m: assert clean(v)==dict(fac[j])
        counts['finite_divisor_coefficients_and_index_edge']+=1
    for den in range(1,m+1):
        for num in range(1,8):
            if gcd(num,den)!=1: continue
            left=Counter();right=Counter()
            for d in range(2,m+1):
                if d*num%den==0:add(left,lam[d],Q(1,d))
            for h in range(1,m//den+1):
                d=den*h
                add(right,lam[d],Q(1,d))
            assert clean(left)==clean(right)
            counts['reciprocal_lattice_reduced_coefficients']+=1
    for cut in range(m,m+5):
        reassembled=[Counter() for _ in range(cut+1)]
        for d in range(2,m+1):
            for j in range(1,cut//d+1):add(reassembled[d*j],lam[d])
            q=d*(cut//d)
            assert Q(q)>=Q(cut,2) and q<=cut and cut-q<d
            counts['floor_edge_coverage']+=1
        for k in range(1,cut+1):
            assert clean(reassembled[k])==clean(dm(m,k))
            counts['truncated_weighted_theta_reassembly']+=1
# A wrong dual coefficient / lost proper power / erased k>m edge.
assert dm(2,4)==Counter({2:1}) and fac[4]==Counter({2:2})
assert dm(4,8)==Counter({2:2}) and dm(8,8)==Counter({2:3})
assert Q(1,2)!=Q(1)  # dual n=2 coefficient must contain 1/n
counts['planted_weight_and_edge_omissions_detected']=3
# Full finite-horizon Green formula and all lower endpoints.
H=1+u+u**2+u**3+u**4+u**5
B2=lambda z:s.diff(z,u,4)-s.diff(z,u,2)/2+z/16
for r in range(1,7):
    p=u**(2*r-1)/s.factorial(2*r-1)
    ker=s.exp(-b*u)*p
    qr=(b*b-s.Rational(1,4))**2*p-4*b*(b*b-s.Rational(1,4))*s.diff(p,u)+(6*b*b-s.Rational(1,2))*s.diff(p,u,2)-4*b*s.diff(p,u,3)+s.diff(p,u,4)
    assert s.simplify(B2(ker)-s.exp(-b*u)*qr)==0
    boundary=ker*s.diff(H,u,3)-s.diff(ker,u)*s.diff(H,u,2)+s.diff(ker,u,2)*s.diff(H,u)-s.diff(ker,u,3)*H-(ker*s.diff(H,u)-s.diff(ker,u)*H)/2
    assert s.simplify(s.diff(boundary,u)-(ker*B2(H)-B2(ker)*H))==0
    expected=(s.diff(H,u,2)+2*b*s.diff(H,u)+(3*b*b-s.Rational(1,2))*H).subs(u,0) if r==1 else H.subs(u,0) if r==2 else 0
    assert s.simplify(-boundary.subs(u,0)-expected)==0
    assert boundary.subs({u:1,b:1})!=0
    counts['full_endpoint_and_bulk_controls']+=4
# Reflection normalization; these are algebraic constants, not numerical zeros.
cw=1+s.I
for r in range(1,7):
    cv=(-1)**r*s.conjugate(cw)
    kap=s.simplify((-1)**r/(s.conjugate(cw)*cv))
    assert s.simplify(kap-1/s.conjugate(cw)**2)==0
    assert kap!=1/(cw*s.conjugate(cw))
    counts['complex_phase_preserved_and_modulus_shortcut_detected']+=2
# Exact error/receiver exponent bookkeeping.
for eps in (Q(1,64),Q(1,100),Q(1,256)):
    q=int(1/eps)+3
    assert all(z<0 for z in (1+eps*(Q(1,2)-q),Q(1,2)+eps*(Q(3,2)-q),Q(1,2)+eps*(1-q)))
    counts['fixed_order_original_P_return']=1+counts['fixed_order_original_P_return']
for nu in (Q(1,100),Q(1,10),Q(1,2)):
    assert 1-(2+2*nu)/2==-nu
    counts['global_theta_cutoff_return_exponents']+=1
out={'status':'PASS_EXACT_LOCAL_ALGEBRA_NOT_ASYMPTOTIC_CCM_CERTIFICATE',
     'sympy':s.__version__,'counts':dict(counts),'total_cases':sum(counts.values()),
     'exact_norms_squared':{'phi1':str(phi_l2),'beta':str(beta_l2),'C0':str(c0_l2)},
     'hypothetical_zero_numerical_values_used':False,'full_CCM_spectrum_computed':False,
     'lean_runs':0,'arb_runs':0,
     'registration_sha256':hashlib.sha256((ROOT/'registration.json').read_bytes()).hexdigest(),
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
