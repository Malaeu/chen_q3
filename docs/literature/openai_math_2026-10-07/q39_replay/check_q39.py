#!/usr/bin/env python3
"""Exact finite controls for Q39; NOT an asymptotic/CCM spectral certificate."""
from __future__ import annotations
import json
from fractions import Fraction as F
from math import gcd, isqrt
from pathlib import Path
import sympy as sp

checks: dict[str, int] = {}
rejections: list[str] = []

def record(name: str, cases: int, ok: bool) -> None:
    if not ok:
        raise AssertionError(name)
    checks[name] = cases

def reject(name: str, false_statement: bool) -> None:
    if false_statement:
        raise AssertionError('Planted failure was not detected: '+name)
    rejections.append(name)

def factors(n: int) -> dict[int, int]:
    out: dict[int,int] = {}
    d=2
    while d*d<=n:
        while n%d==0:
            out[d]=out.get(d,0)+1; n//=d
        d+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def mu(n: int) -> int:
    fac=factors(n)
    return 0 if any(e>1 for e in fac.values()) else (-1)**len(fac)

def divs(n: int) -> list[int]:
    return [d for d in range(1,n+1) if n%d==0]

def logvec(n: int) -> dict[int,int]:
    return factors(n)

def addvec(a: dict[int,int], b: dict[int,int], scale: int=1) -> dict[int,int]:
    c=a.copy()
    for p,v in b.items(): c[p]=c.get(p,0)+scale*v
    return {p:v for p,v in c.items() if v}

def mat(n: int) -> sp.Matrix:
    z=sp.Rational(n%7-3,n+1)+sp.I*sp.Rational(n%5-2,n+2)
    return sp.Matrix([[sp.Rational(n%11-5,n+3),z],
                      [sp.conjugate(z),sp.Rational(n%13-6,n+4)]])

def zero() -> sp.Matrix:
    return sp.zeros(2)

def eq(a: sp.Matrix, b: sp.Matrix) -> bool:
    return all(sp.simplify(v)==0 for v in a-b)

# Actual arithmetic, formal prime logarithms rather than floating logs.
ok=True
for n in range(1,129):
    out={}
    for d in divs(n): out=addvec(out,logvec(n//d),mu(d))
    fac=factors(n)
    expected={next(iter(fac)):1} if len(fac)==1 else {}
    ok &= out==expected
record('actual_mu_convolution_formal_logs',128,ok)

pairs=[(2,3),(2,5),(3,5),(5,7),(7,11)]
record('actual_prime_dilation_mu_product',len(pairs)*128,
       all(mu(p*k)*mu(q*k)==mu(k)**2*int(gcd(k,p*q)==1)
           for p,q in pairs for k in range(1,129)))

# Full physical-source algebra is tested with generic Hermitian entries:
# these are controls of linear identities, not production CCM cells.
case_count=0; good=True
for m,R,p,q in [(24,1,2,3),(37,3,3,5),(60,7,5,7)]:
    D={n:(mat(n) if R<n<m else zero()) for n in range(1,m+1)}
    H=sp.Rational(1,p)+sp.Rational(1,q)
    T=sum((mu(n)*D[n] for n in range(1,m+1)),zero())
    J=zero()
    for k in range(1,m//p+1):
        J+=mu(k)*sum((D[ell*k] for ell in (p,q)
                      if ell*k<=m and k%ell!=0),zero())
    residual=sum((mu(n)*(int(n%p==0)+int(n%q==0)-H)*D[n]
                  for n in range(1,m+1)),zero())
    good &= eq(H*T,-J-residual)
    good &= eq(T,T.conjugate().T) and eq(J,J.conjugate().T)
    case_count+=1
record('finite_prime_incidence_full_complex_matrix',case_count,good)

# Complete full-k hyperbola reconstructed coefficient by coefficient.
good=True; cases=0
for m in [16,25,32]:
    primes=sorted({p for n in range(2,m+1) for p in factors(n)})
    for ell in primes:
        lhs=zero(); rhs=zero()
        for d in range(1,m+1):
            for k in range(1,m//d+1):
                if d*k==m: continue  # model h(m)=0, not a dropped scalar weight
                lhs+=mu(d)*factors(k).get(ell,0)*mat(d*k)
        for n in range(2,m):
            fac=factors(n)
            if len(fac)==1 and ell in fac: rhs+=mat(n)
        good &= eq(lhs,rhs); cases+=1
record('full_k_complex_hyperbolic_return',cases,good)

# Energy identity: no omission of the shared k or cross term.
good=True
for m,p,q in [(31,2,3),(63,3,5),(127,5,7)]:
    beta=lambda n: F((n%9)-4,n+1) if n<=m else F(0)
    energy=F(0); diagonal=F(0); cross=F(0)
    for k in range(1,m//p+1):
        x=beta(p*k) if k%p else F(0)
        y=beta(q*k) if k%q else F(0)
        energy+=mu(k)**2*(x+y)**2
        diagonal+=mu(k)**2*(x*x+y*y)
        cross+=mu(k)**2*x*y
    gamma=sum((mu(p*k)*mu(q*k)*beta(p*k)*beta(q*k)
               for k in range(1,m//q+1)),F(0))
    good &= energy==diagonal+2*gamma and cross==gamma
record('coupled_energy_both_cross_orientations',3,good)

# Exact coprime squarefree count before estimating floors.
good=True; cases=0
for p,q in pairs:
    for n in range(1,81):
        direct=sum(mu(k)**2 for k in range(1,n+1) if gcd(k,p*q)==1)
        rhs=sum(mu(d)*sum(1 for v in range(1,n//(d*d)+1)
                         if gcd(v,p*q)==1)
                for d in range(1,isqrt(n)+1) if gcd(d,p*q)==1)
        good &= direct==rhs; cases+=1
record('squarefree_coprime_floor_identity',cases,good)

# Symbolic analytic algebra controls, not tests of the smooth infinite profile.
t,z=sp.symbols('t z', real=True)
x=sp.symbols('x',positive=True)
chi=t**4*(1-t)**4
u=sp.diff(chi,t,2)-chi/4
record('two_contact_integrals_polynomial_control',2,
       all(sp.integrate(sp.exp(s*t/2)*u,(t,0,1))==0 for s in [-1,1]))
pref=sp.expand((z*z-sp.Rational(1,4))**2)
record('double_mellin_zero_prefactor',4,
       all(sp.diff(pref,z,j).subs(z,a)==0
           for a in [sp.Rational(1,2),sp.Rational(-1,2)] for j in [0,1]))
rr=sp.Function('rr'); T=sp.symbols('T',positive=True)
w=sp.log(x)/sp.sqrt(x)*rr(sp.log(x/T))
rhs=x**(-sp.Rational(3,2))*((1-sp.log(x)/2)*rr(sp.log(x/T))+
       sp.log(x)*sp.Subs(sp.Derivative(rr(t),t),t,sp.log(x/T)))
record('euler_weight_derivative_full_log',1,sp.simplify(sp.diff(w,x)-rhs)==0)
W=sp.Function('W'); X=sp.symbols('X',positive=True)
record('scaled_stieltjes_derivative',1,
       sp.simplify(sp.diff(W(x/X)/x,x)-
       (x/X*sp.Subs(sp.Derivative(W(t),t),t,x/X)-W(x/X))/x**2)==0)

# Projection exponent is strictly negative for the prescribed fixed order.
e=sp.symbols('e',positive=True)
qmin=2/e+2
record('projection_exponent_margins',3,
       sp.simplify(sp.Rational(1,2)+e*(sp.Rational(1,2)-qmin))<0 and
       sp.simplify(e/2-sp.Rational(1,2)).subs(e,sp.Rational(1,32))<0 and
       sp.simplify(sp.Rational(1,2)+e*(sp.Rational(1,2)-qmin)+e)<0)

# Plant genuinely incorrect variants. Detect with exact witnesses.
reject('omit_prime_divisibility_mask',mu(2*2)==-mu(2))
reject('replace_joint_mu_product_by_independent_zero',mu(2*1)*mu(3*1)==0)
reject('delete_centered_incidence_residual',
       -(F(1,2)+F(1,3))==0)  # D_5=1, R=1, p=2,q=3: mu(5)=-1, omega(5)=0, J=0
reject('drop_one_cross_orientation',(F(2)+F(3))**2==F(2)**2+F(3)**2+F(2)*F(3))
reject('omit_proper_prime_powers',
       sum(mu(d)*factors(4//d).get(2,0) for d in divs(4))==0)
reject('replace_log_k_by_log_dk',
       sum(mu(d)*factors(2).get(2,0) for d in divs(2))==1)
reject('replace_coprime_squarefree_by_unrestricted',
       sum(mu(k)**2 for k in range(1,7) if gcd(k,6)==1)==
       sum(mu(k)**2 for k in range(1,7)))
reject('use_single_instead_of_double_zero',
       sp.diff(z*z-sp.Rational(1,4),z).subs(z,sp.Rational(1,2))==0)
# Constant raw Gram test alone does not give a small total spectral return.
reject('forget_projection_linear_cross_terms',(1+F(1,10))**2-1==F(1,10)**2)

out={'scope':'Exact finite algebra and auxiliary controls only; no production spectrum, interval proof, or asymptotic inference.',
     'groups':checks,'groups_passed':len(checks),'individual_equalities':sum(checks.values()),
     'planted_failures_detected':rejections,'planted_count':len(rejections),
     'external_theorem_executed':False,'lean':False,'arb':False}
Path(__file__).with_name('check_q39_results.json').write_text(
    json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True))
