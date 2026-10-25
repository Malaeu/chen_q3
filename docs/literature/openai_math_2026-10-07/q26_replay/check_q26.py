#!/usr/bin/env python3
"""Finite exact controls for Q26. Not a proof of the asymptotic CCM claim.
Run: python check_q26.py > exact_results.json   (requires SymPy).
No numerical value is assigned to an off-critical zero.
"""
from __future__ import annotations
import json
from collections import defaultdict
from fractions import Fraction
import sympy as sp

passed: list[str] = []
planted: list[str] = []

def check(name: str, condition: bool) -> None:
    if not bool(condition):
        raise AssertionError(name)
    passed.append(name)

def reject(name: str, false_condition: bool) -> None:
    if bool(false_condition):
        raise AssertionError('Planted error was not detected: ' + name)
    planted.append(name)

def factors(n: int) -> dict[int, int]:
    ans: dict[int, int] = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        ans[n] = ans.get(n, 0) + 1
    return ans

def divisors(n: int) -> list[int]:
    return [d for d in range(1, n+1) if n % d == 0]

def d2(n: int) -> int:
    ans = 1
    for e in factors(n).values():
        ans *= e+1
    return ans

def lam(n: int, primes_only: bool = False) -> dict[int, sp.Expr]:
    f = factors(n)
    if len(f) == 1:
        p, e = next(iter(f.items()))
        if not primes_only or e == 1:
            return {p: sp.Integer(1)}
    return {}

def add(out: dict, vec: dict, scale=sp.Integer(1)) -> None:
    for p, v in vec.items():
        out[p] = out.get(p, sp.Integer(0)) + scale*v

def clean(vec: dict) -> dict:
    return {p: sp.simplify(v) for p, v in vec.items() if sp.simplify(v) != 0}

def coeff(n: int, m: int | None = None, primes_only: bool = False) -> dict:
    out: dict = {}
    for d in divisors(n):
        if m is None or d <= m:
            add(out, lam(d, primes_only), d2(n//d))
    return clean(out)

for n in range(1, 65):
    rhs = {p: sp.Rational(d2(n)*e, 2) for p, e in factors(n).items()}
    check(f'divisor_log_convolution_{n}', coeff(n) == rhs)

for m in (2, 3, 5, 11):
    Q = 40
    check(f'finite_coefficients_below_cutoff_{m}', all(coeff(n,m)==coeff(n) for n in range(1,m+1)))
    check(f'finite_coefficient_defect_sign_{m}', all(all(v>=0 for v in clean({p:coeff(n).get(p,0)-coeff(n,m).get(p,0) for p in factors(n)}).values()) for n in range(1,Q+1)))
    # An arbitrary finite COMPLEX test is legitimate for the algebra only.
    H = lambda q: sp.Rational(q % 7 - 3, q+1) + sp.I*sp.Rational((2*q) % 5 - 2,q+2)
    raw: dict = {}; grouped: dict = {}; returned: dict = {}
    for n in range(2,m+1):
        for k in range(1,Q//n+1):
            add(raw,lam(n),d2(k)*H(n*k))
    for q in range(1,Q+1):
        add(grouped,coeff(q,m),H(q))
        add(returned,coeff(q),H(q))
        if q>m:
            add(returned,coeff(q,m),H(q))
            add(returned,coeff(q),-H(q))
    check(f'finite_hyperbolic_regroup_{m}',clean(raw)==clean(grouped))
    check(f'finite_upper_index_return_{m}',clean(returned)==clean(grouped))
reject('drop_all_proper_prime_powers',coeff(4,primes_only=True)==coeff(4))
reject('replace_a_m_by_a_above_m',coeff(6,2)==coeff(6))

x,z,u = sp.symbols('x z u')
D = lambda p: sp.expand((-sp.Rational(1,2)+2*x)*p-2*x*sp.diff(p,x))
Bd = lambda p: sp.expand(D(D(p))-p/4)
poly = sp.expand(-4*Bd(Bd(sp.Integer(1))))
expected = -64*x**4+448*x**3-656*x**2+144*x
check('explicit_reflected_gamma_polynomial',poly==expected)
nu = sp.Rational(1,4)-z/2
ratio = sp.expand(sum(sp.Rational(1,2)*c*sp.rf(nu,k[0]) for k,c in sp.Poly(poly,x).terms()))
check('gamma_kernel_mellin_multiplier',sp.factor(ratio+2*(z*z-sp.Rational(1,4))**2)==0)
check('leading_right_exponential_cancelled',sp.Poly(poly,x).coeff_monomial(1)==0)
Dquarter=lambda p:sp.expand((-sp.Rational(1,4)+2*x)*p-2*x*sp.diff(p,x))
poly2=Dquarter(Dquarter(poly))
check('weighted_second_derivative_integrable',sp.Poly(poly2,x).coeff_monomial(1)==0)

A0,A1,A2,B0,B1=sp.symbols('A0 A1 A2 B0 B1', nonzero=True)
residues=[]
for r in range(1,7):
    Z=u**r*(A0+A1*u+A2*u*u)
    G=B0+B1*u
    kappa=1/(A0*B0)**2
    MC=sp.cancel(kappa*G**2*Z**2/u**(2*r))
    LL=sp.cancel(kappa*G**2*Z*sp.diff(Z,u)/u**(2*r))
    res=sp.simplify(sp.limit(u*LL,u,0))
    residues.append(str(res))
    check(f'selected_removable_value_{r}',sp.simplify(MC.subs(u,0))==1)
    check(f'selected_simple_residue_{r}',res==r)
    check(f'complete_derivative_relation_{r}',sp.cancel(LL-sp.diff(MC,u)/2-(r/u-sp.diff(G,u)/G)*MC)==0)
reject('selected_pole_cancels_completely',residues[0]=='0')
reject('multiplicity_always_one',residues[2]=='1')
# Local arithmetic pole s=1 has only a removable contribution: order 4-3=1.
Zpole=-1/u+A0+A1*u
Gpole=u*u*(B0+B1*u)
num=sp.expand(Gpole**2*Zpole*sp.diff(Zpole,u))
check('zeta_pole_cancelled_by_gamma_polynomial',sp.simplify(sp.limit(num/u,u,0))==-B0**2)
check('zeta_pole_not_a_residue',sp.simplify(sp.limit(u*num,u,0))==0)

# Inverse bilateral convention: the LEFT line closes clockwise to the right.
vertices=[(-1,-2),(-1,2),(sp.Rational(1,4),2),(sp.Rational(1,4),-2)]
area=sp.simplify(sum(vertices[i][0]*vertices[(i+1)%4][1]-vertices[(i+1)%4][0]*vertices[i][1] for i in range(4))/2)
check('contour_orientation_clockwise',area<0)
reject('inverse_contour_residue_plus_sign',area>0)
b,zz=sp.symbols('b zz')
check('bilateral_negative_exponential_transform',sp.simplify(-(-1/(zz+b))-1/(zz+b))==0)

realc,imagc=sp.symbols('realc imagc', real=True)
c=realc+sp.I*imagc; cb=realc-sp.I*imagc
check('complex_normalization_selected_value',sp.cancel(cb**2/cb**2)==1)
reject('replace_complex_kappa_by_absolute_square',sp.simplify(cb**2/(c*cb)-1)==0)
a,delta,gamma,h,T=sp.symbols('a delta gamma h T', real=True, positive=True)
check('full_phase_return',sp.expand(2*sp.I*gamma*a+2*(delta-sp.I*gamma)*a)==2*delta*a)
mean=sp.integrate(sp.exp(-a/2),(a,h-T,h))/T
check('averaged_analytic_tail',sp.simplify(mean-2*sp.exp(-(h-T)/2)*(1-sp.exp(-T/2))/T)==0)
signal=sp.integrate(sp.exp(2*delta*a),(a,h-T,h))/T
check('unchanged_signal_normalization',sp.simplify(signal-sp.exp(2*delta*h)*(1-sp.exp(-2*delta*T))/(2*delta*T))==0)
for m in (1,2,5,9):
    partial=sum(q*x**q for q in range(1,m+1))
    tail=x**(m+1)*((m+1)-m*x)/(1-x)**2
    check(f'geometric_tail_identity_{m}',sp.factor(x/(1-x)**2-partial-tail)==0)

# Complete quadratic return, on an abstract rational Hermitian control.
K=sp.Matrix([[2,1+sp.I],[1-sp.I,-3]])
y=sp.Matrix([1+sp.I,2]); e=sp.Matrix([sp.Rational(1,3),sp.I/5])
quad=lambda v:sp.expand((v.conjugate().T*K*v)[0])
cross=sp.expand((y.conjugate().T*K*e)[0]+(e.conjugate().T*K*y)[0])
check('all_mixed_projection_terms',sp.simplify(quad(y+e)-quad(y)-cross-quad(e))==0)
reject('delete_linear_mixed_return',sp.simplify(quad(y+e)-quad(y)-quad(e))==0)

eps=Fraction(1,64); q=67
powers=[1+eps*(Fraction(1,2)-q),Fraction(1,2)+eps*(Fraction(3,2)-q),Fraction(1,2)+eps*(1-q),Fraction(1,2)+eps*(Fraction(1,2)-q)]
for i,p in enumerate(powers):
    check(f'inherited_return_negative_power_{i}',p<0)
result={
  'exact_controls':len(passed),'planted_errors_detected':len(planted),
  'sympy_version':sp.__version__,'selected_residues':residues,
  'b0_polynomial':str(poly),'weighted_derivative_polynomial':str(poly2),
  'contour_signed_area':str(area),'return_powers':[str(v) for v in powers],
  'passed':passed,'planted':planted,
  'scope':'Finite algebra controls only; no Lean, Arb, numerical zeta zero or CCM spectrum; no independent audit.'
}
print(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True))
