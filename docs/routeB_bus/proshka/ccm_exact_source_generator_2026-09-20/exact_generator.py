#!/usr/bin/env python3
"""Exact algebraic source-to-coefficient generator, not a rounded-cache certificate.

Symbolic functions return exact expressions for FINITE polynomial/Ferrers inputs.
An analytic prolate source uses the infinite outer Ferrers sum proved in VERDICT.md.
Truncating that sum is NOT silently certified. No eigenvalue solver is used.
Run this file to execute exact controls and separately labelled numerical diagnostics.
"""
from __future__ import annotations

import json
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Sequence

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
T = sp.Symbol('t', real=True)


def _check(m: int, n: int) -> None:
    if not isinstance(m, int) or isinstance(m, bool) or m < 2:
        raise ValueError('m must be an integer >= 2')
    if not isinstance(n, int) or isinstance(n, bool):
        raise ValueError('n must be an integer Fourier mode')


def monomial_kernel(m: int, n: int, degree: int) -> sp.Expr:
    """Exact <V_n, E_star[(x/sqrt(m))**degree]> for the compact source.

    Endpoint values do not affect these integrals. Degree may be odd.
    All powers have positive real bases; no branch convention is hidden.
    """
    _check(m, n)
    if not isinstance(degree, int) or degree < 0:
        raise ValueError('degree must be a nonnegative integer')
    s = sp.Rational(1, 2) - 2 * sp.pi * sp.I * n / sp.log(m)
    harmonic = sum(sp.Integer(k)**(-s) for k in range(1, m + 1))
    power_sum = sum(sp.Integer(k)**degree for k in range(1, m + 1))
    numerator = sp.sqrt(m) * harmonic - sp.Rational(1, m**degree) * power_sum
    return sp.Integer(m)**(-sp.Rational(1, 4)) / sp.sqrt(sp.log(m)) * numerator / (s + degree)


def polynomial_coefficient(m: int, n: int, polynomial: sp.Expr) -> sp.Expr:
    """Exact finite polynomial coefficient. Input is H(t)=h(sqrt(m)*t)."""
    p = sp.Poly(polynomial, T)
    return sp.Add(*(coefficient * monomial_kernel(m, n, degree[0])
                    for degree, coefficient in p.terms()))


def ferrers_column(m: int, n: int, j: int) -> sp.Expr:
    """Source convention: (-1)**j * a[j] * P_(2j)(t)."""
    if not isinstance(j, int) or j < 0:
        raise ValueError('j must be nonnegative')
    return (-1)**j * polynomial_coefficient(m, n, sp.legendre(2*j, T))


def zero_mass_packet_row(m: int, N: int, a0: Sequence[sp.Expr],
                         a4: Sequence[sp.Expr]) -> tuple[list[sp.Expr], sp.Expr]:
    """Exact finite Ferrers-source analogue of the 0/4 packet.

    Returns the UNNORMALIZED finite Fourier row and its exact Euclidean norm.
    For actual prolate modes use the infinite series identity, not zero padding.
    No claim that arbitrary finite a0/a4 are eigenfunctions is made.
    """
    _check(m, 0)
    if not isinstance(N, int) or N < 0 or not a0 or not a4:
        raise ValueError('N >= 0 and two nonempty Ferrers rows required')
    J = max(len(a0), len(a4))
    u = [sp.sympify(a0[j]) if j < len(a0) else sp.S.Zero for j in range(J)]
    v = [sp.sympify(a4[j]) if j < len(a4) else sp.S.Zero for j in range(J)]
    b = [sp.expand(v[0]*u[j] - u[0]*v[j]) for j in range(J)]
    assert b[0] == 0
    row = [sp.Add(*(b[j]*ferrers_column(m,n,j) for j in range(J) if b[j] != 0))
           for n in range(-N, N+1)]
    norm = sp.sqrt(sp.Add(*(sp.conjugate(z)*z for z in row)))
    if norm == 0:
        raise ValueError('projected packet is zero; normalized row undefined')
    return row, norm


def even_taylor_coefficients(theta: sp.Expr, c_squared: sp.Expr,
                             terms: int) -> list[sp.Expr]:
    """Formal local solution f(0)=1, f'(0)=0 of the angular prolate ODE.

    Outputs coefficients of 1,t^2,... . Endpoint regularity and the 0/4 branch
    selection are additional spectral conditions, not consequences of recurrence.
    """
    if terms < 1:
        raise ValueError('at least one term required')
    out = [sp.S.One]
    for j in range(terms-1):
        previous = out[j-1] if j else sp.S.Zero
        out.append(sp.expand(((2*j*(2*j+1)-theta)*out[j] + c_squared*previous)
                             / ((2*j+2)*(2*j+1))))
    return out


def _cmul(a: tuple[Fraction,Fraction], b: tuple[Fraction,Fraction]):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


def _phase_witness(z):
    c = (z[0][0], -z[0][1])
    return _cmul(_cmul(z[1], z[-1]), _cmul(c,c))[1]


def _mp_kernel(m, n, degree):
    L=mp.log(m); s=mp.mpf('0.5')-2j*mp.pi*n/L
    return mp.mpf(m)**(-mp.mpf('0.25'))/mp.sqrt(L) * mp.fsum(
        (mp.sqrt(m)*mp.mpf(k)**(-s)-(mp.mpf(k)/m)**degree)/(s+degree)
        for k in range(1,m+1))


def _mp_direct(m,n,coefficients):
    """Independent original breakpoint integral, for diagnostics only."""
    L=mp.log(m); lam=mp.sqrt(m)
    def H(t): return mp.fsum(a*t**d for d,a in coefficients.items())
    total=mp.mpc(0)
    for j in range(1,m):
        lo=mp.log(mp.mpf(m)/(j+1)); hi=mp.log(mp.mpf(m)/j)
        def integrand(x):
            e=mp.exp(x)
            return mp.sqrt(e/lam)*mp.fsum(H(k*e/m) for k in range(1,j+1))*mp.exp(-2j*mp.pi*n*x/L)/mp.sqrt(L)
        total += mp.quad(integrand,[lo,hi])
    return total


def main() -> None:
    if not (ROOT/'registration.json').exists():
        raise RuntimeError('preregister before running controls')
    checks=[]
    def check(name, statement):
        if not bool(statement): raise AssertionError(name)
        checks.append(name);print('EXACT_PASS',name)
    data=json.loads((ROOT/'cache_three_modes.json').read_text())
    z={r['n']:(Fraction(r['re']),Fraction(r['im'])) for r in data['coefficients']}
    chi=_phase_witness(z)
    check('cache_central_imaginary_not_zero',z[0][1]!=0)
    check('cache_no_common_phase_real_source',-Fraction(3,10**112)<chi<-Fraction(2,10**112))
    control={0:(Fraction(2),Fraction(0)),1:(Fraction(3),Fraction(5)), -1:(Fraction(3),Fraction(-5))}
    phase=(Fraction(3,5),Fraction(4,5))
    rotated={k:_cmul(v,phase) for k,v in control.items()}
    check('phase_rotated_real_source_control_zero',_phase_witness(rotated)==0)
    mutated=dict(rotated); mutated[1]=(mutated[1][0],mutated[1][1]+Fraction(1,10**120))
    check('planted_conjugacy_violation_detected',_phase_witness(mutated)!=0)
    x,s=sp.symbols('x s'); d=sp.Symbol('d',integer=True,nonnegative=True)
    check('primitive_identity',sp.simplify(sp.diff(sp.exp((s+d)*x)/(s+d),x)-sp.exp((s+d)*x))==0)
    # The support-aware numerator vanishes at its apparent s=-d pole.
    for m in (2,3,5):
        for degree in (0,2,4):
            num=sum((sp.Rational(m,k)**s-sp.Rational(k,m)**degree) for k in range(1,m+1))
            check(f'removable_{m}_{degree}',sp.simplify(num.subs(s,-degree))==0)
    theta,c2=sp.symbols('theta c2', real=True)
    co=even_taylor_coefficients(theta,c2,5)
    poly=sum(v*T**(2*j) for j,v in enumerate(co))
    ode=sp.Poly(sp.expand(-sp.diff((1-T*T)*sp.diff(poly,T),T)+c2*T*T*poly-theta*poly),T)
    check('taylor_recurrence_low_orders',all(ode.nth(2*j)==0 for j in range(4)))
    check('finite_polynomial_top_residual',sp.simplify(ode.nth(10)-c2*co[-1])==0)
    a,b,A,B=sp.symbols('a b A B',real=True)
    F0=a+(A*T*T); F4=b+(B*T*T)
    J0=sp.integrate(F0,(T,-1,1)); J4=sp.integrate(F4,(T,-1,1))
    check('zero_mass_packet_identity',sp.simplify(sp.integrate(J4*F0-J0*F4,(T,-1,1)))==0)
    rows0=[sp.Rational(2),sp.Rational(3),sp.Rational(5)]
    rows4=[sp.Rational(7),sp.Rational(11),sp.Rational(13)]
    ff0=sum((-1)**j*rows0[j]*sp.legendre(2*j,T) for j in range(3))
    ff4=sum((-1)**j*rows4[j]*sp.legendre(2*j,T) for j in range(3))
    check('Ferrers_integral_is_2_a0',sp.integrate(ff0,(T,-1,1))==2*rows0[0])
    packet=rows4[0]*ff0-rows0[0]*ff4
    check('Ferrers_packet_zero_mode_cancels',sp.integrate(packet,(T,-1,1))==0)
    n0,n4,lam,den=sp.symbols('n0 n4 lam den',positive=True)
    original=(2*lam*rows4[0]/n4*ff0/n0-2*lam*rows0[0]/n0*ff4/n4)/den
    check('individual_mode_norms_cancel_projectively',sp.simplify(original-2*lam/(n0*n4*den)*packet)==0)
    # Exercise the public symbolic generator against a different integral variable.
    u=sp.Symbol('u',positive=True)
    hpoly=1+sp.Rational(2,3)*T**2-sp.Rational(5,7)*T**4
    direct_exact=sum(sp.integrate(hpoly.subs(T,sp.Rational(k,2)*u)/sp.sqrt(u),
                                  (u,sp.Rational(1,2),sp.Rational(2,k)))
                     for k in range(1,5))/sp.sqrt(sp.log(4))
    check('public_generator_exact_original_u_integral',
          sp.simplify(polynomial_coefficient(4,0,hpoly)-direct_exact)==0)
    # Exact source basis phase and sign is tested independently below.
    mp.mp.dps=55
    terms={0:mp.mpf(1),2:mp.mpf(2)/3,4:-mp.mpf(5)/7}
    diagnostic=[]
    for m in (2,3,5):
        for n in (-2,-1,0,1,2):
            closed=mp.fsum(a*_mp_kernel(m,n,d) for d,a in terms.items())
            direct=_mp_direct(m,n,terms)
            error=abs(closed-direct)
            if error>=mp.mpf('1e-45'):raise AssertionError((m,n,error))
            diagnostic.append({'m':m,'n':n,'absolute_discrepancy':mp.nstr(error,10)})
    good=mp.fsum(a*_mp_kernel(3,1,d) for d,a in terms.items())
    wrong=mp.fsum(a*_mp_kernel(3,-1,d) for d,a in terms.items())
    if abs(good-wrong)<mp.mpf('1e-10'):raise AssertionError('phase mutation not detected')
    original=_mp_direct(3,0,{0:mp.mpf(1)})
    # Incorrectly retaining all m summands across the entire window.
    wrong_support=3*mp.mpf(3)**(-mp.mpf('0.25'))/mp.sqrt(mp.log(3))*2*(mp.sqrt(3)-1)
    if abs(original-wrong_support)<mp.mpf('0.1'):
        raise AssertionError('support mutation not detected')
    print('DIAGNOSTIC_PASS 15 breakpoint quadratures; wrong-phase and wrong-support controls; NOT_INTERVAL_PROOF')
    with localcontext() as dc:
        dc.prec=40
        display=str(Decimal(chi.numerator)/Decimal(chi.denominator))
    result={'exact_checks_passed':len(checks),'exact_check_names':checks,
      'phase_invariant':{'numerator':str(chi.numerator),'denominator':str(chi.denominator),
       'display_only':display,'strict_interval':['-3e-112','-2e-112']},
      'quadrature_diagnostics_not_proof':diagnostic,
      'analytic_cache_equality':False,'new_project_positivity':False,'lean_run':False,
      'prediction_fates':{'P_GEN':'CONFIRMED_FOR_PAPER_IDENTITY_AND_CONTROLS',
        'P_PHASE':'CONFIRMED_EXACT_RATIONAL_WITNESS','P_TRUNC':'CONFIRMED_TOP_DEGREE_IDENTITY',
        'P_NORMALIZATION':'CONFIRMED_BY_PAPER_ORTHOGONAL_PROJECTION_IDENTITY'}}
    (ROOT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PHASE_INVARIANT',display)
    print('EXACT_CHECKS',len(checks))
    print('DONE; GENERATOR_IDENTITY_PAPER; CACHE_NOT_EQUAL_SOURCE; NO_LEAN; NO_RH')


if __name__=='__main__':
    main()
