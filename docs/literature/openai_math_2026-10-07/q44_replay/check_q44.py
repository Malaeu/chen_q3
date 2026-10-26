#!/usr/bin/env python3
"""Sensitive exact algebra checks only. No numerical zeta zero or CCM spectrum.
Requires the already available SymPy; no installation is performed.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sympy as s

checks: list[str] = []
planted: list[str] = []

def zero(name: str, expression: s.Expr) -> None:
    value = s.simplify(expression)
    if value != 0:
        raise AssertionError(f'{name}: {value}')
    checks.append(name)

def rejects(name: str, wrong_residual: s.Expr) -> None:
    if s.simplify(wrong_residual) == 0:
        raise AssertionError(f'Planted error was not detected: {name}')
    planted.append(name)

def run() -> dict:
    t = s.symbols('t')
    a0, a1, a2, e0, e1 = s.symbols('a0 a1 a2 e0 e1', nonzero=True)
    for r in (1, 2, 3):
        A = (-t)**r * (a0 + a1*t + a2*t**2)
        E = e0 + e1*t
        cn = (-1)**r * s.diff(A*E, t, r).subs(t, 0)/s.factorial(r)
        zero(f'normalization_order_{r}', cn - a0*e0)
        gn = s.cancel(A*E / (cn * (-t)**r))
        g = s.cancel(A / (a0 * (-t)**r))
        zero(f'normalized_value_order_{r}', gn.subs(t, 0) - 1)
        zero(f'radical_difference_value_order_{r}', (gn-g).subs(t, 0))
    rejects('omit_separate_E_normalization', e0 - 1)

    x, y, u, v = s.symbols('x y u v', real=True)
    cw, Ew = x+s.I*y, u+s.I*v
    for r in (1, 2, 3):
        cv = (-1)**r*s.conjugate(cw)
        kappaE = (-1)**r/(s.conjugate(cw*Ew)*cv*s.conjugate(Ew))
        zero(f'complex_kappa_order_{r}', kappaE - 1/s.conjugate(cw*Ew)**2)
    rejects('replace_complex_normalizer_by_modulus',
            (s.conjugate(Ew)**2/(Ew*s.conjugate(Ew))-1).subs({u:1,v:1}))

    b, w, z = s.symbols('b w z')
    F = s.Function('F')
    derivative = s.diff(s.exp(-w*b)*F(z-b), b)
    zero('finite_translation_derivative_sign',
         derivative+s.exp(-w*b)*(w*F(z-b)+s.diff(F(z-b), z)))

    H=s.Matrix([[2,1+s.I],[1-s.I,-3]])
    f=s.Matrix([1+s.I, s.Rational(1,2)-s.I])
    q=s.Matrix([2-s.I, -1+2*s.I])
    form=lambda a,b:(s.conjugate(a).T*H*b)[0]
    delta=form(f+q,f+q)-form(f,f)
    cross=form(f,q)+form(q,f)
    zero('full_complex_variation', delta-cross-form(q,q))
    rejects('drop_quadratic_variation', delta-cross)

    zz=s.symbols('zz')
    contact=(zz**2-s.Rational(1,4))**2
    # These are the exact principal parts of d(z), not an approximation to d.
    pole_half=1/(zz-s.Rational(1,2))
    pole_52=1/(zz-s.Rational(5,2))
    zero('first_arch_pole_removed', s.limit((zz-s.Rational(1,2))*contact*pole_half,zz,s.Rational(1,2)))
    zero('first_arch_value_zero', s.limit(contact*pole_half,zz,s.Rational(1,2)))
    zero('next_arch_residue',s.limit((zz-s.Rational(5,2))*contact*pole_52,zz,s.Rational(5,2))-36)
    rejects('drop_contact_factor',s.limit((zz-s.Rational(1,2))*pole_half,zz,s.Rational(1,2)))
    rejects('claim_next_pole_removed',s.limit((zz-s.Rational(5,2))*contact*pole_52,zz,s.Rational(5,2)))
    xi3=s.Rational(1,2)*3*2*s.pi**(-s.Rational(3,2))*s.gamma(s.Rational(3,2))*s.zeta(3)
    zero('actual_A_at_five_halves',-24*xi3+36*s.zeta(3)/s.pi)

    aa=s.symbols('aa', positive=True)
    model=2*aa/(aa**2-zz**2) # transform of exp(-aa |y|)
    residue=s.limit((zz-aa)*model,zz,aa)
    zero('right_shift_orientation',-residue-1)
    rejects('wrong_right_shift_residue_sign',residue-1)

    lam,U=s.symbols('lam U', nonzero=True)
    for n in (2,4,6):
        partial=(1-s.exp(-lam*U)*sum((lam*U)**j/s.factorial(j) for j in range(n)))/lam**n
        zero(f'incomplete_gamma_derivative_{n}',s.diff(partial,U)-U**(n-1)*s.exp(-lam*U)/s.factorial(n-1))
        zero(f'incomplete_gamma_lower_edge_{n}',partial.subs(U,0))
    L=s.symbols('L',positive=True)
    yh=L-2*s.log(L); band=s.Rational(3,2)*s.log(L)
    zero('seam_lower_at_h',L-band-yh-s.log(L)/2)
    zero('seam_upper_at_h',L+band-yh-7*s.log(L)/2)

    eps,p,extra=s.symbols('eps p extra',positive=True)
    order=(2*p+1)/eps+2+extra
    zero('moving_profile_first_return_exponent',
         2*p+1+eps*(s.Rational(1,2)-order)+eps*(s.Rational(3,2)+extra))
    zero('moving_profile_derivative_return_exponent',
         2*p+s.Rational(1,2)+eps*(s.Rational(3,2)-order)+s.Rational(1,2)+eps*(s.Rational(1,2)+extra))
    zero('moving_profile_jump_return_exponent',
         2*p+s.Rational(1,2)+eps*(1-order)+s.Rational(1,2)+eps*(1+extra))
    return dict(scope='EXACT_LOCAL_ALGEBRA_NOT_AN_ASYMPTOTIC_OR_SPECTRAL_CERTIFICATE',
                exact_checks=checks, exact_check_count=len(checks),
                planted_errors_detected=planted, planted_error_count=len(planted),
                hypothetical_zero_numerically_assigned=False,
                production_CCM_spectrum=False, lean=False, arb=False)

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,default=Path('check_q44_results.json'))
    args=parser.parse_args()
    result=run()
    text=json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+'\n'
    args.out.write_text(text,encoding='utf-8')
    print(text,end='')

if __name__=='__main__':
    main()
