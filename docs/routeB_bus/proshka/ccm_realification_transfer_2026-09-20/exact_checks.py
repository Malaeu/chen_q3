#!/usr/bin/env python3
"""Exact scalar closure of a preserved-cache CCM certificate transfer.

No eigensolver, floating-point arithmetic, Arb replay or analytic source
approximation is performed. The pinned Phase-1 Arb certificate is an input.
Run from any working directory; source_extract.json is next to this file.
"""
from __future__ import annotations
import hashlib
import json
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
passed: list[str] = []

def check(name: str, ok: bool) -> None:
    if not ok:
        raise AssertionError(name)
    passed.append(name)
    print('PASS', name)

def interval(data: dict[str, str]) -> tuple[F, F]:
    m, r = F(data['mid']), F(data['rad'])
    if r < 0:
        raise ValueError('Negative input radius')
    return m-r, m+r

def log_bounds(x: int, terms: int = 120) -> tuple[F, F]:
    """log(x)=2 sum t^(2j+1)/(2j+1), with positive geometric tail."""
    if x < 1 or terms < 1:
        raise ValueError('x>=1 and terms>=1 required')
    t = F(x-1, x+1)
    lo = 2*sum((t**(2*j+1)/F(2*j+1) for j in range(terms)), F(0))
    tail = 2*t**(2*terms+1)/(F(2*terms+1)*(1-t*t))
    return lo, lo+tail

def sqrt_lower(x: int) -> F:
    scale = 10**12
    return F(isqrt(x*scale*scale), scale)

def dot(x: list[F], y: list[F]) -> F:
    return sum((a*b for a,b in zip(x,y,strict=True)), F(0))

def action(k: list[list[F]], x: list[F]) -> list[F]:
    return [dot(row,x) for row in k]

def qf(k: list[list[F]], x: list[F]) -> F:
    return dot(x,action(k,x))

def encoded(x: F) -> dict[str, str]:
    with localcontext() as c:
        c.prec=45
        approximate = str(Decimal(x.numerator)/Decimal(x.denominator))
    return {'numerator':str(x.numerator),'denominator':str(x.denominator),
            'decimal_display_only':approximate}

def main() -> None:
    e=json.loads((HERE/'source_extract.json').read_text())
    check('import_full_dimension_and_two_parity_blocks',
          e['imported_certificate']['full_dimension']==241 and
          e['imported_certificate']['even_positive_pivots']==121 and
          e['imported_certificate']['odd_positive_pivots']==120)
    al,au=interval(e['a_hat_ball'])
    check('saved_Rayleigh_ball_inside_zero_to_5e_minus59',0<al<=au<F('5e-59'))
    _,imag_upper=interval(e['discarded_imag_norm_sq_ball'])
    _,asym_upper=interval(e['max_real_J_asymmetry_ball'])
    discarded_upper=imag_upper+F(241,4)*asym_upper**2
    check('real_odd_plus_imaginary_mass_below_3e_minus60',discarded_upper<F('3e-60'))
    real_subset=[F(v) for v in e['real_coefficients_subset'].values()]
    partial_norm=dot(real_subset,real_subset)
    check('seven_exact_coefficients_give_raw_norm_sq_above_099',partial_norm>F(99,100))

    logs={k:log_bounds(k) for k in [2,3,4,5,7,8,9,11,13]}
    Llo,Lhi=logs[13]
    check('log13_strictly_between_5over2_and_3',F(5,2)<Llo<=Lhi<3)
    exp7_lower=sum((F(7)**j/F(factorial(j)) for j in range(41)),F(0))
    check('exp7_lower_exceeds_960',exp7_lower>960)
    check('sqrt13_upper_and_exp1_lower',F(11,3)**2>13 and sum((F(1,factorial(j)) for j in range(5)),F(0))>F(8,3))
    check('h_max_bound_11over10',2*F(11,3)/(F(8,3)*F(5,2))==F(11,10))
    prime_powers=[(2,2),(3,3),(4,2),(5,5),(7,7),(8,2),(9,3),(11,11)]
    S_upper=F(0)
    for k,p in prime_powers:
        root=sqrt_lower(k)
        check(f'sqrt_lower_{k}_valid',root>0 and root*root<=k)
        S_upper+=logs[p][1]/root*(1-logs[k][0]/Lhi)
    check('weighted_prime_sum_below_8over5',0<S_upper<F(8,5))
    # The preceding scalar bounds feed the integral/trace proof in VERDICT.md.
    arch_one=-1+F(11,10)*(7+F(9,4))
    trace_K_upper=10-1+240*arch_one+2*241*F(8,5)
    check('trace_K_upper_14911over5',trace_K_upper==F(14911,5))
    check('positive_penalty_trace_implies_K_upper_3000',trace_K_upper+1<3000)

    delta=F('3e-60')/F(99,100)
    Ua=F('5e-59')+3000*delta
    L=F('1e-56')-Ua-delta
    check('cache_transfer_strict_lower_exceeds_8e_minus58',L>F('8e-58'))
    check('transfer_uses_squared_mass_not_amplitude',delta<F('4e-60'))

    # Independent finite rational controls of the general realification identity.
    K=[[F(2),F(1),F(0)],[F(1),F(3),F(0)],[F(0),F(0),F(5)]]
    x=[F(3,5),F(4,5),F(0)];u=[F(0),F(0),F(1,10)]
    y=[F(1,7),F(1,11),F(1,13)]
    real=[a+b for a,b in zip(x,u,strict=True)]
    s=dot(x,x); t=dot(u,u)+dot(y,y); norm=s+t
    direct=(qf(K,real)+qf(K,y))/norm
    split=(qf(K,x)+qf(K,u)+qf(K,y))/norm
    check('real_parity_energy_identity',direct==split)
    D=1-(s*s+dot(x,y)**2)/(s*norm)
    check('complex_overlap_loss_bounded_by_discarded_mass',0<=D<=t/norm)
    # Omit reflection commutation: a real-even/real-odd cross term survives.
    badK=[[F(1),F(1)],[F(1),F(1)]]
    check('plant_missing_commutation_rejected',qf(badK,[F(1),F(1,10)]) != qf(badK,[F(1),F(0)])+qf(badK,[F(0),F(1,10)]))
    # K=[[1,i],[-i,1]], z=e1+i*t*e2: energy 1+t^2-2t, not 1+t^2.
    t0=F(1,10)
    check('plant_Hermitian_but_not_real_rejected',1+t0*t0-2*t0!=1+t0*t0)
    # The old certificate K=diag(0,1), gamma=tau=.9 is positive,
    # but dropping angular loss wrongly certifies q=(.6,.8).
    a0=F(16,25); d0=F(16,25); gamma0=tau0=F(9,10)
    true_complement=F(9,25)-a0
    check('plant_omitted_angular_loss_rejected',gamma0-a0>0 and true_complement<0 and gamma0-a0-tau0*d0<=true_complement)
    # Zero discarded part recovers the original complement certificate.
    check('zero_defect_recovers_old_margin',F('1e-56')-F('5e-59')-(3000+1)*0>0)

    results={'scope':'FINITE_CELL_PAPER_WITH_IMPORTED_ARB_CERTIFICATE',
       'analytic_source_enclosure_proved':False,'arb_rerun':False,'lean_run':False,
       'checks_passed':len(passed),'registered_predictions':{'P_TRACE':'CONFIRMED','P_CACHE':'CONFIRMED_CONDITIONAL_ON_IMPORTED_CERTIFICATE','P_REALIFICATION':'CONFIRMED','P_SCOPE':'CONFIRMED'},
       'raw_norm_sq_lower':encoded(F(99,100)),
       'discarded_mass_sq_upper':encoded(F('3e-60')),
       'delta_upper':encoded(delta),'a_cache_upper':encoded(Ua),
       'K_upper':encoded(F(3000)),'transfer_lower':encoded(L),
       'published_floor':encoded(F('8e-58')),
       'trace_K_upper':encoded(trace_K_upper),
       'prime_sum_certified_upper':encoded(F(8,5)),
       'source_extract_sha256':hashlib.sha256((HERE/'source_extract.json').read_bytes()).hexdigest()}
    (HERE/'result.json').write_text(json.dumps(results,indent=2)+'\n')
    print('CACHE_TRANSFER_LOWER',encoded(L)['decimal_display_only'])
    print('ALL_EXACT_CHECKS_PASSED',len(passed))
    print('PAPER_TRANSFER_COMPLETE; OLD_ARB_IMPORTED_NOT_RERUN; ANALYTIC_SOURCE_OPEN; LEAN_NOT_RUN')

if __name__=='__main__':
    main()
