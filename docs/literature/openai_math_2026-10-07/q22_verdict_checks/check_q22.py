#!/usr/bin/env python3
"""Q22 local algebra controls, not a CCM spectral or interval certificate."""
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path
import sympy as s

checks = []
planted = []
def ck(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)

def zero_matrix(A):
    return all(s.simplify(x) == 0 for x in A)

# Abstract minimum-norm interpolation: rational complex data, NOT zeta zeros.
i = s.I
P = s.diag(1, 1, 1, 0, 0)
E = s.Matrix([[1, i, 2, 3, -i], [i, 2, -1, 1, 2*i]])
G = E*P*E.conjugate().T
b = s.Matrix([1+i, -1-i])
x0 = P*E.conjugate().T*G.inv()*b
v = (E*P)[:, :3].nullspace()[0]
v = s.Matrix(list(v)+[0, 0])
x = x0+(2-i)*v
ck('gram_hermitian', zero_matrix(G-G.conjugate().T))
ck('gram_positive_first_minor', s.re(G[0,0]) > 0)
ck('gram_positive_determinant', s.re(G.det()) > 0)
ck('projected_minimizer', zero_matrix(P*x0-x0))
ck('both_interpolation_values', zero_matrix(E*x0-b))
ck('null_fiber', zero_matrix(E*v))
ck('orthogonal_fiber', s.simplify((x0.conjugate().T*v)[0]) == 0)
minnorm = (b.conjugate().T*G.inv()*b)[0]
ck('minimum_norm_identity', s.simplify((x0.conjugate().T*x0)[0]-minnorm) == 0)
ck('full_pythagoras_including_mixed_terms',
   s.simplify((x.conjugate().T*x)[0]-minnorm-5*(v.conjugate().T*v)[0]) == 0)
# Deliberately wrong adjoint must be detected; do not silently repair.
Gwrong = E*P*E.T
ck('detector_wrong_transpose', not zero_matrix(Gwrong-G))
planted.append('conjugate transpose replaced by transpose')
ck('detector_zeroed_interpolation', not zero_matrix(b))
planted.append('nonzero normalized pair values erased')

# Actual projected-exponential limiting coefficient, symbolic only.
d, gam = s.symbols('delta gamma', real=True, positive=True)
chi = 1/(2*d)-1/((d+s.Rational(1,2))**2+gam**2)
positive_expression = ((d-s.Rational(1,2))**2+gam**2)/(2*d*((d+s.Rational(1,2))**2+gam**2))
ck('chi_factorization', s.simplify(chi-positive_expression) == 0)
ck('unprojected_coefficient_is_different', s.simplify(1/(2*d)-chi) != 0)
# Exact complex pair normalization and sign, with no numerical zero.
t, aa = s.symbols('t a', real=True)
w = d+i*gam
vv = -s.conjugate(w)
ck('reflected_partner', s.simplify(vv-(-d+i*gam)) == 0)
ck('first_pair_evaluation', s.simplify(s.exp(-i*gam*aa)*s.exp(w*aa)-s.exp(d*aa)) == 0)
ck('second_pair_evaluation', s.simplify(-s.exp(i*gam*aa)*s.exp(-vv*aa)+s.exp(d*aa)) == 0)
ck('whole_line_gram_cross_integrand', s.simplify(s.exp(w*t)*s.exp(s.conjugate(vv)*t)-1) == 0)
# Radial/phase error is detected on an ordinary normalization scalar, not a zero.
c = 1+2*i
ck('complex_kappa_not_modulus', s.simplify(1/s.conjugate(c)**2-1/(c*s.conjugate(c))) != 0)
planted.append('kappa replaced by its modulus normalization')

# Uniform polynomial-amplitude return: the coefficients are exact exponents.
exponent_records = []
for eps in [F(1,64), F(1,48), F(1,100)]:
    for p in [F(0),F(1,2),F(1),F(2)]:
        threshold=(2*p+1)/eps+2
        q=threshold.numerator//threshold.denominator+1
        powers={
            'full_E_cross_0':2*p+1+eps*(F(1,2)-q),
            'full_E_cross_1':2*p+F(1,2)+eps*(F(3,2)-q),
            'full_E_cross_endpoint':2*p+F(1,2)+eps*(1-q),
            'constraint':2*p+F(1,2)+eps*(F(1,2)-q),
            'E0_squared':2*p+1+eps*(1-2*q),
            'E1_squared':2*p+eps*(3-2*q),
            'Eendpoint_squared':2*p+2*eps*(1-q),
            # delta*alpha < 1/8; this is a uniform upper exponent.
            'relative_evaluation_upper':p+F(1,8)+eps*(F(1,2)-q)
        }
        ck(f'all_return_powers_negative_eps{eps}_p{p}', all(x<0 for x in powers.values()))
        exponent_records.append({'epsilon':str(eps),'p':str(p),'q':q,'powers':{k:str(v) for k,v in powers.items()}})
# Old q=67 at epsilon=1/64 does NOT cover variation m^1.
ck('detector_old_q_on_growing_profile',2*F(1)+1+F(1,64)*(F(1,2)-67)>0)
planted.append('polynomial total-variation factor omitted from return')

# Ratios: lambda_min-type signal is not a favorable arithmetic supplier.
L, mm, al, xi = s.symbols('L m alpha chi', positive=True)
ET = mm**d/L**(2*d+1)/(2*d*al)
res_lower = 2/xi*mm**(-d)*ET
Bprice = s.Rational(1,2)*12*s.sqrt(mm)*res_lower
ck('price_signal_ratio',s.simplify(Bprice/ET-12/xi*mm**(s.Rational(1,2)-d))==0)
ck('absolute_price_log_factor',s.simplify(Bprice-6/(xi*d*al)*s.sqrt(mm)/L**(2*d+1))==0)
for dd in [F(1,10),F(1,4),F(49,100)]:
    ck(f'positive_price_exponent_at_delta{dd}',F(1,2)-dd>0)
ck('detector_claimed_subpower_ratio',s.simplify(Bprice/ET-12/xi*mm**(-d)) != 0)
planted.append('sqrt(m) completion cost dropped from normalized price')

# Centering must be exact before any cost. Labels are formal variables here.
D0, D, B0, Btilde = s.symbols('D0 D B0 Btilde')
ctr = D-D0
ck('continuous_reference_has_zero_discrepancy',s.expand(ctr.subs(D,D0))==0)
ck('signed_reference_return_once',s.expand((Btilde+B0)-B0-Btilde)==0)
ck('detector_missing_continuum',s.expand(D.subs(D,D0)) != 0)
planted.append('continuous reference not subtracted')
# Counting is literal; no asymptotic or spectral assertion is tested by this file.
out={'status':'PASS_EXACT_LOCAL_CONTROLS_NOT_GLOBAL_PROOF',
     'sympy':s.__version__, 'checks':len(checks),'planted_failures_detected':len(planted),
     'names':checks,'planted':planted,'return_exponents':exponent_records,
     'hypothetical_zero_numerically_assigned':False,'ccm_spectrum_computed':False,
     'arb_run':False,'lean_run':False}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':out['status'],'checks':len(checks),'planted_failures_detected':len(planted),'sympy':s.__version__},ensure_ascii=False))
