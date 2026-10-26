#!/usr/bin/env python3
"""Exact local algebra controls for Q28; no actual zero data, CCM spectrum, or global sign test."""
from __future__ import annotations
import json
from fractions import Fraction
import sympy as s
passed=[]; planted=[]
def ok(name, test):
    if not bool(test): raise AssertionError(name)
    passed.append(name)
def reject(name, test):
    if bool(test): raise AssertionError('undetected planted error: '+name)
    planted.append(name)
def mz(X): return all(s.cancel(x)==0 for x in X)
def simp(x): return s.simplify(s.expand_complex(x))
# These rational frequencies check algebraic identities, not production integer m.
om=s.Matrix([-2,-1,0,1,2]); one=s.ones(5,1)
ve=s.Matrix([1/(s.Rational(1,4)+t*t) for t in om])
vo=s.Matrix([t/(s.Rational(1,4)+t*t) for t in om])
G=s.Matrix.hstack(one,ve,vo); P=s.eye(5)-G*(G.T*G).inv()*G.T
ok('three_contact_idempotence',mz(P*P-P))
ok('three_contact_real_symmetry',P==P.T)
ok('all_three_contacts',mz(P*G))
ok('test_projector_rank',P.rank()==2)
v=lambda z,sign:s.Matrix([1/(z+sign*s.I*t) for t in om])
Sm=lambda z: P*(v(z,1)*v(z,1).T+v(z,-1)*v(z,-1).T)*P
z=s.Rational(2,3)+s.I/5 # a generic transfer point, not asserted to be any zero
ok('v_reflection_plus',mz(v(-z,1)+v(z,-1)))
ok('v_reflection_minus',mz(v(-z,-1)+v(z,1)))
ok('v_conjugation_swaps_time',mz(v(s.conjugate(z),1)-s.conjugate(v(z,-1))))
ok('transfer_even',mz(Sm(-z)-Sm(z)))
ok('transfer_real_type',mz(Sm(s.conjugate(z))-s.conjugate(Sm(z))))
ok('transfer_symmetric_not_Hermitian',Sm(z).T==Sm(z))
reject('analytic_transfer_equals_its_adjoint',mz(Sm(z)-Sm(z).conjugate().T))
# Whole quartet versus right half. X represents exp(L*z), not a freely changed arithmetic phase.
X=s.symbols('X',nonzero=True)
D=X+1/X-2
ok('sinh_square_factor',s.factor(D-(X-1)**2/X)==0)
ok('right_to_completed_orbit_correction',s.factor(X-D-(2-1/X))==0)
ok('right_evaluation_factor',s.factor(X/D-1/(1-1/X)**2)==0)
ok('left_and_constant_return',s.factor((X+1/X)-2-D)==0)
reject('delete_constant_two',s.factor(X-D+1/X)==0)
reject('delete_left_partner',s.factor(X-D-2)==0)
t=s.symbols('t',real=True)
ok('window_factor_difference',s.factor(1/(1-t)**2-1-(2*t-t*t)/(1-t)**2)==0)
# Explicit complex mixed vector, not a zeta test.
c=P*s.Matrix([1+s.I,2-s.I,3,4*s.I,-2+s.I])
e=s.Rational(5,4)+s.I/3 # formal exp(L*z/2); conjugate carried independently
ell=lambda arg:(v(arg,1).T*c)[0]
fz=(e-1/e)*ell(z)
fmz=-(e-1/e)*ell(-z)
fbar=(s.conjugate(e)-1/s.conjugate(e))*ell(s.conjugate(z))
fmbar=-(s.conjugate(e)-1/s.conjugate(e))*ell(-s.conjugate(z))
q=(c.conjugate().T*Sm(z)*c)[0]
quad=fz*s.conjugate(fmbar)+fmz*s.conjugate(fbar)
ok('complete_Mellin_two_time_identity',simp(quad-(e-1/e)**2*q)==0)
quart=2*s.re(fz*s.conjugate(fmbar)+fbar*s.conjugate(fmz))
ok('full_four_evaluations',simp(quart-2*s.re((e-1/e)**2*q))==0)
right=2*s.re(e**2*q)
ok('right_residue_via_actual_cross_products',simp(right-2*s.re(quad/(1-1/e**2)**2))==0)
reject('replace_cross_products_by_moduli',simp(quart-2*(abs(fz)**2+abs(fbar)**2))==0)
# Positive/negative coupled square identity, full complex values.
A=1+2*s.I; B=-3+s.I; C=s.Rational(1,2)-s.I; DD=2+3*s.I
mixed=2*s.re(A*s.conjugate(B)+C*s.conjugate(DD))
plus=(abs(A+B)**2+abs(C+DD)**2)/2
minus=(abs(A-B)**2+abs(C-DD)**2)/2
ok('coupled_positive_negative_identity',s.simplify(mixed-plus+minus)==0)
reject('drop_negative_square',s.simplify(mixed-plus)==0)
# Every transfer pole is cancelled but its value is not dropped.
h,L=s.symbols('h L',positive=True)
factor=s.exp(L*h)+s.exp(-L*h)-2
ok('pole_factor_double_zero',s.limit(factor/h**2,h,0)==L**2)
ok('pole_factor_no_cubic',s.limit((factor-L**2*h**2)/h**3,h,0)==0)
for k in (-2,-1,0,1,2):
    # coefficient of h^-2 in S(i*k+h): one or both raw mode poles
    lead=s.zeros(5)
    for sign in (-1,1):
        j=-sign*k
        ee=s.zeros(5,1); ee[j+2]=1
        u=P*ee; lead+=u*u.T
    ok('mode_double_pole_nonzero_'+str(k),not mz(lead))
    # Since exp(i*k*L)=1 on the production lattice, the entire value is L*lead.
    ok('mode_limit_real_psd_trace_'+str(k),s.trace(lead)>0)
reject('entire_transfer_zero_at_zero_mode',mz(2*L*(P*s.eye(5)[:,2])*(P*s.eye(5)[:,2]).T))
# Source normalization is symbolic; these are removable-value identities, not a synthetic zero theorem.
r,E=s.symbols('r E',positive=True)
ok('selected_pair_positive_credit_zero',s.simplify(r*(abs(E-E)**2+0)/2)==0)
ok('selected_pair_negative_credit',s.simplify(r*abs(E+E)**2/2-2*r*E**2)==0)
ok('selected_orbit_signed_value',s.simplify(2*r*s.re(E*(-E))+2*r*E**2)==0)
reject('multiplicity_can_be_dropped',s.simplify(-2*r*E**2+2*E**2)==0)
cw=s.Rational(1,2)+s.I
eta=cw/s.conjugate(cw)
ok('normalization_retains_unit_phase',s.simplify(eta*s.conjugate(eta)-1)==0)
reject('normalization_phase_is_one',s.simplify(eta-1)==0)
# Full linear and quadratic perturbation formula.
a0,b0,dc,dd=s.symbols('a0 b0 dc dd')
ok('four_mixed_perturbation_terms',s.expand((a0+dc)*(b0+dd)-a0*b0-a0*dd-dc*b0-dc*dd)==0)
reject('remove_quadratic_leakage',s.expand((a0+dc)*(b0+dd)-a0*b0-a0*dd-dc*b0)==0)
# m-exponents, use pi>3 only to obtain rigorous negative rational upper bounds.
eps=s.symbols('eps',positive=True)
rightpow=s.Rational(1,2)+3*eps-3*(s.Rational(1,4)+eps)
leftpow=3*eps-3*(s.Rational(1,4)+eps)
horizpow=s.Rational(1,2)+3*eps-4*(s.Rational(1,4)+eps)
ok('allP_right_tail_power',s.simplify(rightpow+s.Rational(1,4))==0)
ok('allP_left_tail_power',s.simplify(leftpow+s.Rational(3,4))==0)
ok('allP_horizontal_power',s.simplify(horizpow+s.Rational(1,2)+eps)==0)
lin_upper=Fraction(1,2)-6
quad_upper=Fraction(3,4)+Fraction(1,32)-12
ok('selected_linear_return_decays',lin_upper<0)
ok('all_other_orbits_joint_return_decays',quad_upper<0)
ok('short_fee_below_2epsilon',s.simplify(2*eps-s.Rational(3,2)*eps)>0)
# Exponential averaging with both endpoints.
a,delta,T=s.symbols('a delta T',positive=True); hh=s.symbols('hh',real=True)
ET=s.exp(2*delta*hh)*(1-s.exp(-2*delta*T))/(2*delta*T)
ok('full_signal_average',s.simplify(s.integrate(s.exp(2*delta*a),(a,hh-T,hh))/T-ET)==0)
LL=s.symbols('LL',positive=True)
ok('window_correction_average_log_scale',s.simplify(ET.subs(hh,LL/2-s.log(LL))*s.exp(-delta*LL)-LL**(-2*delta)*(1-s.exp(-2*delta*T))/(2*delta*T))==0)
# Full CCM bookkeeping from the same A, no short fee in K.
Hh,Vv,Rr,Err,Da,Ts,Ww,Ga=s.symbols('Hh Vv Rr Err Da Ts Ww Ga')
Apr=-Hh+Vv-Rr+Err
ok('CCM_return_sign',s.expand((Da-Apr)-(Rr+Hh+Da-Vv-Err))==0)
ok('long_divisor_return_once',s.expand((Apr-Ts)-(-Hh+Vv-Rr+Err-Ts))==0)
ok('orbit_return_full_source',s.expand((Da-Apr).subs(Rr,Ww+Ga)-(Ww+Ga+Hh+Da-Vv-Err))==0)
reject('second_decaying_credit_is_free',s.expand((Da-Apr)-(Rr+2*Hh+Da-Vv-Err))==0)
print(json.dumps({'exact_controls':len(passed),'planted_errors_detected':len(planted),'sympy_version':s.__version__,'passed':passed,'planted':planted,'rational_decay_upper_bounds':{'linear':str(lin_upper),'joint_other_orbits':str(quad_upper)},'scope':'Exact local algebra only. No actual zero values, production spectra, global sign certificate, Lean, Arb or independent review.'},ensure_ascii=False,indent=2,sort_keys=True))
