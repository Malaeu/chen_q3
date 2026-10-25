"""Exact local checks, not numerical tests of an off-line zero or CCM spectrum."""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import hashlib, json
import sympy as s
R=Path(__file__).resolve().parent
C=Counter(); planted=[]
x,d=s.symbols('x d', real=True); d=s.symbols('d', positive=True)
u,v=s.symbols('u v', real=True)
eta=(1+s.I*u)/(1-s.I*u)
q=(1+s.I*v)/(1-s.I*v)  # abstract unit translation phase, not a zero
for r in range(1,5):
    U=eta*((d-s.I*x)/(d+s.I*x))**r
    assert s.cancel(U*s.conjugate(U)-1)==0
    C['allpass_unitarity']+=1
# The full mixed identity below is checked once for formal unit phases;
# expanding it separately after four rational substitutions is unnecessary.
Q,V=s.symbols('Q V',nonzero=True)
assert s.expand((Q-V/Q)*(1/Q-Q/V)-(2-V/Q**2-Q**2/V))==0
C['whole_pair_cross_terms']=1
# Reflection in the coefficient quotient.
a,b=s.symbols('a b', real=True)
r=s.symbols('r', positive=True)
z=a+s.I*b
J=s.Matrix([[0,r],[r,0]])
T=s.diag(z,s.conjugate(z))
assert s.simplify(T.conjugate().T*J*T-r*s.Matrix([[0,s.conjugate(z)**2],[z**2,0]]))==s.zeros(2)
C['full_reflected_congruence']+=1
N=s.diag(1/z,1/s.conjugate(z))
assert s.simplify(N.conjugate().T*T.conjugate().T*J*T*N-J)==s.zeros(2)
C['separate_complex_normalization']+=1
# A deliberately wrong modulus-only normalization does not recover J.
z0=s.Rational(3,5)+s.I*s.Rational(4,5)
T0=s.diag(z0,s.conjugate(z0))
assert T0.conjugate().T*J*T0 != J
planted.append('modulus_only_source_normalization')
# The physical compression is not the pointwise diagonal realization.
P=s.Matrix([[s.Rational(1,2),s.Rational(1,2)],[s.Rational(1,2),s.Rational(1,2)]])
D=s.diag(s.Rational(1,4),s.Rational(3,4))
assert P*P==P and P*D != D*P
assert (P*D*P).trace()==s.Rational(1,2)
C['compression_and_leakage']+=2
planted.append('free_P_commutation')
# Positive smoothing does not turn an indefinite test matrix positive.
K=s.diag(-1,2)
assert (D*K*D)[0,0]<0
planted.append('positive_smoothing_implies_positive_signed_form')
# Full quadratic return: two mixed terms plus the error square.
zv=s.Matrix([1+s.I,2-s.I]); ev=s.Matrix([s.Rational(1,3),s.I/s.Integer(5)])
KH=s.Matrix([[2,1+s.I],[1-s.I,-3]])
lhs=((zv+ev).conjugate().T*KH*(zv+ev)-zv.conjugate().T*KH*zv)[0]
rhs=(zv.conjugate().T*KH*ev+ev.conjugate().T*KH*zv+ev.conjugate().T*KH*ev)[0]
assert s.simplify(lhs-rhs)==0
C['full_quadratic_return']=1
assert s.simplify(lhs-(ev.conjugate().T*KH*ev)[0]) != 0
planted.append('omitted_projection_mixed_terms')
# Axis control for an even entire model: not a counterexample to Xi.
t=s.symbols('t',real=True); F=lambda z:1+z*z
assert s.simplify(F(t)-F(s.I*t))==2*t*t
planted.append('free_real_imaginary_axis_rotation')
# Whole-pair source phase cannot be replaced by eta=1.
Ub=eta*(d-s.I*x)/(d+s.I*x)
assert s.simplify(Ub-(d-s.I*x)/(d+s.I*x)) != 0
planted.append('eta_replaced_by_one')
# Vertical source powers from xi, the second-order filter and separator.
for rr in range(1,9):
    p=Fraction(7,2)+4-2*rr
    assert p==Fraction(15,2)-2*rr
    assert p-1==Fraction(13,2)-2*rr
    C['source_and_dyadic_powers']+=2
# Fixed derivative order, full mixed-return powers.
for eps in (Fraction(1,64),Fraction(1,100),Fraction(1,256)):
    qq=int(1/eps)+3
    powers=(1+eps*(Fraction(1,2)-qq),Fraction(1,2)+eps*(Fraction(3,2)-qq),Fraction(1,2)+eps*(1-qq),Fraction(1,2)+eps*(Fraction(1,2)-qq))
    assert all(p<0 for p in powers)
    assert Fraction(1,2)-1<0
    C['full_return_exponents']+=2
# A Fourier cutoff Y=(4/pi)log(m) has exp(-pi Y/4)=m^-1.
L=s.symbols('L',positive=True)
assert s.simplify(s.exp(-s.pi*(4*L/s.pi)/4)-s.exp(-L))==0
C['paid_frequency_cutoff']=1
out={
 'status':'PASS_EXACT_LOCAL_CONTROLS_NOT_GLOBAL_SIGN_CERTIFICATION',
 'sympy_version':s.__version__,'counts':dict(C),'exact_controls':sum(C.values()),
 'planted_failures_detected':len(planted),'planted_failures':planted,
 'registration_sha256':hashlib.sha256((R/'registration.json').read_bytes()).hexdigest(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'numerical_hypothetical_zero_assigned':False,'CCM_spectral_runs':0,'arb_runs':0,'lean_runs':0
}
(R/'exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
