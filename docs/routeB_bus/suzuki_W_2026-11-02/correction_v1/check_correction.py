"""Exact sign/parity controls for the correction; no source W computation."""
from pathlib import Path
import json
import sympy as s

x,z,U,O=s.symbols('x z U O')
I=s.I
tests={
    'plus_rhs_has_deficiency_plus_i':s.simplify(I*s.diff(s.exp(x),x)-I*s.exp(x))==0,
    'minus_rhs_has_deficiency_minus_i':s.simplify(I*s.diff(s.exp(-x),x)+I*s.exp(-x))==0,
    'swapped_plus_rhs_rejected':s.simplify(I*s.diff(s.exp(-x),x)-I*s.exp(-x))!=0,
}
Wpi=s.expand((z-I)*(U+O)-(z+I)*(U-O))
W0=s.expand((z-I)*(U+O)+(z+I)*(U-O))
tests['theta_pi_two_parity_identity']=s.simplify(Wpi-(-2*I*U+2*z*O))==0
tests['theta_zero_two_parity_identity']=s.simplify(W0-(2*z*U-2*I*O))==0
tests['cosine_only_omits_nonzero_polynomial']=s.simplify(Wpi-(-2*I*U))==2*z*O
tests['cosine_only_is_not_general_W']=s.Poly(Wpi+2*I*U,z,U,O).is_zero is False

# Planted finite rational form, explicitly not a source discretization.
A=s.diag(2,3,5,7);lam=s.Rational(-1);T=A-lam*s.eye(4)
R=s.diag(1,1,-1,-1)
c=s.Matrix([1,2,0,0]);h=s.Matrix([0,0,3,4])
u=T.inv()*c;o=T.inv()*h
vp=T.inv()*(c+h);vm=T.inv()*(c-h)
tests['same_shift_parity_reconstruction_plus']=vp==u+o
tests['same_shift_parity_reconstruction_minus']=vm==u-o
tests['reflection_interchanges_pair']=vm==R*vp
tests['T_norms_equal_without_separate_normalization']=(vp.T*T*vp)[0]==(vm.T*T*vm)[0]
tests['odd_solution_nonzero']=o!=s.zeros(4,1)
assert all(tests.values()),tests
out={'status':'DIAGNOSTIC_NEVER_A_PROOF','control_kind':'exact symbolic/rational sign and parity checks; no numerical source W','checks':tests,'passed':len(tests),'source_W_computed':False,'continuum_shift_certified':False}
Path(__file__).with_name('CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
