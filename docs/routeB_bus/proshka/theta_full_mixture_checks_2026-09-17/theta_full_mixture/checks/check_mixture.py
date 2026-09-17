"""Exact algebraic/rational controls for the full-mixture research note.
No floating-point sign test and no claim to verify the analytical arguments.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
import sympy as s

x,y=s.symbols('x y', real=True)
P=1-x+x**2/s.Integer(6)-x**3/s.Integer(18)
margin=s.factor(P.subs(x,s.Rational(10,9)))
assert margin==s.Rational(121,6561)
# dP/dx = -((x-1)^2+5)/6 < 0 on the full real axis.
assert s.simplify(s.diff(P,x)+((x-1)**2+5)/6)==0
# Moment lower polynomial Q_s(y), y in [0,s].
Q=1-y+(1-x/3)*y**2/6
assert s.expand(Q.subs(y,x)-P)==0
# Its y derivative is at most -1+(10/9)/3<0 for 0<=x,y<=10/9.
assert -1+s.Rational(10,27)<0
assert s.Rational(19,17)*3==s.Rational(57,17)

# Noncommuting positive anchor matrices and genuinely complex feature matrices.
A1=s.Matrix([[2,1],[1,3]])
A2=s.Matrix([[3,0],[0,1]])
B1=s.Matrix([[1,s.I,2],[2,1-s.I,0]])
B2=s.Matrix([[0,2,1+s.I],[1,0,-1]])
p=s.Rational(1,3)
A=p*A1+(1-p)*A2
B=p*B1+(1-p)*B2
Z=A.inv()*B
Z1=A1.inv()*B1
Z2=A2.inv()*B2
var=p*(Z1-Z).conjugate().T*A1*(Z1-Z)+(1-p)*(Z2-Z).conjugate().T*A2*(Z2-Z)
difference=p*B1.conjugate().T*A1.inv()*B1+(1-p)*B2.conjugate().T*A2.inv()*B2-B.conjugate().T*A.inv()*B
assert (var-difference).applyfunc(s.simplify)==s.zeros(3)

# Scale covariance of the raw theta summand, using r=exp(t/2).
r,n=s.symbols('r n',positive=True)
phi= (4*s.pi**2*r**9-6*s.pi*r**5)*s.exp(-s.pi*r**4)
phi_n=(4*s.pi**2*n**4*r**9-6*s.pi*n**2*r**5)*s.exp(-s.pi*n**2*r**4)
assert s.simplify(phi_n.subs(r,r/s.sqrt(n))-phi/s.sqrt(n))==0

# A strong-log-concavity moment majorant does not imply global Fourier positivity.
# j(w)=exp(-18w^2-(18^2/8)w^4), nodes r/(4*sqrt(18)).
def exp_minus_bounds(a: F) -> tuple[F,F]:
    assert 0<=a<=1
    lo=sum(((-a)**k/F(factorial(k))) for k in range(40))
    hi=lo+(-a)**40/F(factorial(40))
    assert lo>0 and hi>=lo
    return lo,hi
al,au=exp_minus_bounds(F(129,2048))
bl,bu=exp_minus_bounds(F(33,128))
cl,cu=exp_minus_bounds(F(1233,2048))
assert al>bu
U=(1-cl)*(1-al)-(al-bu)**2
L=(1-cu)*(1-au)-(au-bl)**2
assert L<=U < -F(1,100000)

result={
    'status':'PASS',
    'band_polynomial_lower':str(margin),
    'band_tau_squared_upper':20,
    'source_phi_scaling':'EXACT_SYMBOLIC',
    'complex_noncommuting_variance_control':'EXACT_ZERO_DIFFERENCE',
    'quartic_plant_determinant_L':str(L),
    'quartic_plant_determinant_U':str(U),
    'quartic_plant_U_less_than':'-1/100000',
    'quartic_plant_U_decimal_diagnostic':float(U),
    'scope':'Algebra and rational controls only; new analytical theorems require review.'
}
Path(__file__).with_name('mixture_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
