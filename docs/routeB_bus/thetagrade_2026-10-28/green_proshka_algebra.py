import sympy as s
from math import comb, lcm

t = s.symbols('t', positive=True)
u = s.Matrix([s.sqrt(1+t**2), t**3])
J = s.diag(1, 2+t**4)
H = J+u*u.T
B = H-2*s.eye(2)
assert s.simplify(B.det()) == 0
assert s.simplify(s.trace(B)-(t**2+t**4+t**6)) == 0
S = s.simplify(u[1]**2/t**4)
T = s.simplify(u[1]**2/t**8)
assert S == t**2 and T == t**-2
alpha2 = s.factor(1/(1+(1+t**2)*T/(1+S)**2))
assert s.limit(alpha2, t, 0, dir='+') == 0

J = s.diag(2, 5, 11)
u = s.Matrix([1, 2, -1]); H = J+u*u.T
rho = s.Integer(3); q = s.Matrix([1, 2, 2])/3
r = (H-rho*s.eye(3))*q
up = u[1:3, 0:1]
R = s.diag(s.Rational(1, 2), s.Rational(1, 8))
S = (up.T*R*up)[0]
W = R-R*up*up.T*R/(1+S)
assert s.simplify(W-(J[1:3, 1:3]-rho*s.eye(2)+up*up.T).inv()) == s.zeros(2)
a = q[0]; b = u[0]
assert s.simplify(-a*b*W*up+W*r[1:3, 0:1]-q[1:3, 0:1]) == s.zeros(2, 1)
sigma = J[0, 0]-rho+b**2/(1+S)
assert s.simplify(a*sigma-r[0]+b*(up.T*W*r[1:3, 0:1])[0]) == 0
C = s.Integer(4); lam = rho-C
z = s.Matrix([2, 1, -1]); e = (H-C*s.eye(3))*z
assert s.simplify(z[1:3, 0:1]+b*z[0]*W*up-W*(e[1:3, 0:1]-lam*z[1:3, 0:1])) == s.zeros(2, 1)
d = (u.T*z)[0]
assert s.simplify(d*R*up+z[1:3, 0:1]-R*(e[1:3, 0:1]-lam*z[1:3, 0:1])) == s.zeros(2, 1)

J0 = s.diag(1, 1, 4); u0 = s.Matrix([1, 0, 1])
assert (J0+u0*u0.T-s.eye(3))*s.Matrix([0, 1, 0]) == s.zeros(3, 1)
assert s.diag(1, 2)+s.Matrix([1, 0])*s.Matrix([[1, 0]]) == 2*s.eye(2)
Q = s.Matrix([[s.Rational(1,2), -s.Rational(1,2)],
              [-s.Rational(1,2), s.Rational(1,2)]])
assert Q*s.ones(2,1) == s.zeros(2,1)
assert Q.det() == 0 and s.trace(Q) == 1 and Q[0,1] < 0
RR = s.diag(2, 1); uu = s.Matrix([1, 1])
WW = RR-RR*uu*uu.T*RR/4
assert (RR**2-WW**2).det() == -s.Rational(1, 4)
for n in range(1, 101):
    v = 1
    for k in range(1, 2*n+1):
        v = lcm(v, k)
    assert v % comb(2*n, n) == 0
print('ALL_EXACT_CHECKS_PASSED')
