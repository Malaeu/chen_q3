#!/usr/bin/env python3
"""Exact algebra controls for DIAGONAL; no literal CCM numerical scan."""
import sympy as s

# Pole contribution has zero diagonal defect.
t, L, kap = s.symbols('t L kap', positive=True)
bp = kap*t/(L**2+16*s.pi**2*t**2)
wp = kap*(L**2-16*s.pi**2*t**2)/(L**2+16*s.pi**2*t**2)**2
assert s.simplify(s.diff(bp,t)-wp) == 0

# One jump: full even diagonal equals derivative part plus the cosine defect.
a, w = s.symbols('a w', positive=True)
bj = w/s.pi*s.sin(2*s.pi*t*a/L)
defect = -2*w*s.cos(2*s.pi*t*a/L)
actual_even = -2*w*(1-a/L)*s.cos(2*s.pi*t*a/L) + bj/t
assert s.simplify(s.diff(bj,t)+bj/t+defect-actual_even) == 0
assert s.simplify(s.limit(s.diff(bj,t)+defect,t,0)+2*w*(1-a/L)) == 0

# Reciprocal positive pair: beta values cancel, derivative and defect do not.
for n in range(6):
    theta = s.symbols('theta', real=True)
    cs = s.cos(2*s.pi*n-theta)
    assert s.trigsimp(s.sin(theta)+s.sin(2*s.pi*n-theta)) == 0
    assert s.trigsimp((2*w/L)*(a*s.cos(theta)+(L-a)*cs)-2*w*s.cos(theta)) == 0
    assert s.trigsimp(-2*w*(s.cos(theta)+cs)+4*w*s.cos(theta)) == 0

# Moment-disk identity for a finite positive-atom control (not the CCM measure).
r = s.Integer(1)
ats = [(s.pi/3,s.Integer(2)),(s.pi/2,s.Integer(3))]
beta = lambda x: sum(v*s.sin(x*q)/s.pi for q,v in ats)
delta = lambda x: 2*sum(v*(1-s.cos(x*q)) for q,v in ats)
dd = s.simplify(delta(2)+delta(0)-2*delta(1))
db = s.simplify(beta(2)+beta(0)-2*beta(1))
Z = s.simplify(sum(v*(1-s.cos(q))*(s.cos(q)+s.I*s.sin(q)) for q,v in ats))
Z0 = sum(v*(1-s.cos(q)) for q,v in ats)
assert s.simplify(dd-4*s.re(Z)) == 0
assert s.simplify(db+2*s.im(Z)/s.pi) == 0
assert s.simplify(4*delta(1)**2-dd**2-4*s.pi**2*db**2-16*(Z0**2-s.expand_complex(Z*s.conjugate(Z)))) == 0

# Supplied synthetic stationary control; all calculations are exact.
z = s.symbols('z')
xs = [s.Integer(x) for x in (0,1,4,9)]
ds = [s.Integer(1),s.sqrt(2),s.sqrt(2),s.sqrt(2)]
P = s.prod(z-x for x in xs)
F = z+z/(z*z+1)
fs = [F.subs(z,x) for x in xs]
c = s.Matrix([-(x*x+1)/(d*s.diff(P,z).subs(z,x)) for x,d in zip(xs,ds)])
A = s.zeros(4)
for i in range(4):
    for j in range(4):
        if i != j:
            A[i,j] = ds[i]*ds[j]*(fs[i]-fs[j])/(xs[i]-xs[j])
for i in range(4):
    A[i,i] = -sum(A[i,j]*c[j] for j in range(4) if j != i)/c[i]
assert A*c == s.zeros(4,1)
V = s.factor(sum(ds[i]*c[i]/(xs[i]-z) for i in range(4)))
U = s.factor(sum(ds[i]*fs[i]*c[i]/(xs[i]-z) for i in range(4)))
assert s.factor(U/V-F) == 0
p = s.cancel(P*V); q = s.cancel(P*U)
for i,x in enumerate(xs):
    assert s.simplify(q.subs(z,x)-fs[i]*p.subs(z,x)) == 0
    assert s.simplify(ds[i]**2*(s.diff(q,z).subs(z,x)-fs[i]*s.diff(p,z).subs(z,x))-A[i,i]*p.subs(z,x)) == 0
R = s.diag(*[1/(x+1) for x in xs])
y = R*c; e = s.eye(4)[:,0]
aa = A[0,0]; bb = (A*y)[0]; qq = (y.T*A*y)[0]
assert (aa,bb,qq) == (2,s.Rational(3,100),s.Rational(1,2500))
det = s.factor(aa*qq-bb**2)
assert det == -s.Rational(1,10000)
g0 = bb*e-aa*y
assert s.factor((g0.T*A*g0)[0]) == -s.Rational(1,5000)
assert s.factor((g0.T*g0)[0]) == s.Rational(391,33750)
assert s.factor((g0.T*A*g0)[0]/(g0.T*g0)[0]) == -s.Rational(27,1564)

# Trial corrections checked on an unrelated rational symmetric matrix.
T = s.Matrix([[2,1,-1],[1,-2,3],[-1,3,4]])
ct = s.Matrix([s.Rational(2,3),s.Rational(1,3),s.Rational(2,3)])
assert (ct.T*ct)[0] == 1
rho = (ct.T*T*ct)[0]; residual = T*ct-rho*ct
amp = s.diag(1,s.Rational(-2,3),s.Rational(3,5))
W = -sum(T[i,j]*ct[i]*ct[j]*(amp[i,i]-amp[j,j])**2 for i in range(3) for j in range(i+1,3))
assert s.simplify(((amp*ct).T*(T-rho*s.eye(3))*(amp*ct))[0]-W-sum(amp[i,i]**2*ct[i]*residual[i] for i in range(3))) == 0
print('PASS: pole, jump diagonal, reciprocal pair, moment disk, Hermite, mixed-node negative witness, trial correction')
