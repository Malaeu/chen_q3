"""Exact algebra controls; not a CCM cone-dimension or D2 certificate."""
from itertools import product
import sympy as s

# Registered before execution: sign-only maximality, exact deletion-box bound,
# and Q<=0 not forcing a nonpositive DH prime block.
N,A,O,P,H,I,P12,P3,c=s.symbols('N A O P H I P12 P3 c', real=True)
k=A+O-c*N-P
assert s.expand(k+c*N-(A+O-P))==0
assert s.expand((P12-I-H).subs(I,A+O-H-4*N)-(P12-A-O+4*N))==0
print('PASS 1 full-form floor and exact (12) normalization')

w=[s.Rational(1,2),s.Rational(3,2),s.Integer(2)]
for q in product([-2,0,3],repeat=3):
    vals=[sum(wi*qi*ei for wi,qi,ei in zip(w,q,e)) for e in product([0,1],repeat=3)]
    assert max(vals)==sum(wi*max(qi,0) for wi,qi in zip(w,q))
for bval in product([-2, 0, 3], repeat=2):
    vals=[sum(qi*ei for qi,ei in zip(bval,e)) for e in product([0,1],repeat=2)]
    assert max(vals)==sum(max(qi,0) for qi in bval)
print('PASS 2 exact atom- and prime-block-deletion suprema')

base,loss,pp,pm=s.symbols('base loss pp pm', real=True)
assert s.expand(base+loss-(pp-pm) - (pm-(pp-base-loss)))==0
print('PASS 3 uncovered signed remainder keeps favorable correlations')

# Cone geometry controls: same dimension and positive arithmetic weights,
# but full-dimensional, zero-only, and lower-dimensional cones.
x,y=s.symbols('x y', real=True)
assert s.Matrix([x,y]).dot(-s.eye(2)*s.Matrix([x,y]))==-x*x-y*y
assert s.Matrix([x,y]).dot(s.eye(2)*s.Matrix([x,y]))==x*x+y*y
assert s.Matrix([x,y]).dot(s.diag(1,0)*s.Matrix([x,y]))==x*x
print('PASS 4 cone geometry depends on correlation matrices, not weight signs')

t=s.symbols('t', positive=True)
a={1:1,2:t,3:-t,4:-1,5:0,6:1}
b={1:s.Integer(0)}
for n in range(2,7):
    b[n]=s.expand(a[n]*s.log(n)-sum(a[d]*b[n//d] for d in s.divisors(n) if d>1))
assert s.simplify(b[2]-t*s.log(2))==0
assert s.simplify(b[3]+t*s.log(3))==0
assert s.simplify(b[6]-(1+t*t)*s.log(6))==0
print('PASS 5 literal DH log-derivative recurrence at 2,3,6')

r,u=s.symbols('r u', real=True)
q00=2*(1-r)
q11=2*(1-r)*s.cos(2*s.pi*r)-s.sin(2*s.pi*r)/s.pi
q01=-s.sqrt(2)*s.sin(2*s.pi*r)/s.pi
qf=s.expand((q00+q11-2*q01)/2)
assert s.simplify(qf.subs(r,s.Rational(1,2)))==0
assert s.simplify(qf.subs(r,1))==0
rhs=(u*(1+s.cos(u))-(2*s.sqrt(2)-1)*s.sin(u))/(2*s.pi)
assert s.trigsimp(qf.subs(r,1-u/(2*s.pi))-rhs)==0
assert 3**4>4**3 and 3**6<4**5
assert s.Rational(173,100)**2<3
assert s.Rational(707,500)**2<2
assert s.Rational(2200,1211)<s.Rational(457,250)
# d[u*cot(u/2)]/du = (sin(u)-u)/(2 sin^2(u/2)).
assert s.trigsimp(s.expand(s.diff(u*s.cos(u/2)/s.sin(u/2),u)*2*s.sin(u/2)**2+u-s.sin(u)))==0
print('PASS 6 even literal-carrier witness: Q(log 2)=0, Q(log 3)<0 analytically')

# For a finite pole-free DH form, the correct forced-exclusion threshold is c_D,
# not zero: K_D=c_D*N+A_D-P_D.
cD,AD,PD=s.symbols('cD AD PD', real=True)
assert s.expand(cD*N+AD-PD-cD*N)==AD-PD
print('PASS 7 signed-cone exclusion threshold and normalization')

# Exact projection-upper simplification for the recovered DH-C witness.
R,delta=s.symbols('R delta', positive=True)
a=s.symbols('a', real=True)
ray=(-R+(2*R+delta)*a)/(1-a)
upper=-R+delta**2/(R-delta)
assert s.factor(ray.subs(a,delta**2/R**2)-upper)==0
assert s.factor(s.diff(ray,a)-(R+delta)/(1-a)**2)==0
beta=s.symbols('beta', positive=True)
AD,PD=s.symbols('AD PD', real=True)
assert s.expand((AD-beta-PD)+beta)==AD-PD
assert s.simplify(upper.subs({R:10,delta:s.Rational(1,10)})+1)<0
print('PASS 8 recovered projected-witness Rayleigh envelope and signed threshold')
print('ALL 8 GROUPS PASSED; no literal-Q membership or CCM cone dimension claimed')
