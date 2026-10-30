import sympy as s
x, a = s.symbols('x a', real=True)
C = s.integrate(((x*x-(x+a)**2)**2)/2, (x, -1, 1-a))
assert s.simplify(C-a**2*(2-a)**3/6) == 0
J = {k: s.integrate(x**k*s.cosh(x/2), (x,-1,1)) for k in (0,2,4)}
pole = J[2]**2-J[0]*J[4]
assert s.simplify(s.expand_trig(
    pole+2*s.integrate(s.cosh(a/2)*C,(a,0,2)))) == 0
P = s.diag(1,1,0)
I = s.eye(3)
H = s.Matrix([[2,-1,3],[-1,1,2],[3,2,4]])
B = s.Matrix([[2,1,1],[1,2,0],[1,0,2]])/4
q = s.Matrix([s.Rational(3,5),s.Rational(4,5),0])
rho = (q.T*H*q)[0]
r = P*H*q-rho*q
z = B*q
e = (I-P)*z
sigma = (I-P)*B*B*q
v = P*z
comm = (z.T*H*z-q.T*H*B*B*q)[0]
r_local = (r.T*P*B*B*q)[0]
N = (v.T*H*v)[0]-rho*(v.T*v)[0]
ledger = ((q.T*H*sigma)[0]+comm+r_local-2*(z.T*H*e)[0]
          +(e.T*H*e)[0]+rho*(e.T*e)[0])
assert s.simplify(N-ledger)==0
assert s.simplify((z.T*H*z)[0]-rho*(z.T*z)[0]
                  -(q.T*H*sigma)[0]-comm-r_local)==0
M=s.symbols('M',positive=True)
A=s.diag(-1,M)
bb=s.Matrix([[s.Rational(1,2),s.Rational(1,4)],
             [s.Rational(1,4),s.Rational(1,2)]])
f=s.Matrix([1,0]); y=bb*f
assert s.simplify((y.T*(A+s.eye(2))*y)[0]-(M+1)/16)==0
assert (y.T*y)[0]==s.Rational(5,16)
assert s.simplify((y.T*A*y)[0]-(-s.Rational(1,4)+M/16))==0
print('PASS: moving endpoint / pole factor / full residual ledger / minimality lower-bound control')
