import sympy as s
z=s.symbols('z',real=True)
xs=[s.Integer(i*i) for i in range(4)]
d=s.Matrix([1,s.sqrt(2),s.sqrt(2),s.sqrt(2)])
P=s.prod(z-x for x in xs)
H=z+z/(z*z+1)
c=s.Matrix([-(x*x+1)/(d[i]*s.diff(P,z).subs(z,x)) for i,x in enumerate(xs)])
F=[H.subs(z,x) for x in xs]
A=s.zeros(4)
for i in range(4):
 for j in range(4):
  if i!=j:A[i,j]=s.simplify(d[i]*d[j]*(F[i]-F[j])/(xs[i]-xs[j]))
for i in range(4): A[i,i]=s.simplify(-sum(A[i,j]*c[j] for j in range(4) if j!=i)/c[i])
X=s.diag(*xs);u=s.Matrix([d[i]*F[i] for i in range(4)])
assert A*c==s.zeros(4,1)
assert s.simplify(X*A-A*X-u*d.T+d*u.T)==s.zeros(4)
R=lambda t:s.diag(*[1/(x-t) for x in xs])
V=s.factor((d.T*R(z)*c)[0]);U=s.factor((u.T*R(z)*c)[0])
assert s.simplify(V-(z*z+1)/P)==0
assert s.simplify(U-z*(z*z+2)/P)==0
assert s.factor(s.diff(H,z)-s.Rational(7,8))==(z*z-3)**2/(8*(z*z+1)**2)
cols=[R(t)*c/V.subs(z,t) for t in [-2,2]]
Y=s.Matrix.hstack(*cols);G=s.simplify(Y.T*A*Y)
assert G==s.Matrix([[s.Rational(22,25),s.Rational(6,5)],[s.Rational(6,5),s.Rational(22,25)]])
y=cols[0]-cols[1]
assert (y.T*A*y)[0]==-s.Rational(16,25)
print('A=',A)
print('c=',c.T,'norm²=',(c.T*c)[0])
print('single resolvent quadratic=V² Hprime>=7 V²/8>0 for every real nonnode')
print('two-shift Gram=',G,'eigenvalues=',G.eigenvals())
print('competitor=',y.T,'norm²=',(y.T*y)[0],'Rayleigh=',s.factor((y.T*A*y)[0]/(y.T*y)[0]))
print('ALL EXACT ASSERTIONS PASS; synthetic, not CCM.')
