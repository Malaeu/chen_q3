import sympy as s,json
from pathlib import Path
x,m,y,z=s.symbols('x m y z')
B=m*(2*m*x-3)/(2*x-3)
res={}
for x0,n0,E,name in [(s.Rational(31,10),4,22,'tail_n4'),(s.Integer(8),2,2980,'tail_x8')]:
 assert sum(x0**k/s.factorial(k) for k in range(40))>E
 C=B;rows=[]
 for j in range(7):
  P=s.Poly(s.factor((-1)**j*C.subs(x,x0)),m)
  p=n0*n0; cc=sum(abs(co)*p**power[0] for power,co in P.terms())
  # n^degree exponential tail ratio at n>=n0; check <1/2
  rat=s.Rational(n0+1,n0)**(2*(j+2))/s.Integer(E)**(2*n0+1)
  assert rat<s.Rational(1,2)
  ub=2*cc/s.Integer(E)**(p-1)
  rows.append(str(ub));print(name,j,float(ub))
  C=s.factor(2*x*(s.diff(C,x)-(m-1)*C))
 res[name]=rows
# sign-polys Tj(z+24)
T=s.Integer(1)
for j in range(8):
 assert all(co>0 for co in s.Poly(s.expand(T.subs(z,y+24)),y).all_coeffs())
 T=s.expand(z*(T-s.diff(T,z)))
q=4*x+24*x/(2*x-3)**2
D=lambda f:2*x*s.diff(f,x)
dq=D(q);ddq=s.factor(D(dq));d4q=s.factor(D(D(ddq)))
for name,f in [('dq',dq),('2q_dq',2*q-dq),('ddq_16x',ddq-16*x),('8q_ddq',8*q-ddq),('d4q',d4q)]:
 num,den=s.fraction(s.factor(f));coeff=s.Poly(s.expand(num.subs(x,y+8)),y).all_coeffs()
 print(name,'positive',all(co>=0 for co in coeff),s.factor(f))
 assert all(co>=0 for co in coeff) and any(co>0 for co in coeff)
 dc=s.Poly(s.expand(den.subs(x,y+8)),y).all_coeffs()
 assert all(co>=0 for co in dc) and any(co>0 for co in dc)
res['tail_x8_use_e8_lower']=2980
assert sum(s.Integer(8)**k/s.factorial(k) for k in range(40))>2980
Path(__file__).with_name('tail_bounds.json').write_text(json.dumps(res,indent=2)+'\n')
