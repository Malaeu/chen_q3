from pathlib import Path
import json
import sympy as s
u,b=s.symbols('u b');H=s.Function('H')(u)
B=lambda f:s.diff(f,u,2)-f/4
cases=0
for r in range(1,7):
 p=u**(2*r-1)/s.factorial(2*r-1);k=s.exp(-b*u)*p
 q=(b*b-s.Rational(1,4))**2*p-4*b*(b*b-s.Rational(1,4))*s.diff(p,u)+(6*b*b-s.Rational(1,2))*s.diff(p,u,2)-4*b*s.diff(p,u,3)+s.diff(p,u,4)
 assert s.simplify(B(B(k))-s.exp(-b*u)*q)==0;cases+=1
 F=k*s.diff(H,u,3)-s.diff(k,u)*s.diff(H,u,2)+s.diff(k,u,2)*s.diff(H,u)-s.diff(k,u,3)*H-(k*s.diff(H,u)-s.diff(k,u)*H)/2
 assert s.simplify(s.diff(F,u)-(k*B(B(H))-B(B(k))*H))==0;cases+=1
 h0,h1,h2,h3=s.symbols('h0:4')
 end=-(k.subs(u,0)*h3-s.diff(k,u).subs(u,0)*h2+s.diff(k,u,2).subs(u,0)*h1-s.diff(k,u,3).subs(u,0)*h0-(k.subs(u,0)*h1-s.diff(k,u).subs(u,0)*h0)/2)
 expected=h2+2*b*h1+(3*b*b-s.Rational(1,2))*h0 if r==1 else h0 if r==2 else 0
 assert s.simplify(end-expected)==0;cases+=1
 if r<=2:assert end!=0;cases+=1
# Negative control for phase loss: an ordinary nonreal constant, NOT a zero.
c=1+s.I
assert s.simplify(1/s.conjugate(c)**2-1/(c*s.conjugate(c)))!=0;cases+=1
out={'status':'PASS_LOCAL_FILTER_ALGEBRA_ONLY','sympy':s.__version__,'checks':cases,'zero_values_assigned':False,'CCM_evaluations':0,'lean_runs':0,'arb_runs':0}
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
