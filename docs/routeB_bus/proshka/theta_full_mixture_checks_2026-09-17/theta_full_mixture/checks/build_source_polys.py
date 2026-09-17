"""Generate exact rational polynomials for the certified full-source derivatives."""
import sympy as s,json
from pathlib import Path
x,y=s.symbols('x y')
D=lambda f:2*x*s.diff(f,x)
def pdata(f):
 n,d=s.fraction(s.factor(f))
 return [[str(c) for c in s.Poly(s.expand(v.subs(x,y+3)),y).all_coeffs()] for v in [n,d]]
res={'eps':{},'qone':{}}
for m in [4,9]:
 f=m*(2*m*x-3)/(2*x-3)
 res['eps'][str(m)]=[]
 for j in range(7):
  res['eps'][str(m)].append(pdata(f))
  f=s.factor(2*x*(s.diff(f,x)-(m-1)*f))
f=4*x+24*x/(2*x-3)**2
for j in range(5):
 if j in [0,1,2,4]:res['qone'][str(j)]=pdata(f)
 f=s.factor(D(f))
Path(__file__).with_name('source_polys.json').write_text(json.dumps(res,indent=2)+'\n')
