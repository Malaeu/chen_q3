from pathlib import Path
from fractions import Fraction as Q
import json
import sympy as s
z,h,T,u=s.symbols('z h T u', real=True)
F=s.exp(-2*z*h)*(s.exp(2*z*T)-1)/(2*z*T)
assert s.limit(F,z,0)==1
# Derivative in upper endpoint verifies the full interval integral (T fixed).
assert s.simplify(s.diff(T*F,h)-(s.exp(-2*z*h)-s.exp(-2*z*(h-T))))==0
assert s.simplify(F.subs(h,T/2)-(s.sinh(z*T)/(z*T)).rewrite(s.exp))==0
checks=3
for alpha in [Q(1,16),Q(1,8),Q(1,5)]:
 for sigma in [Q(-1),Q(-1,2),Q(-1,10),Q(0),Q(1,10),Q(1,2),Q(1)]:
  exponent=Q(1,2)+abs(sigma)-sigma+(2*sigma*alpha if sigma>0 else 0)
  assert exponent>=Q(1,2)
  assert exponent==(Q(1,2)+2*sigma*alpha if sigma>0 else Q(1,2)+2*abs(sigma) if sigma<0 else Q(1,2))
  checks+=2
# Pair denominator reflection at t=gamma+-v; no numerator symmetry assumed.
d,v=s.symbols('d v',real=True)
for r in range(1,7):
 assert s.conjugate((d+s.I*v)**(2*r))==(d-s.I*v)**(2*r);checks+=1
ka,kb,zx,zy,np,nm=s.symbols('ka kb zx zy np nm',real=True)
assert s.expand(s.re((ka+s.I*kb)*((zx+s.I*zy)*np+(zx-s.I*zy)*nm))-(ka*zx*(np+nm)-kb*zy*(np-nm)))==0
checks+=1
out={'status':'PASS_LOCAL_ALGEBRA_ONLY','checks':checks,'source_spectral_evaluations':0,'hypothetical_zeros_assigned':False,'lean':0,'arb':0}
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
