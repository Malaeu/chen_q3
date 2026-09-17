import sympy as s,json,hashlib
from fractions import Fraction as F
from pathlib import Path
B=Path(__file__).parent
q,r,t,u,v=s.symbols('q r t u v')
W=12*q**6-24*q**4*t+24*q**3*r**2+2*q**3*v-12*q**2*r*u+7*q**2*t**2+12*q*r**2*t-q*t*v+q*u**2-9*r**4+r**2*v-2*r*t*u+t**3
A,C,D,E=s.symbols('A C D E',real=True)
normal=s.expand(W.subs({r:A*q**s.Rational(3,2),t:C*q**2,u:D*q**s.Rational(5,2),v:E*q**3})/q**6)
complete=(D-A*(6+C))**2+12-24*C+7*C**2+C**3+E*(2-C+A**2)-A**2*(12+C**2)-9*A**4
assert s.simplify(normal-complete)==0
lower=s.Rational(130,27)-s.Rational(9,16)-s.Rational(109,36)-s.Rational(9,16)
assert lower==s.Rational(143,216)>0
# Direct symbolic local derivative/Hankel determinants with the l1 gauge removed.
l=s.symbols('l1:7');P=[s.Integer(1)]
for _ in range(6):P.append(s.expand(sum(s.diff(P[-1],l[j])*l[j+1] for j in range(5))-l[0]*P[-1]))
H=s.Matrix(4,4,lambda i,j:P[i+j].subs(l[0],0))
assert s.expand(H.det()-W.subs({q:l[1],r:l[2],t:l[3],u:l[4],v:l[5]}))==0
# Certificate cover and exact positive endpoint checks, not floating point comparisons.
rep=json.loads((B/'source_cert_results.json').read_text());rows=json.loads((B/'source_cert_rows.json').read_text())
assert rep['finite_pass'] and rep['outer_pass'] and not rep['failed_cells']
assert len(rows)==2048
assert F(rows[0][0])==F(31,10) and F(rows[-1][1])==8
for a,b in zip(rows,rows[1:]):assert F(a[1])==F(b[0])
threshold=[F(13,20),F(35),F(54),F(120),F(38),F(862)]
S=1<<144
for row in rows:
 assert F(row[0])<F(row[1])
 for z,c in zip(row[2:],threshold):assert F(int(z),S)>c
for z in rep['outer_positive_margins'].values():assert F(z)>0
# Pair block determinants for equispaced points.
a,b,c=s.symbols('a b c')
G=s.Matrix([[1,a,b,c],[a,1,a,b],[b,a,1,a],[c,b,a,1]])
Eblock=s.Matrix([[1+c,a+b],[a+b,1+a]])
Oblock=s.Matrix([[1-c,a-b],[a-b,1-a]])
assert s.expand(G.det()-Eblock.det()*Oblock.det())==0
out={'status':'PASS','W4_normalized_lower':'143/216','full_interval_cover_cells':len(rows),'no_failed_cells':True,'finite_exact_margin_thresholds':list(map(str,threshold)),'outer_positive':True,'prior_three_point_check':'separately rerun; not a dependency of this four-point certificate','scope':'symbolic identities and complete rational interval scalar certificate, not Lean or independent analytic review'}
(B/'final_algebra_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
