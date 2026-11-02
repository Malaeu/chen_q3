"""Exact DH support via the formal Dirichlet logarithm; no zero threshold.
If log D(s)=sum c_n n^-s, then b_n=c_n log n. Polynomials are reduced
modulo the exact minimal polynomial of the source tau.
"""
from pathlib import Path
import sympy as s,json,math
P=Path(__file__).resolve().parent

def generate(M=300):
 t=s.Symbol('t');tau=(s.sqrt(10-2*s.sqrt(5))-2)/(s.sqrt(5)-1)
 mod=s.Poly(s.minimal_polynomial(tau,t),t,domain=s.QQ)
 zero=s.Poly(0,t,domain=s.QQ);A=[zero for _ in range(M+1)]
 for n in range(2,M+1):A[n]=s.Poly({0:0,1:1,2:t,3:-t,4:-1}[n%5],t,domain=s.QQ)
 F=A.copy();C=[zero for _ in range(M+1)]
 for k in range(1,int(math.log2(M))+1):
  weight=s.Rational((-1)**(k+1),k)
  for n in range(2,M+1):C[n]+=F[n]*weight
  H=[zero for _ in range(M+1)]
  for n in range(4,M+1):
   for d in range(2,n//2+1):
    if n%d==0:H[n]+=A[d]*F[n//d]
  F=H
 rows=[]
 for n in range(2,M+1):
  c=C[n].rem(mod);rows.append({'n':n,'c_n_polynomial':str(c.as_expr()),'coefficients_high_to_low':[str(a) for a in c.all_coeffs()],'exact_zero':bool(c.is_zero)})
 assert rows[4]['n']==6 and s.expand(s.sympify(rows[4]['c_n_polynomial'])-(1+t*t))==0
 data={'status':'EXACT_FINITE_DIRICHLET_LOG_SUPPORT','max_n':M,'tau_minimal_polynomial':str(mod.as_expr()),'tau_definition':'(sqrt(10-2sqrt(5))-2)/(sqrt(5)-1)','identity':'b_n = log(n)*[n^-s]log(D(s)); exact rational-polynomial Dirichlet convolution','zero_indices':[r['n'] for r in rows if r['exact_zero']],'rows':rows,'no_numerical_zero_threshold':True}
 (P/'DH_EXACT_COEFFICIENTS.json').write_text(json.dumps(data,indent=2)+'\n')
 print('Exact DH coefficient table',M,'minimal polynomial',mod.as_expr(),'zeros',len(data['zero_indices']))
if __name__=='__main__':generate()
