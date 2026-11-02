"""Exact real-root count of the same rounded rational numerator polynomial."""
from pathlib import Path
import json
import sympy as s
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=180;x=s.Symbol('x')
for m,dps,order in [(16,180,160),(24,180,160),(32,160,128),(40,180,160)]:
 d=json.loads((P/f'cell_m{m}_dps{dps}_gl{order}.json').read_text());V=mp.matrix(d['V']);f=P/f'root_results_m{m}_dps{dps}.json';rows=json.loads(f.read_text());products=[]
 for n in range(m+1):
  p=s.Poly(1,x)
  for k in range(m+1):
   if k!=n:p*=s.Poly(x-s.Rational(k*k,m*m),x)
  products.append(p)
 for r in rows:
  i=r['i'];p=sum((s.Rational(mp.nstr(V[n,i]*(1 if n==0 else mp.sqrt(2)),100))*products[n] for n in range(m+1)),s.Poly(0,x));intervals=p.intervals();zero=sum(mult for (lo,hi),mult in intervals if lo==hi==0);pos=sum(mult for (lo,hi),mult in intervals if lo>=0 and hi>0);neg=sum(mult for (lo,hi),mult in intervals if hi<=0 and lo<0)
  r.update(polynomial_degree=int(p.degree()),positive_y_root_count=pos,negative_y_root_count=neg,zero_y_root_count=zero,polynomial_square_free=all(mult==1 for _,mult in intervals),nonreal_y_root_count=int(p.degree())-pos-neg-zero)
 f.write_text(json.dumps(rows,indent=2)+'\n');print(m,flush=True)
