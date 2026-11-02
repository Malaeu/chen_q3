"""Residual at serialized125-digit roots, distinct from internal refined-root residual."""
import csv,json
from pathlib import Path
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=180;rows=list(csv.DictReader((P/'roots.csv').open()))
for m,dps,order in [(16,180,160),(24,180,160),(32,160,128),(40,180,160)]:
 d=json.loads((P/f'cell_m{m}_dps{dps}_gl{order}.json').read_text());V=mp.matrix(d['V']);L=mp.log(m);b=L/2;om=2*mp.pi/L
 for r in rows:
  if int(r['m'])!=m:continue
  i=int(r['i']);t=mp.mpf(r['t_root']);c=[V[n,i]*(1 if n==0 else mp.sqrt(2)) for n in range(m+1)]
  if min(abs(t-n*om) for n in range(m+1))<mp.mpf('1e-40'):
   val=mp.fsum(c[n]*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-n*om)*b)+mp.sinc((t+n*om)*b)) for n in range(m+1))
  else:val=2*t*mp.sin(t*b)/mp.sqrt(L)*mp.fsum(c[n]/(t*t-(n*om)**2) for n in range(m+1))
  r['serialized_F_residual']=mp.nstr(abs(val),50);r['serialized_position_residual']=mp.nstr(abs(val/mp.mpf(r['direct_Fprime'])),50)
with (P/'roots.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
print('max serialized position residual',mp.nstr(max(mp.mpf(r['serialized_position_residual']) for r in rows),30))
