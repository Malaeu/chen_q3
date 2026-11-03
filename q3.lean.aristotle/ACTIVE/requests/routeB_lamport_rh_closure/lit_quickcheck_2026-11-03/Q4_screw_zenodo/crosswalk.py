"""20 fixed numerical checks of retrieved Proposition2.1 vs original source."""
from pathlib import Path
import mpmath as mp
import json,csv
P=Path(__file__).resolve().parent;mp.mp.dps=85
alpha=(mp.euler+mp.log(8*mp.pi)+mp.pi/2)/2;C0=mp.pi**2/4+2*mp.catalan-8
rows=[]
for i in range(1,21):
 t=mp.mpf(i)/20;x=mp.exp(t)
 arithmetic=mp.mpf(0)
 for n in range(2,int(mp.floor(x))+1):
  for p in range(2,n+1):
   if n%p==0:
    v=n
    while v%p==0:v//=p
    if v==1:arithmetic+=mp.log(p)/mp.sqrt(n)*(t-mp.log(n))
    break
 rem=mp.fsum(4*mp.exp(-(4*k+1)*t/2)/(4*k+1)**2 for k in range(1,3000))
 retrieved=4*mp.sqrt(x)-alpha*t+C0-rem-arithmetic
 original=4*(mp.exp(t/2)+mp.exp(-t/2)-2)-arithmetic+t*(mp.digamma(mp.mpf(1)/4)-mp.log(mp.pi))/2+(mp.pi**2+8*mp.catalan-mp.exp(-t/2)*mp.lerchphi(mp.exp(-2*t),2,mp.mpf(1)/4))/4
 err=abs(retrieved-original);assert err<mp.mpf('1e-60')
 rows.append(dict(t=str(t),retrieved=mp.nstr(retrieved,70),original=mp.nstr(original,70),absolute_difference=mp.nstr(err,20)))
with (P/'crosswalk.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
report=dict(status='FORMULA_MATCH_NUMERICAL_NOT_INTERVAL',points=20,max_absolute_difference=mp.nstr(max(mp.mpf(r['absolute_difference']) for r in rows),30),C0=mp.nstr(C0,80),alpha=mp.nstr(alpha,80),alpha_logderivative_error=mp.nstr(abs(alpha-mp.diff(mp.zeta,mp.mpf('.5'))/mp.zeta(mp.mpf('.5'))),30))
(P/'crosswalk.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
