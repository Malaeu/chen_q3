"""Scalar uniform sampling cap, independent of source F2 and zero counts."""
import csv,json
from pathlib import Path
import mpmath as mp
mp.mp.dps=90
OUT=Path(__file__).resolve().parent
CENSUS=Path('/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03/source_inputs/zeta_zeros.csv')
G=mp.mpf(next(csv.DictReader(CENSUS.open()))['gamma'])
def peak(k):
 lo=2*k*mp.pi;hi=lo+mp.pi/2
 for _ in range(260):
  mid=(lo+hi)/2
  if mid*mp.cos(mid)-mp.sin(mid)>0:lo=mid
  else:hi=mid
 return (lo+hi)/2
rows=[]
for m in range(16,301):
 L=mp.log(m);x0=L*G;k=max(1,int(mp.floor(x0/(2*mp.pi))));x=peak(k)
 if x<x0:k+=1;x=peak(k)
 boundary=mp.sin(x0)/x0;pk=1/mp.sqrt(1+x*x);v=max(boundary,pk)
 # Later positive stationary heights strictly decrease; negative lobes <=0.
 sig=L*(1+v);loose=L+1/G
 assert L<sig<=loose
 rows.append(dict(m=m,L=mp.nstr(L,25),gamma_star=mp.nstr(G,90),x_boundary=mp.nstr(x0,25),next_positive_peak_k=k,next_positive_peak_x=mp.nstr(x,25),boundary_sinc=mp.nstr(boundary,25),peak_sinc=mp.nstr(pk,25),maximizer='boundary'if boundary>=pk else'next_positive_peak',sigma_sharp=mp.nstr(sig,25),sigma_uniform_sharp=mp.nstr(sig,25),sigma_L_plus_inverse_gamma=mp.nstr(loose,25),improvement=mp.nstr(loose-sig,25),scope='diagnostic gamma_star assumption; zeta only; NOT control height cap'))
with(OUT/'sigma_sharp.csv').open('w')as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
(OUT/'sigma_sharp.json').write_text(json.dumps(dict(status='SCALAR_DIAGNOSTIC_NOT_INTERVAL',rows=len(rows),gamma_star=str(G),formula='sup_{gamma>=gamma_star} [L+sin(L gamma)/gamma]',algorithm='boundary or next positive stationary peak; subsequent peak heights strictly decrease',zero_scan=False,source_moment_input=False,min_improvement=min(float(r['improvement'])for r in rows),max_improvement=max(float(r['improvement'])for r in rows)),indent=2)+'\n')
