"""Independent basis transform check: rational, direct sinc, and physical integration."""
from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=180
zeros=[mp.mpf(r['gamma']) for r in csv.DictReader((P/'zeros.csv').open()) if mp.mpf(r['gamma'])<=400]
results=[]
for m in [16,24]:
 L=mp.log(m);b=L/2;omega=2*mp.pi/L;ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 maxerr=mp.mpf(0);where=None
 def direct(t,n):return ds[n]*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-n*omega)*b)+mp.sinc((t+n*omega)*b))
 def rational(t,n):return 2*ds[n]*t*mp.sin(t*b)/(mp.sqrt(L)*(t*t-(n*omega)**2))
 for k,t in enumerate(zeros,1):
  for n in range(m+1):
   err=abs(direct(t,n)-rational(t,n))
   if err>maxerr:maxerr=err;where=[k,n]
 nearest=min(range(len(zeros)),key=lambda k:min(abs(zeros[k]-n*omega) for n in range(m+1)))
 chosen=sorted(set([0,len(zeros)-1,nearest]));physical=[]
 for order in [96,128]:
  nodes,weights=mp.gauss_quadrature(order,'legendre');quad=[(b*(panel+(nodes[j]+1)/2)/8,b*weights[j]/16) for panel in range(8) for j in range(order)]
  basis=[[ds[n]*(-1)**n/mp.sqrt(L)*mp.cos(n*omega*x) for x,w in quad] for n in range(m+1)]
  for k in chosen:
   t=zeros[k];osc=[mp.cos(t*x) for x,w in quad]
   errors=[abs(2*mp.fsum(w*e*v for (x,w),e,v in zip(quad,basis[n],osc))-direct(t,n)) for n in range(m+1)]
   physical.append(dict(k=k+1,gamma=mp.nstr(t,180),order=order,panels=8,max_absolute_difference=mp.nstr(max(errors),80),worst_mode=max(range(m+1),key=lambda n:errors[n])))
 results.append(dict(m=m,zero_count=len(zeros),dps=180,max_rational_vs_sinc_difference=mp.nstr(maxerr,80),worst_location=where,selected_physical_integration=physical,normalization='E_kn=hat e_n(gamma_k), no 2pi factor, positive zeros only',scope='Numerical normalization and quadrature check, not interval certification'))
 print(m,mp.nstr(maxerr,12),flush=True)
 (P/'validation.json').write_text(json.dumps(results,indent=2)+'\n')
