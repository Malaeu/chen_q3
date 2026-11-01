"""Independent adaptive-integral spot checks of shared GL coefficients/moments."""
import json,sys,time
from pathlib import Path
import mpmath as mp
ROOT=next(p for p in Path(__file__).resolve().parents if (p/'docs/routeB_bus/thetagrade_2026-10-28/radical_rayleigh.py').exists())
sys.path.insert(0,str(ROOT/'docs/routeB_bus/thetagrade_2026-10-28'))
from radical_rayleigh import h
mp.mp.dps=80
L=mp.log(16);b=L/2
z,w=mp.gauss_quadrature(96,'legendre')
def nodes(lo,hi):
 for k in range(8):
  aa=lo+(hi-lo)*k/8;bb=lo+(hi-lo)*(k+1)/8
  for zz,ww in zip(z,w):yield (aa+bb)/2+(bb-aa)*zz/2,ww*(bb-aa)/2
xx=[(x,ww*h(x)) for x,ww in nodes(-b,b)]
sx=[(x,ww*mp.exp(x/2)/(2*mp.sinh(x))) for x,ww in nodes(mp.mpf(0),L)]
rows=[];start=time.monotonic()
for n in (16,36,76):
 om=2*mp.pi*n/L
 cg=mp.fsum(ww*mp.cos(om*(x+b)) for x,ww in xx)/mp.sqrt(L)
 ca=2*(-1)**n*mp.quad(lambda x:h(x)*mp.cos(om*x),mp.linspace(0,b,max(8,n)+1))/mp.sqrt(L)
 mg=mp.fsum(ww*mp.sin(om*x) for x,ww in sx)
 ma=mp.quad(lambda x:om/2 if not x else mp.exp(x/2)*mp.sin(om*x)/(2*mp.sinh(x)),mp.linspace(0,L,max(8,2*n)+1))
 row={'n':n,'coefficient_adaptive':mp.nstr(ca,65),'coefficient_GL96':mp.nstr(cg,65),'coefficient_abs_error':mp.nstr(abs(ca-cg),12),'coefficient_relative_error':mp.nstr(abs(ca-cg)/abs(ca),12),'moment_adaptive':mp.nstr(ma,65),'moment_GL96':mp.nstr(mg,65),'moment_abs_error':mp.nstr(abs(ma-mg),12),'seconds':round(time.monotonic()-start,3)}
 rows.append(row);print(json.dumps(row),flush=True)
 Path(__file__).with_suffix('.json').write_text(json.dumps(rows,indent=2)+'\n')
