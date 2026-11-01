"""DIAGNOSTIC_NEVER_A_PROOF: direct physical Fourier canary, no sinc formulas."""
from pathlib import Path
import json,hashlib,time
import mpmath as mp
mp.mp.dps=140
ROOT=next(p for p in Path(__file__).resolve().parents if (p/'docs/routeB_bus/lowcluster_2026-11-02/core.py').exists())
SRC=ROOT/'docs/routeB_bus/lowcluster_2026-11-02'
start=time.monotonic()
zeros={i:mp.im(mp.zetazero(i)) for i in (1,10)}
names=['core_m20_dps100_gl128.json','core_m24_dps100_gl128.json','core_m24_dps140_gl160.json']
data={n:json.loads((SRC/n).read_text()) for n in names}
reference=mp.matrix(data[names[2]]['V'])
rows=[]
for order in (192,224):
 nodes,weights=mp.gauss_quadrature(order,'legendre')
 for name in names:
  d=data[name];m=d['m'];L=mp.log(m);b=L/2;V=mp.matrix(d['V'])
  for col in (0,7):
   c=V[:,col]
   if m==24 and mp.fdot(c,reference[:,col])<0:c=-c
   vals={i:mp.mpf(0) for i in zeros};norm=mp.mpf(0)
   # Direct physical-space evaluation of the zero-extended Fourier series.
   for node,w in zip(nodes,weights):
    x=b*node
    f=mp.fsum(c[n]*(1 if n==0 else mp.sqrt(2))*(-1)**n*mp.cos(2*mp.pi*n*x/L)/mp.sqrt(L) for n in range(m+1))
    norm+=b*w*f*f
    for i,gamma in zeros.items():vals[i]+=b*w*f*mp.cos(gamma*x)
   rows.append({'source':name,'m':m,'column':col,'order':order,'norm_squared':mp.nstr(norm,140),'coefficient_norm_squared':mp.nstr(mp.fdot(c,c),140),'fourier':{str(i):mp.nstr(v,140) for i,v in vals.items()}})
   print(name,col,order,flush=True)
comparisons=[]
for col in (0,7):
 for zero in (1,10):
  def get(name,order):return mp.mpf(next(r for r in rows if r['source']==name and r['order']==order and r['column']==col)['fourier'][str(zero)])
  a=get(names[1],224);v=get(names[2],224);err=abs(a-v);qerr=abs(v-get(names[2],192))
  comparisons.append({'column':col,'zero':zero,'m24_source100':mp.nstr(a,100),'m24_source140':mp.nstr(v,140),'input_precision_difference':mp.nstr(err,80),'relative_input_precision_difference':mp.nstr(err/abs(v),80),'quadrature_difference_140source':mp.nstr(qerr,80)})
out={'status':'DIAGNOSTIC_NEVER_A_PROOF','evaluation_dps':140,'transform':'integral_-L/2^L/2 phi(x) exp(-itx) dx; real even cosine quadrature','basis':'e_n=d_n(-1)^n cos(2pi n x/L)/sqrt(L), d0=1,dn=sqrt2','zeros':{str(k):mp.nstr(v,140) for k,v in zeros.items()},'source_sha256':{n:hashlib.sha256((SRC/n).read_bytes()).hexdigest() for n in names},'rows':rows,'comparisons':comparisons,'seconds':time.monotonic()-start,'limitation':'Finite input vectors only; no assertion of exact nonzero samples for limiting functions.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
