"""Independent mp real-space scalar replay. No external Python imported.
Legendre polynomial converted to monomials; autocorrelation integrated by exact-degree GL64.
"""
from pathlib import Path
import json,time
import mpmath as mp
P=Path(__file__).parent

def replay(dps=100,order=64,Lstr="1.1147"):
 mp.mp.dps=dps;d=json.loads((P/'upstream_polyupper_P2_L11147_10000_D61_p1.json').read_text());L=mp.mpf(Lstr);a=L/2
 # Legendre recurrence independently in polynomial coefficients (ascending).
 pol=[[mp.mpf(1)],[mp.mpf(0),mp.mpf(1)]]
 for n in range(1,61):
  z=[mp.mpf(0)]*(n+2)
  for k,v in enumerate(pol[n]):z[k+1]+=(2*n+1)*v/(n+1)
  for k,v in enumerate(pol[n-1]):z[k]-=n*v/(n+1)
  pol.append(z)
 c=[mp.mpf(0)]*62
 for n,v in zip(d['degrees'],d['coeffs']):
  wt=mp.mpf(v)*mp.sqrt((2*n+1)/(2*a))
  for k,u in enumerate(pol[n]):c[k]+=wt*u
 def f(x):return mp.polyval(c[::-1],x/a)
 x,w=mp.gauss_quadrature(64,'legendre')
 def corr(s):
  lo=s-a;hi=a;h=(hi-lo)/2;mid=(hi+lo)/2
  return h*mp.fsum(wi*f(mid+h*xi)*f(mid+h*xi-s) for xi,wi in zip(x,w))
 g0=mp.fsum(mp.mpf(v)**2 for v in d['coeffs'])
 pe=a*mp.fsum(wi*f(a*xi)*mp.exp(-a*xi/2) for xi,wi in zip(x,w));pole=-2*pe*pe
 gx,gw=mp.gauss_quadrature(order,'legendre');integ=mp.mpf(0)
 for panel in range(8):
  for xi,wi in zip(gx,gw):
   t=2*L*(panel+(xi+1)/2)/8
   integ+=L*wi/8*(g0*mp.exp(-t)-mp.exp(-t/4)*corr(t/2))/(-mp.expm1(-t))
 arch=-(mp.euler+mp.log(mp.pi))*g0-g0*mp.log(-mp.expm1(-2*L))+integ
 prime=-2*mp.log(2)/mp.sqrt(2)*corr(mp.log(2))
 row={k:mp.nstr(v,75) for k,v in dict(norm=g0,pole=pole,arch=arch,prime=prime,Q=pole+arch+prime).items()};row.update(L=Lstr,dps=dps,GL_inner=64,GL_outer=order,panels=8);print(json.dumps(row),flush=True);(P/f'independent_vector_L{Lstr}_dps{dps}.json').write_text(json.dumps(row,indent=2)+'\n')
if __name__=='__main__':
 import sys
 replay(int(sys.argv[1]) if len(sys.argv)>1 else 100,int(sys.argv[2]) if len(sys.argv)>2 else 64,sys.argv[3] if len(sys.argv)>3 else "1.1147")
