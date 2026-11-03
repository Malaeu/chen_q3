"""Independent MP physical-form evaluation of a published fixed polynomial witness.
DIAGNOSTIC_NEVER_A_PROOF; no interval arithmetic and no zero-side positivity.
"""
import json,mpmath as mp,time,sys
from pathlib import Path
mp.mp.dps=80
ROOT=Path(__file__).resolve().parent
z=json.loads((ROOT/'published/semilocal/results/polyupper_P2_L11147_10000_D61_p1.json').read_text())
L=mp.mpf(11147)/10000;a=L/2;D=61
coef=[mp.mpf(0)]*(D+1)
for degree,c in zip(z['degrees'],z['coeffs']):
 c=mp.mpf(c)*mp.sqrt((2*degree+1)/L)
 for k in range(degree//2+1):
  power=degree-2*k
  coef[power]+=c*(-1)**k*mp.factorial(2*degree-2*k)/(2**degree*mp.factorial(k)*mp.factorial(degree-k)*mp.factorial(power))
def f(x):return mp.polyval(list(reversed(coef)),x/a)
xs,ws=mp.gauss_quadrature(64,'legendre')
def corr(u):
 half=(L-u)/2;mid=u/2
 if half<=0:return mp.mpf(0)
 return half*mp.fsum(w*f(mid+half*x)*f(mid+half*x-u) for x,w in zip(xs,ws))
g0=mp.fsum(mp.mpf(c)**2 for c in z['coeffs'])
Am=a*mp.fsum(w*f(a*x)*mp.exp(a*x/2) for x,w in zip(xs,ws));Ap=a*mp.fsum(w*f(a*x)*mp.exp(-a*x/2) for x,w in zip(xs,ws))
order=int(sys.argv[1]) if len(sys.argv)>1 else 24
xx,ww=mp.gauss_quadrature(order,'legendre');t0=time.monotonic();arch=mp.mpf(0)
for p in range(8):
 for x,w in zip(xx,ww):
  u=L*(p+(x+1)/2)/8
  arch+=L*w/16*mp.exp(-u/2)/(-mp.expm1(-2*u))*(2*g0-2*corr(u))
tail=mp.atanh(mp.exp(-L/2))+mp.atan(mp.exp(-L/2))
arch+=2*tail*g0
const=mp.euler+mp.log(8*mp.pi)+mp.pi/2
prime=2*mp.log(2)/mp.sqrt(2)*corr(mp.log(2))
value=arch-const*g0-prime+2*Ap*Am
out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',dps=80,outer_panels=8,outer_GL=order,inner_GL=64,coefficient_source='published P2 upper JSON, fixed vector; independent physical form',norm=mp.nstr(g0,65),arch=mp.nstr(arch,65),constant=mp.nstr(-const*g0,65),prime=mp.nstr(-prime,65),pole=mp.nstr(2*Ap*Am,65),Q=mp.nstr(value,65),seconds=time.monotonic()-t0)
(ROOT/f'independent_witness_GL{order}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
