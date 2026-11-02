"""Actual global completed log derivative, NOT finite-end impedance.
DIAGNOSTIC_NEVER_A_PROOF; finite source evaluations, no RH inference.
"""
from pathlib import Path
import mpmath as mp,json,sys
from curve import coefficients
mp.mp.dps=80;P=Path(__file__).resolve().parent;IN=Path(sys.argv[1])
tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);a=[mp.mpf(1),tau,-tau,mp.mpf(-1)]
def DD(s):return mp.power(5,-s)*mp.fsum(a[r-1]*mp.zeta(s,mp.mpf(r)/5) for r in range(1,5))
def logder(s,world):
 if world=='zeta':
  if s==1:return 1+mp.euler/2-mp.log(4*mp.pi)/2
  return 1/s+1/(s-1)-mp.log(mp.pi)/2+mp.digamma(s/2)/2+mp.diff(mp.zeta,s)/mp.zeta(s)
 if s==1:
  d0=-mp.fsum(a[r-1]*mp.digamma(mp.mpf(r)/5) for r in range(1,5))/5
  d1=-mp.log(5)*d0-mp.fsum(a[r-1]*mp.stieltjes(1,mp.mpf(r)/5) for r in range(1,5))/5
 else:d0=DD(s);d1=mp.diff(DD,s)
 return mp.log(5/mp.pi)/2+mp.digamma((s+1)/2)/2+d1/d0
zero=json.loads((IN/'dh_zeros_extended.json').read_text())['off_line_pairs'][0]
gamma=mp.mpf(zero['gamma']);eta=mp.mpf(zero['sigma_right'])-mp.mpf('.5')
zs=[mp.j/2,mp.j,2*mp.j,gamma+mp.j*3*eta/4];rows=[]
for world in ['zeta','dh']:
 for z in zs:
  q=mp.j*logder(mp.mpf('.5')-mp.j*z,world)
  rows.append({'world':world,'z_real':mp.nstr(mp.re(z),75),'z_imag':mp.nstr(mp.im(z),75),'Q_real':mp.nstr(mp.re(q),75),'Q_imag':mp.nstr(mp.im(q),75),'scope':'GLOBAL_COMPLETED_LOGDERIVATIVE_NOT_FINITE_END_IMPEDANCE'})
print(json.dumps({'status':'DIAGNOSTIC_NEVER_A_PROOF','dps':80,'rows':rows,'finite_points_do_not_certify_Herglotz':True,'Hermitian_resolvent_warning':'Im[v*(C-zI)^-1v]=Im(z)*||(C-zI)^-1v||^2 for every Hermitian C, even indefinite'},indent=2))
