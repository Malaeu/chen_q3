"""Independent diagnostic crosswalk: direct integrals, exact source scalar g.
No interval positivity conclusion is inferred from these numerical controls.
"""
from pathlib import Path
import json,mpmath as m
m.mp.dps=80;L=m.log(3);b=L/2
rows=[]
for n in range(4):
 phi=lambda x:m.sqrt((2*n+1)/L)*m.legendre(n,x/b)
 for t in [m.mpf('.7'),m.mpf(7)]:
  numeric=m.quad(lambda x:phi(x)*m.exp(-m.j*t*x),[-b,b])
  js=m.sqrt(m.pi/(2*b*t))*m.besselj(n+m.mpf('.5'),b*t)
  expected=(-m.j)**n*m.sqrt(L*(2*n+1))*js
  rows.append(dict(n=n,t=str(t),Fourier_error=m.nstr(abs(numeric-expected),12)))
 pole=m.quad(lambda x:phi(x)*m.sqrt(2)*(m.cosh(x/2) if n%2==0 else m.sinh(x/2)),[-b,b])
 isph=m.sqrt(m.pi/(2*b/2))*m.besseli(n+m.mpf('.5'),b/2)
 rows.append(dict(n=n,pole_error=m.nstr(abs(pole-m.sqrt(2*L*(2*n+1))*isph),12)))
c=m.euler+m.log(8*m.pi)+m.pi/2
# Constant-test normalization from direct source integrals with explicit outside tail.
j=lambda x:m.exp(-x/2)/(-m.expm1(-2*x))
arch=2*m.quad(lambda x:j(x)*x,[0,L/2,L])+2*L*(m.atanh(m.exp(-L/2))+m.atan(m.exp(-L/2)))
prime=-2*m.log(2)/m.sqrt(2)*(L-m.log(2));pole=32*m.sinh(L/4)**2
physical=arch-c*L+prime+pole
# Independent scalar g from its closed dilogarithm series, not the generator.
x=m.exp(-L/2)
tail=m.polylog(2,x)-m.polylog(2,-x)+2*m.im(m.polylog(2,m.j*x))
g=c*L/2-m.polygamma(1,m.mpf('.25'))/4+tail-16*m.sinh(L/4)**2+m.log(2)/m.sqrt(2)*(L-m.log(2))
control=(physical+prime)/L
out=dict(dps=80,columns=rows,indicator_physical_W=m.nstr(physical,65),kernel_diagonal_minus2g=m.nstr(-2*g,65),indicator_crosswalk_error=m.nstr(abs(physical+2*g),12),doubled_prime_unit_constant=m.nstr(control,65),doubled_prime_below_minus23over100=bool(control<-m.mpf(23)/100))
assert abs(physical+2*g)<m.mpf('1e-70') and control<-m.mpf(23)/100
assert max(m.mpf(r.get('Fourier_error',r.get('pole_error'))) for r in rows)<m.mpf('1e-70')
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
