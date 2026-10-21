"""Profile-transform normalization checks only; no prime/CCM spectral calculation."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import mpmath as mp
import json,hashlib
mp.mp.dps=60
h=[F(0)]*4+[F(1),F(-4),F(6),F(-4),F(1)]
def der(a):return [F(i)*a[i] for i in range(1,len(a))] or [F(0)]
h2=der(der(h)); g=[(h2[i] if i<len(h2) else F(0))-h[i]/4 for i in range(len(h))]
def mpq(x):return mp.mpf(x.numerator)/x.denominator
def val(a,x):return mp.fsum(mpq(v)*x**i for i,v in enumerate(a))
r=[F(0)]*(2*len(g))
for i,a in enumerate(g):
    for j,b in enumerate(g):r[i+j+1]+=a*b*F(factorial(i)*factorial(j),factorial(i+j+1))
def conv(q):return val(r,q if q<=1 else 2-q)
rows=[]
for tau in (mp.mpf(0),mp.mpf(1)/10,mp.mpf(3)/10):
    z=mp.mpf('0.5')+1j*tau
    Hh=mp.quad(lambda x:val(h,x)*mp.exp(-z*(x+1)),[0,1])
    Hg=mp.quad(lambda x:val(g,x)*mp.exp(-z*(x+1)),[0,1])
    Hr=mp.quad(lambda q:conv(q)*mp.exp(-z*(q+2)),[0,1,2])
    assert abs(Hg-(z*z-mp.mpf('0.25'))*Hh)<mp.mpf('1e-50')
    assert abs(Hr-Hg*Hg)<mp.mpf('1e-50')
    n2=mpq(F(3041,628320))
    if tau:
        L=mp.mpf(40) # transform diagnostic, not a production CCM cell
        phase=mp.exp(1j*tau*L)*Hg**2/abs(Hg)**2
        ray=mp.re(mp.exp(1j*tau*L)*mp.conj(phase)*Hr)/n2
        assert ray>0 and abs(ray-abs(Hg)**2/n2)<mp.mpf('1e-48')
    else:
        ray=mp.re(Hr)/n2
        assert abs(Hg)<mp.mpf('1e-50') and abs(ray)<mp.mpf('1e-48')
    rows.append({'tau':str(tau),'filter_identity_error':str(abs(Hg-(z*z-mp.mpf('.25'))*Hh)),
                 'convolution_laplace_error':str(abs(Hr-Hg**2)),
                 'normalized_continuous_cross_coefficient':str(ray)})
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','cases':len(rows),'decimal_digits':60,'rows':rows,
     'scope':'Explicit compact profile transforms only; no prime sums, CCM spectra, or asymptotic verification.',
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
