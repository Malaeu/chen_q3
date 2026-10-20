"""Small floating-point convention checks, not interval or spectral certificates."""
from pathlib import Path
import math, cmath, hashlib, json
from scipy.integrate import quad
rows=[]

def cquad(fn, lo, hi):
    return complex(quad(lambda t:fn(t).real,lo,hi,epsabs=1e-12,epsrel=1e-12,limit=150)[0],
                   quad(lambda t:fn(t).imag,lo,hi,epsabs=1e-12,epsrel=1e-12,limit=150)[0])

for power in (64,128,192):
    L=power*math.log(2); w0=2*math.pi/L; M=2**(power//64)
    odd={1:(.25+w0*w0)*math.sqrt(L)/(2j),-1:-(.25+w0*w0)*math.sqrt(L)/(2j),
         2:-(.25+4*w0*w0)*math.sqrt(L)/(4j),-2:(.25+4*w0*w0)*math.sqrt(L)/(4j)}
    even={0:-.75*math.sqrt(L),1:(1+4*w0*w0)*math.sqrt(L)/2,-1:(1+4*w0*w0)*math.sqrt(L)/2,
          2:-(.25+4*w0*w0)*math.sqrt(L)/2,-2:-(.25+4*w0*w0)*math.sqrt(L)/2}
    for kind in ('odd','even','mixed'):
        raw=odd if kind=='odd' else even if kind=='even' else {j:even.get(j,0)+1j*odd.get(j,0) for j in range(-2,3)}
        norm=math.sqrt(sum(abs(v)**2 for v in raw.values()))
        c={j:v/norm for j,v in raw.items()}
        def f(t):return sum(v*cmath.exp(1j*j*w0*t) for j,v in c.items())/math.sqrt(L)
        def H(z):return (1-cmath.exp(-z*L))/math.sqrt(L)*sum(v/(z-1j*j*w0) for j,v in c.items())
        z=.375+1j*(1/3+1.5*w0)
        hd=cquad(lambda t:f(t)*cmath.exp(-z*t),0,L)
        hr=cquad(lambda t:f(L-t)*cmath.exp(-z*t),0,L)
        # Compare after removing the large exp(Re(z)*L) factor, not before.
        Fscaled=cquad(lambda t:f(t)*cmath.exp(z*(t-L)),0,L)
        partner=H(z.conjugate())
        a=2*(Fscaled*partner.conjugate()).real
        b=2*(hr*partner.conjugate()).real
        res=cquad(lambda t:f(t)*cmath.exp(-1j*w0*t),0,L)
        eH=abs(hd-H(z)); ePair=abs(a-b); eRes=abs(res-math.sqrt(L)*c.get(1,0))
        emom=[]
        for r in (-.5,.5):
            # Moment divided by its common exponential endpoint factor.
            emom.append(abs(sum(v/(r+1j*j*w0) for j,v in c.items())/math.sqrt(L)))
        assert eH<2e-10 and ePair<2e-10 and eRes<2e-10 and max(emom)<2e-10
        rows.append({'m':'2^'+str(power),'epsilon':'1/64','M=R':M,'profile':kind,
                     'Laplace_abs_error':eH,'scaled_pair_abs_error':ePair,
                     'removable_resonance_abs_error':eRes,'moment_coefficient_abs_error':max(emom)})
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','cases':len(rows),'precision':'binary64',
     'scope':'transform conventions on original constrained profiles at legal schedules; no primes, zeta zeros or CCM spectra evaluated',
     'prior_attempt':'A 70-digit, 9-case mpmath quadrature exceeded the 45s execution limit and produced no completed result; not counted as PASS.',
     'max_error':max(max(r['Laplace_abs_error'],r['scaled_pair_abs_error'],r['removable_resonance_abs_error'],r['moment_coefficient_abs_error']) for r in rows),
     'rows':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('laplace_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
