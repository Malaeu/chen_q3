"""MP80 early-interval stationary candidates; not outward intervals."""
from pathlib import Path
import mpmath as m,json
m.mp.dps=80;P=Path(__file__).resolve().parent
alpha=(m.euler+m.log(8*m.pi)+m.pi/2)/2;C=m.pi**2/4+2*m.catalan-8
x=m.findroot(lambda x:x**3-x-1,(1,2));tc=m.log(x)
def der(t):
 r=m.exp(-t/2);return 4*m.sinh(t/2)-alpha+m.atanh(r)+m.atan(r)
def psi(t):return 4*m.exp(t/2)-alpha*t+C-4*m.fsum(m.exp(-(4*k+1)*t/2)/(4*k+1)**2 for k in range(1,1500))
roots=[m.findroot(der,(m.mpf('1e-6'),tc),solver='anderson'),m.findroot(der,(tc,m.log(2)),solver='anderson')]
result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',turning_point=m.nstr(tc,70),minimum_first_derivative=m.nstr(der(tc),70),stationary=[dict(t=m.nstr(t,70),psi=m.nstr(psi(t),70),type=['maximum','minimum'][i]) for i,t in enumerate(roots)],origin_limit='0; positive small-t asymptotic -t log(t)/2 + O(t)',note='MP80 candidates, not outward interval certificate. The unique sign change of A second derivative follows x^3-x-1.')
(P/'early_interval.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
