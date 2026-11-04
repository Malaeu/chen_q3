"""Independent exact algebra and bounded scalar diagnostics; never a proof backend."""
import sympy as s
import mpmath as mp
import json,hashlib
from pathlib import Path
OUT=Path(__file__).resolve().parent
mp.mp.dps=80
g,e,o,t,a=s.symbols('gamma eta omega t a',real=True)
exact={}
exact['complex_denominator_slack']=s.simplify(((g*g-e*e-o*o)**2+4*g*g*e*e)-(g*g-o*o)**2-2*e*e*(g*g+o*o)-e**4)==0
v=(t*t+s.Rational(1,4))/(t*t-a*a)**2
exact['mode_derivative']=s.simplify(s.diff(v,t)+2*t*(t*t+a*a+s.Rational(1,2))/(t*t-a*a)**3)==0
r=s.symbols('r',positive=True);K=s.symbols('K',integer=True,nonnegative=True)
exact['geometric_tail']=s.simplify(r**K*((K+1)/(1-r)+r/(1-r)**2)-r**K*((K+1)-K*r)/(1-r)**2)==0
# Explicit scalar Rosser monotonicity: R/log=.137+.443log(u)/u+1.588/u.
u=s.symbols('u',positive=True)
ratio=s.Rational(137,1000)+s.Rational(443,1000)*s.log(u)/u+s.Rational(1588,1000)/u
exact['Rosser_ratio_derivative']=s.simplify(s.diff(ratio,u)-(s.Rational(443,1000)*(1-s.log(u))-s.Rational(1588,1000))/u**2)==0
zerr=26*mp.exp(-mp.pi)/(mp.pi*(1-mp.exp(-3*mp.pi)))
L=mp.log(300);kap=1+(1+mp.log(L))/(4*L);T=kap*2*mp.pi*300/L
rr=lambda t:mp.mpf('.137')+mp.mpf('.443')*mp.log(mp.log(t))/mp.log(t)+mp.mpf('1.588')/mp.log(t)
sig=L+mp.mpf('.2');F=4*mp.mpf('895.9')/sig-4*mp.mpf('12.5')/sig-((mp.sqrt(5481)+mp.mpf('12.5'))/sig)**2
# Test analytic EM remainder on points spanning needed m300 frequencies.
ber=[mp.bernoulli(2*k)for k in range(1,13)];tests=[]
for y in [0,1,10,100,400]:
 Z=mp.mpc(mp.mpf('32.25'),y)
 ps=mp.log(Z)-1/(2*Z)-mp.fsum(ber[k-1]/(2*k*Z**(2*k))for k in range(1,13))
 tr=1/Z+1/(2*Z**2)+mp.fsum(ber[k-1]/Z**(2*k+1)for k in range(1,13))
 bp=abs(ber[-1])/(24*Z.real**24);bt=abs(ber[-1])/Z.real**25
 tests.append(dict(imag=y,psi_error_over_bound=float(abs(mp.digamma(Z)-ps)/bp),trigamma_error_over_bound=float(abs(mp.polygamma(1,Z)-tr)/bt)))
assert all(exact.values())and zerr<mp.mpf('.5')and rr(T)<mp.mpf('.55')
assert all(v['psi_error_over_bound']<1 and v['trigamma_error_over_bound']<1 for v in tests)
res=dict(status='TAIL_PAPER_AUDIT_NO_COUNTEREXAMPLE_FOUND',exact_algebra=exact,zero_free_error=mp.nstr(zerr,50),T=mp.nstr(T,50),Rosser_R_over_log_T=mp.nstr(rr(T),50),safe_score=mp.nstr(F,50),simple_real_lower=mp.nstr(F-370,50),distinct_real_lower=mp.nstr((F-185)/2,50),EM_point_diagnostics=tests,interval_certificate=False,external_Rosser_theorem_reproved=False,input_sha256=hashlib.sha256((OUT/'INPUT_VERDICT.md').read_bytes()).hexdigest())
(OUT/'tail_audit_checks.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
