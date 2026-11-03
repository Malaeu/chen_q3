"""Independent manufactured numerators exercise real, nonreal and imaginary census."""
from pathlib import Path
import json,time,sys
import mpmath as mp
sys.path.insert(0,str(Path(__file__).resolve().parent))
from census import isolate,direct,decimal
from scipy.optimize import linear_sum_assignment
import numpy as np
mp.mp.dps=200
checks=[]
for m,parity in [(16,'even'),(16,'odd'),(64,'even')]:
 c=['1']+['0']*(m if parity=='even' else m-1)
 rr,info=isolate(c,m,parity)
 expected=[mp.mpf(n*n)/(m*m) for n in range(1 if parity=='even' else 2,m+1)]
 observed=[mp.mpc(decimal(u.real),decimal(u.imag)) for u in rr]
 a,b=linear_sum_assignment(np.array([[float(abs(x-y)) for y in expected] for x in observed]));err=max(abs(observed[i]-expected[j]) for i,j in zip(a,b))
 checks.append(dict(control=f'{parity}_single_mode_m{m}',expected_degree=len(expected),observed_count=len(rr),max_u_error=mp.nstr(err,30),**info));assert err<mp.mpf('1e-38')
m=16;a=[mp.mpf(n*n)/(m*m) for n in range(1,m+1)]
expected=[mp.mpf('-.1'),mp.mpc('.13','.004'),mp.mpc('.13','-.004')]+[(mp.mpf(n)+mp.mpf('.37'))**2/m**2 for n in range(3,m)]
def P(x):return mp.fprod(x-r for r in expected)
def D(x):return mp.fprod(x-r for r in a)
c=[mp.re(P(0)/D(0))]
for n,x in enumerate(a):
 dp=mp.fprod(x-r for j,r in enumerate(a) if j!=n)
 c.append(mp.re(P(x)/(mp.sqrt(2)*x*dp)))
rr,info=isolate([mp.nstr(v,190) for v in c],m,'even');observed=[mp.mpc(decimal(u.real),decimal(u.imag)) for u in rr]
aa,bb=linear_sum_assignment(np.array([[float(abs(x-y)) for y in expected] for x in observed]));err=max(abs(observed[i]-expected[j]) for i,j in zip(aa,bb))
real=sum(r.imag.contains(0) and r.real>0 for r in rr);neg=sum(r.imag.contains(0) and r.real<0 for r in rr);nonreal=sum(not r.imag.contains(0) for r in rr)
L=mp.log(m);Om=2*mp.pi*m/L;res=max(abs(direct(c,mp.sqrt(u)*Om,L,'even')) for u in expected)
checks.append(dict(control='manufactured_mixed_m16',expected_degree=len(expected),observed_count=len(rr),real_positive=real,pure_imaginary=neg,nonreal=nonreal,max_u_error=mp.nstr(err,30),max_direct_F_at_expected=mp.nstr(res,30),**info));assert (real,neg,nonreal)==(13,1,2);assert err<mp.mpf('1e-38')
result=dict(status='PASS',checks=checks,scope='Manufactured finite coefficients and known polynomial roots; validates indexing, parity, real/imaginary/complex separation and complete degree accounting. Does not validate spectral ground-vector accuracy.')
Path(__file__).with_name('controls.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
