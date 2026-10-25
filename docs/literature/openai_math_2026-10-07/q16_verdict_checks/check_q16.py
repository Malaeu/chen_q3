"""Exact finite algebra controls; not CCM asymptotic or spectral certificates."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from math import isqrt
import json, hashlib
import sympy as sp
R=Path(__file__).resolve().parent
stats=Counter()
x=sp.symbols('x',real=True)
r=10*x**3-15*x**4+6*x**5
assert sp.expand(sp.diff(r,x)-30*x**2*(1-x)**2)==0
assert sp.expand(sp.diff(r,x,2)-60*x*(1-x)*(1-2*x))==0
assert sp.Rational(15,8)<2 and sp.Rational(100,3)<36
stats['partition_derivative_bounds']=2
# Pointwise test detects the omitted factor 2 in the commutator return.
commutator_sum=4*sp.diff(r,x).subs(x,sp.Rational(1,2))
assert commutator_sum==sp.Rational(15,2) and commutator_sum>4 and commutator_sum<=8
stats['dropped_commutator_factor_detected']=1
for k in range(3):
 assert sp.simplify(sp.diff(r+1-r,x,k)-(1 if k==0 else 0))==0
 stats['partition_sums']=stats['partition_sums']+1
for a in (0,1):
 for k in (1,2):
  assert sp.diff(r,x,k).subs(x,a)==0
  stats['partition_endpoint_jets']+=1

def B(p):return sp.diff(p,x,2)-p/4
h=x**6*(1-x)**6;g=B(h)
assert sp.expand(B(r*h)+B((1-r)*h)-g)==0
assert sp.expand(B(r*h)-r*g-2*sp.diff(r,x)*sp.diff(h,x)-sp.diff(r,x,2)*h)==0
assert sp.expand(B(r*h)-r*g)!=0
stats['commutator_and_planted_omission']=3
for p in (h,r*h,(1-r)*h):
 for a in (0,1):
  for k in (0,1):
   assert sp.diff(p,x,k).subs(x,a)==0
   stats['packet_contact_IBP_boundary_jets']+=1
for n in range(4,9):
 h0=x**n*(1-x)**n;f0=B(h0)
 F=sp.integrate(sp.expand(f0*f0),(x,0,1))
 H=sp.integrate(sp.expand(h0*h0),(x,0,1))
 D=sp.integrate(sp.expand(sp.diff(h0,x)**2),(x,0,1))
 DD=sp.integrate(sp.expand(sp.diff(h0,x,2)**2),(x,0,1))
 assert F==DD+D/2+H/16 and H<=16*F and D<=F
 stats['primitive_energy_controls']+=1
N2=sp.integrate(sp.expand(g*g),(x,0,1))
assert N2==sp.Rational(370411,11898286400) and 0<N2<1
assert g.subs(x,sp.Rational(1,2))==-sp.Rational(193,16384)
y=sp.Rational(2499,10000)
b=y**4*(12*y+y*y/4-sp.Rational(30,2500))
assert b>sp.Rational(1,100)
stats['actual_compact_profile_constants']=3
for ell in (Q(1,8),Q(2,9),Q(1,2),Q(2),Q(8)):
 C=1+8/ell+48/ell**2
 assert C>=1
 stats['norm_return_constants']+=1
assert 1+8/Q(2,9)+48/Q(2,9)**2==1009
assert 1+8/Q(1,8)+48/Q(1,8)**2==3137
# log 2 = 2 atanh(1/3) > 2/3; no decimal log inequality.
assert Q(2,3)+Q(2,81)>3*Q(2,9)
stats['narrow_support_and_constants']=3
w,a=sp.symbols('w a',positive=True)
rat=-sp.Rational(3,4)/a+(1+4*w*w)*a/(a*a+w*w)-(sp.Rational(1,4)+4*w*w)*a/(a*a+4*w*w)
assert sp.factor(rat.subs(a,sp.Rational(1,2)))==0
assert sp.factor(sp.diff(rat,a).subs(a,sp.Rational(1,2)))==384*w**4/((4*w*w+1)*(16*w*w+1))
stats['naive_f_localization_loses_contact']=2
# Full mixed-sector reconstruction, including noncommuting linear maps.
for z in range(1,9):
 L0=sp.Matrix([[sp.Rational(1,z+2),sp.Rational(1,3)],[-sp.Rational(1,2),sp.Rational(z,2*z+3)]])
 L1=sp.Matrix([[sp.Rational(1,4),-sp.Rational(2,3)],[sp.Rational(1,5),-sp.Rational(1,z+1)]])
 L2=sp.eye(2)-L0-L1;ls=[L0,L1,L2]
 A=sp.Matrix([[z,sp.Rational(1,z+1)],[sp.Rational(1,z+1),-z-1]])
 whole=sum((u.T*A*v for u in ls for v in ls),sp.zeros(2))
 diag=sum((u.T*A*u for u in ls),sp.zeros(2))
 assert whole==A and diag!=A
 stats['full_mixed_matrix_reconstruction']=stats['full_mixed_matrix_reconstruction']+1
# Literal mu*log coefficients, before any kernel or absolute value.
N=128;fac=[Counter() for _ in range(N+1)]
for n in range(2,N+1):
 v=n
 for p in range(2,isqrt(n)+2):
  while v%p==0:fac[n][p]+=1;v//=p
 if v>1:fac[n][v]+=1
mu=[0]+[0 if any(e>1 for e in fac[n].values()) else (-1)**len(fac[n]) for n in range(1,N+1)]
for n in range(1,N+1):
 out=Counter()
 for d in range(1,n+1):
  if n%d==0:
   for p,e in fac[n//d].items():out[p]+=mu[d]*e
 out={p:e for p,e in out.items() if e}
 target={next(iter(fac[n])):1} if len(fac[n])==1 else {}
 assert out==target
 stats['full_actual_arithmetic_coefficients']+=1
# Lower-price constants are rational implications; PNT is not tested here.
assert Q(1,100)**4/Q(27)==Q(1,2700000000)
assert Q(1,2700000000)/2==Q(1,5400000000)
stats['obstruction_constant_arithmetic']=2
out={'status':'PASS_EXACT_LOCAL_ALGEBRA_NOT_ASYMPTOTIC','sympy':sp.__version__,'counts':dict(stats),
 'total_cases':sum(stats.values()),'profile_norm2':str(N2),'profile_interval_lower_bound':str(b),
 'full_CCM_spectra_computed':False,'PNT_numerically_certified':False,'lean_runs':0,'arb_runs':0,
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'registration_sha256':hashlib.sha256((R/'registration.json').read_bytes()).hexdigest()}
(R/'exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
