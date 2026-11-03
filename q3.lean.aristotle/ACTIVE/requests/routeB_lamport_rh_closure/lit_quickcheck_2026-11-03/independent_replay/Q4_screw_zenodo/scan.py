"""Independent prime-side diagnostic. No zero data; not an interval proof."""
import math,json
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
from scipy.special import polygamma
import mpmath as mp
N=100000
out=Path(__file__).resolve().parent
sieve=np.ones(N+1,dtype=bool);sieve[:2]=False
for p in range(2,math.isqrt(N)+1):
 if sieve[p]: sieve[p*p::p]=False
atoms=[]
for p in np.flatnonzero(sieve):
 n=int(p)
 while n<=N:
  atoms.append((n,math.log(int(p))/math.sqrt(n)))
  n*=int(p)
atoms.sort()
c=-float(mp.euler)-math.log(8*math.pi)-math.pi/2
Sinfty=float(polygamma(1,.25))/4

def smooth(x):
 t=math.log(x)
 # Tail S_infty-S(t); converges rapidly at all event x>=2.
 tail=0.;k=0
 while True:
  a=2*k+.5; term=math.exp(-a*t)/(a*a);tail+=term;k+=1
  if term<1e-17:break
 return c*t/2+Sinfty-tail+4*(math.sqrt(x)+1/math.sqrt(x)-2)
def d0(x):
 q=1/math.sqrt(x)
 return c/2+math.atanh(q)+math.atan(q)+2*(1/q-q)
B=D=0.; candidates=[]; stationary=[]
for j,(n,w) in enumerate(atoms):
 B+=w;D+=w*math.log(n)
 candidates.append((smooth(n)-B*math.log(n)+D,float(n),'prime_power'))
 b=atoms[j+1][0] if j+1<len(atoms) else N
 if b>n and d0(n)-B<0<d0(b)-B:
  r=brentq(lambda x:d0(x)-B,n,b,xtol=1e-10)
  v=smooth(r)-B*math.log(r)+D
  candidates.append((v,r,'interior_stationary'));stationary.append((v,r,n,b))
# Independently handle (1,2), where smooth second derivative changes sign once.
plastic=brentq(lambda x:x**3-x-1,1,2)
for a,b in [(1+1e-12,plastic),(plastic,2)]:
 if d0(a)*d0(b)<0:
  r=brentq(d0,a,b)
  candidates.append((smooth(r),r,'initial_stationary'))
minimum=min(candidates)
mp.mp.dps=80
v,x,kind=minimum
xx=mp.mpf(str(x));t=mp.log(xx)
Bb=mp.mpf(0);Dd=mp.mpf(0)
# high precision independent von Mangoldt weights from integer factorization event generation
for n,w in atoms:
 if n>x:break
 # recover prime base exactly from sieve primes
 for k in range(1,int(math.log(n,2))+1):
  p=round(n**(1/k))
  if p>=2 and p<=N and sieve[p] and p**k==n:break
 ww=mp.log(int(p))/mp.sqrt(n);Bb+=ww;Dd+=ww*mp.log(n)
cc=-mp.euler-mp.log(8*mp.pi)-mp.pi/2
S=mp.polygamma(1,mp.mpf('.25'))/4-mp.e**(-t/2)*mp.lerchphi(mp.e**(-2*t),2,mp.mpf('.25'))/4
vv=cc*t/2+S+4*(mp.sqrt(xx)+1/mp.sqrt(xx)-2)-Bb*t+Dd
res={'status':'FINITE_NUMERICAL_DIAGNOSTIC','N':N,'atom_count':len(atoms),'stationary_count':len(stationary),'minimum_candidate':{'Psi_float':v,'x':x,'t':math.log(x),'kind':kind,'Psi_mp80':str(vv)},'minimum_stationary':min(stationary) if stationary else None,'origin_note':'Psi(0)=0; infimum on open (0,log N] is at most 0. Reported minimum is among nonzero event/stationary candidates, not a positive global minimum.','external_P6':'NOT_TESTED_SOURCE_UNREACHABLE','proof_status':'DIAGNOSTIC_NEVER_A_PROOF'}
(out/'scan.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
