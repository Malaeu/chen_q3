"""Independent piecewise exact-integration checks; no source matrices/scans."""
import json,math,cmath
from pathlib import Path
import numpy as np
OUT=Path(__file__).resolve().parent

def integral_exp(t,a,b):
 return (b-a)if abs(t)<1e-15 else (cmath.exp(1j*t*b)-cmath.exp(1j*t*a))/(1j*t)
def dirichlet(m,x):return sum(cmath.exp(1j*j*x)for j in range(-m,m+1)).real

def check(m,L,us,cs,arithmetic=False):
 js=np.arange(-m,m+1);freq=2*np.pi*js/L;breaks=sorted(set([-L/2,L/2]+[v for u in us for v in [-L/2+u,L/2-u]]));M=np.zeros((2*m+1,2*m+1),complex);energy=0.;evenenergy=0.;reflection=0.
 for a,b in zip(breaks[:-1],breaks[1:]):
  if b<=a:continue
  mid=(a+b)/2
  h=np.array([sum(c*((cmath.exp(1j*t*u)if mid+u<L/2 else 0)+(cmath.exp(-1j*t*u)if mid-u> -L/2 else 0))for u,c in zip(us,cs))for t in freq])
  energy+=(b-a)*float(np.sum(np.abs(h)**2))/L
  reflection+=sum((h[j]**2*integral_exp(2*freq[j],a,b)).real for j in range(len(js)))/L
  evenenergy+=(b-a)*abs(h[m])**2/L
  for j in range(m+1,2*m+1):evenenergy+=((b-a)*abs(h[j])**2+(h[j]**2*integral_exp(2*freq[j],a,b)).real)/L
  for k,tk in enumerate(freq):
   for j,tj in enumerate(freq):M[k,j]+=h[j]*integral_exp(tj-tk,a,b)/L
 rhs=2/L*sum(c*d*((L-max(u,v))*dirichlet(m,2*np.pi*(u-v)/L)+max(L-u-v,0)*dirichlet(m,2*np.pi*(u+v)/L))for u,c in zip(us,cs)for v,d in zip(us,cs))
 U=np.zeros((2*m+1,m+1));U[m,0]=1
 for j in range(1,m+1):U[m-j,j]=U[m+j,j]=(-1)**j/np.sqrt(2)
 E=U.T@M@U;frob=float(np.sum(np.abs(E)**2));leak=evenenergy-frob;beta=2/np.pi**2*(math.log(2*m+1)+2);C0=sum(abs(c)for c in cs)
 r=dict(m=m,L=L,shifts=us,coefficients=cs,full_energy=energy,eq3_4_rhs=rhs,eq3_4_error=energy-rhs,even_energy=evenenergy,even_compressed_frob2=frob,parity_identity_error=evenenergy-(energy+reflection)/2,parity_absolute_cost=abs(evenenergy-energy/2),parity_bound=8*C0*C0,even_leakage=leak,leakage_bound=4*beta*C0*C0,full_matrix_hermitian_residual=float(np.max(np.abs(M-M.conj().T))))
 if arithmetic:
  Q=sum(c*c*(1-u/L)for u,c in zip(us,cs));W=sum((n+1)*c*c*(L-u)for n,u,c in zip(range(2,m+1),us,cs));cross=sum(abs(c*d)for u,c in zip(us,cs)for v,d in zip(us,cs)if u+v<=L+1e-14);bL=1+L/(4*math.log(2));EB=1.5*W+bL*cross+(8+4*beta)*C0*C0
  gaps=[min(abs(u-v),L-abs(u-v))/L for i,u in enumerate(us)for v in us[i+1:]]
  nodegates=[]
  for i,u in enumerate(us):
   actual=min([min(abs(u-v),L-abs(u-v))/L for k,v in enumerate(us)if k!=i],default=math.inf);delta=1/((i+3)*L);nodegates.append(actual>=delta-1e-14)
  r.update(eq3_1_lhs=abs(frob-(2*m+1)*Q),eq3_1_bound=EB,eq3_1_pass=abs(frob-(2*m+1)*Q)<=EB+1e-10,eq3_5_pass=all(nodegates))
 return r

def main():
 rows=[];rng=np.random.default_rng(764321)
 for m in [1,2,3,5,10]:
  for us,cs in [([.5],[1.]),([.2,.7],[1.,-.7]),([.1,.4,.9],[.3,-1.,2.])]:rows.append(check(m,1.,us,cs))
 for m in range(2,21):
  L=math.log(m);us=[math.log(n)for n in range(2,m+1)]
  for it in range(3):rows.append(check(m,L,us,list(rng.uniform(-1,1,len(us))),True))
 diagtests=[]
 for m in range(2,21):
  L=math.log(m);beta=2/np.pi**2*(math.log(2*m+1)+2);bound=1+L/(4*math.log(2))+8+4*beta
  for n in range(2,m+1):
   r=check(m,L,[math.log(n)],[1.]);lhs=abs(r['even_compressed_frob2']-(2*m+1)*(1-math.log(n)/L));diagtests.append(dict(m=m,n=n,lhs=lhs,bound=bound,passed=lhs<=bound+1e-10))
 receipt=dict(diagonal_atom_cases=len(diagtests),all_eq3_2=all(r['passed']for r in diagtests),diagonal_atom_tests=diagtests,status='DIAGNOSTIC_NUMERIC_NOT_INTERVAL',counterexample_found=False,cases=len(rows),max_eq3_4_error=max(abs(r['eq3_4_error'])for r in rows),max_parity_identity_error=max(abs(r['parity_identity_error'])for r in rows),all_parity_bounds=all(r['parity_absolute_cost']<=r['parity_bound']+1e-9 for r in rows),all_leakage_bounds=all(-1e-9<=r['even_leakage']<=r['leakage_bound']+1e-9 for r in rows),all_arithmetic_3_1_and_3_5=all(r.get('eq3_1_pass',True)and r.get('eq3_5_pass',True)for r in rows),rows=rows)
 (OUT/'geometry_checks.json').write_text(json.dumps(receipt,indent=2,default=lambda x:x.item())+'\n');print({k:v for k,v in receipt.items()if k not in ['rows','diagonal_atom_tests']})
if __name__=='__main__':main()
