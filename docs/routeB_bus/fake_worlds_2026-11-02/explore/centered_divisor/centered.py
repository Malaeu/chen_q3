"""All-Lambda centered divisor Gram, exact finite floor-integral moments.
DIAGNOSTIC_NEVER_A_PROOF. Complete output continuum retained via preflight7.6.
"""
from pathlib import Path
from fractions import Fraction
from math import gcd
import json,csv,sys,hashlib,time
import mpmath as mp
import numpy as np
P=Path(__file__).resolve().parent;FAKE=P.parents[1];BUS=FAKE.parent
sys.path.insert(0,str(BUS/'phase_space_V'));from v_forms import mangoldt
QMAP={20:8,40:18,60:29,80:41,120:64}

def matrix_from_mom(C,SC,S,L):
 N=len(C)-1;ds=[mp.mpf(1)]+[mp.sqrt(2)]*N;M=mp.zeros(N+1)
 for i in range(N+1):
  M[i,i]=2*(C[i]-SC[i]/L)-(S[i]/(mp.pi*i) if i else 0)
  for k in range(i+1,N+1):M[i,k]=M[k,i]=ds[i]*ds[k]/mp.pi*(k*S[k]-i*S[i])/(i*i-k*k)
 return M

def atom_moments(N,L,atoms):
 C=[mp.mpf(0)]*(N+1);SC=C.copy();S=C.copy()
 for x,w in atoms:
  co=mp.cos(2*mp.pi*x/L);si=mp.sin(2*mp.pi*x/L);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(N+1):C[n]+=w*cn;SC[n]+=w*x*cn;S[n]+=w*sn;cn,sn=cn*co-sn*si,sn*co+cn*si
 return C,SC,S

def peak(f,L,grid_points=2001):
 N=f.rows-1;om=2*mp.pi/L;Omega=N*om;ds=[mp.mpf(1)]+[mp.sqrt(2)]*N
 # Stable sinc-based double grid supplies candidates; high-precision root refinement follows.
 ts=np.linspace(0,float(2*Omega),grid_points);ff=np.array([float(x) for x in f]);nn=np.arange(N+1);bb=float(L/2);ww=float(om)*nn
 vals=(np.sinc((ts[:,None]-ww)*bb/np.pi)+np.sinc((ts[:,None]+ww)*bb/np.pi))@(ff*np.array([float(x) for x in ds])*(-1.)**nn*bb/float(mp.sqrt(L)))
 candidates=[i for i in range(1,len(ts)-1) if abs(vals[i])>=abs(vals[i-1]) and abs(vals[i])>=abs(vals[i+1])]
 def sp(z):return (z*mp.cos(z)-mp.sin(z))/(z*z) if z else mp.mpf(0)
 def fun(t,der=False):
  if min(abs(t-n*om) for n in range(N+1))<mp.mpf('1e-35'):
   b=L/2
   return mp.fsum(f[n]*ds[n]*(-1)**n*b/mp.sqrt(L)*((b*sp((t-n*om)*b)+b*sp((t+n*om)*b)) if der else (mp.sinc((t-n*om)*b)+mp.sinc((t+n*om)*b))) for n in range(N+1))
  ss=mp.sin(t*L/2);cc=mp.cos(t*L/2)
  return mp.fsum(2*f[n]*ds[n]/mp.sqrt(L)*(((ss+t*L*cc/2)/(t*t-(n*om)**2)-2*t*t*ss/(t*t-(n*om)**2)**2) if der else t*ss/(t*t-(n*om)**2)) for n in range(N+1))
 options=[(mp.mpf(0),abs(fun(mp.mpf(0)))),(2*Omega,abs(fun(2*Omega)))];refined=0
 for i in candidates:
  a=mp.mpf(str(ts[i-1]));b=mp.mpf(str(ts[i+1]));da=fun(a,True);db=fun(b,True)
  if da*db<0:
   try:r=mp.findroot(lambda t:fun(t,True),(a,b),solver='anderson',tol=mp.mpf('1e-70'),maxsteps=100)
   except ValueError:continue
   if a<=r<=b:options.append((r,abs(fun(r))));refined+=1
 t,value=max(options,key=lambda x:x[1]);tail=4*mp.fsum(abs(f[n]*ds[n]) for n in range(N+1))/(3*Omega*mp.sqrt(L));modal=max(range(N+1),key=lambda n:abs(f[n]));return dict(t=t,t_over_Omega=t/Omega,amplitude=value,grid_interval=[0,2*Omega],grid_points=grid_points,stationary_candidates=len(candidates),refined_stationary=refined,tail_upper_bound_beyond_2Omega=tail,tail_bound_below_peak=bool(tail<value),largest_modal_index=modal,largest_modal_height=modal*om,largest_modal_height_over_Omega=mp.mpf(modal)/N)

def serial(v,digits):
 if isinstance(v,dict):return {k:serial(x,digits) for k,x in v.items()}
 if isinstance(v,(list,tuple)):return [serial(x,digits) for x in v]
 if isinstance(v,mp.matrix):return [[mp.nstr(v[i,j],digits) for j in range(v.cols)] for i in range(v.rows)]
 if isinstance(v,(mp.mpf,mp.mpc)):return mp.nstr(v,digits)
 return v

def run(m,dps=100,keep_dense=0):
 start=time.monotonic();mp.mp.dps=dps;L=mp.log(m);N=m;q=QMAP[m];source=FAKE/'ledger_diff/matched_cells'/f'zeta_m{m}_q{q}.json';d=json.loads(source.read_text());A=mp.matrix(d['A']);U=mp.matrix(d['U']);h=[mp.mpf(0)]
 for n in range(1,m+1):h.append(h[-1]+mp.log(n)/n)
 atoms=[]
 for a in range(2,m+1):
  if h[m//a]==0:continue
  for b in range(1,a):
   if gcd(a,b)==1:atoms.append((mp.log(mp.mpf(a)/b),h[m//a]/mp.sqrt(a*b)))
 raw=matrix_from_mom(*atom_moments(N,L,atoms),L)+h[m]*mp.eye(N+1)
 endpoints={}
 for divisor in range(2,m+1):
  lam=mangoldt(divisor)
  if not lam:continue
  NN=m//divisor
  for k in range(1,NN):
   frac=Fraction(NN,k);endpoints[frac]=endpoints.get(frac,mp.mpf(0))+lam/divisor
 C=[mp.mpf(0)]*(N+1);SC=C.copy();S=C.copy()
 for ratio,weight in endpoints.items():
  upper=mp.log(mp.mpf(ratio.numerator)/ratio.denominator)
  for n in range(N+1):
   z=mp.mpf('.5')+mp.j*2*mp.pi*n/L;e=mp.exp(z*upper);I0=(e-1)/z;I1=(e*(z*upper-1)+1)/(z*z);C[n]+=weight*mp.re(I0);SC[n]+=weight*mp.re(I1);S[n]+=weight*mp.im(I0)
 continuum=matrix_from_mom(C,SC,S,L);centered=raw-continuum
 high=[]
 for n in range(2,m+1):
  lam=mangoldt(n)
  if lam:
   p=int(mp.nint(mp.exp(lam)));e=0;k=n
   while k%p==0:k//=p;e+=1
   if e>=3 and n<m:high.append((mp.log(n),lam/mp.sqrt(n)))
 P3=matrix_from_mom(*atom_moments(N,L,high),L);cstar=mp.euler+mp.log(8*mp.pi)+mp.pi/2;qmatrix=A+(cstar-4)*mp.eye(N+1)+P3
 reduced=U.T*centered*U;ev,V=mp.eigsy(reduced);qe=mp.eigsy(U.T*qmatrix*U,eigvals_only=True);den=max(abs(x) for x in qe);largest=ev[ev.rows-1];f=U*V[:,V.cols-1];f/=mp.norm(f);pivot=max(range(N+1),key=lambda i:abs(f[i]));f*=1 if f[pivot]>=0 else -1
 full=mp.eigsy(centered,eigvals_only=True);lower=mp.fsum(mangoldt(k)/k for k in range(m//2+1,m+1));pk=peak(f,L)
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',m=m,N=N,q=q,dps=dps,source_input_dps=d.get('dps',120),L=L,Omega=2*mp.pi*m/L,centered_complement_max=largest,q_complement_operator_norm=den,ratio=largest/den,ratio_over_L=largest/(den*L),centered_full_min=full[0],N1_PSD_lower_bound=lower,PSD_margin=full[0]-lower,q_complement_min=qe[0],q_complement_max=qe[qe.rows-1],top_vector_q_Rayleigh=mp.fdot(f,qmatrix*f),top_vector_raw_Gram=mp.fdot(f,raw*f),top_vector_floor_continuum=mp.fdot(f,continuum*f),top_vector_centered=mp.fdot(f,centered*f),orthogonality_error=mp.norm(U.T*U-mp.eye(U.cols)),top_eigen_residual=mp.norm(reduced*V[:,V.cols-1]-largest*V[:,V.cols-1]),peak=pk,raw_rational_atom_count=len(atoms),floor_endpoint_count=len(endpoints),full_continuum_retained=True,centered_matrix=centered,raw_matrix=raw,continuum_matrix=continuum,top_physical_vector=list(f),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),preflight_sha256=hashlib.sha256((BUS/'proshka/PROSHKA_VERDICT_DIVISOR_GRAM_PULLBACK_PREFLIGHT_2026-11-02.md').read_bytes()).hexdigest(),prediction_sha256=hashlib.sha256((P/'PREDICTIONS.md').read_bytes()).hexdigest(),seconds=time.monotonic()-start)
 if not keep_dense:
  for key in ['centered_matrix','raw_matrix','continuum_matrix']:result.pop(key)
 (P/f'cell_m{m}_dps{dps}.json').write_text(json.dumps(serial(result,dps),indent=2)+'\n');print(m,dps,'ratio',mp.nstr(largest/den,12),'ratio/L',mp.nstr(largest/den/L,12),'peak/Omega',mp.nstr(pk['t_over_Omega'],12),'PSDmin',mp.nstr(full[0],12),'sec',time.monotonic()-start,flush=True)
if __name__=='__main__':run(*map(int,sys.argv[1:]))
