"""DIAGNOSTIC_NEVER_A_PROOF. Signed physical source ledger and exact Abel moments.

Source dh_matrix.py@d268313 is read unchanged. This script reconstructs its
components and records J-perp diagnostics; no route-state or proof exports.
"""
from pathlib import Path
import sys,json,time,csv,hashlib,os
import mpmath as mp
P=Path(__file__).resolve().parent
INPUT=Path(os.environ.get('DH_INPUTS',str(P.parents[1])))

def fmt(x):
 if isinstance(x,mp.matrix):return [[mp.nstr(x[i,j],120) for j in range(x.cols)] for i in range(x.rows)]
 if isinstance(x,mp.mpf):return mp.nstr(x,120)
 if isinstance(x,dict):return {str(k):fmt(v) for k,v in x.items()}
 if isinstance(x,(list,tuple)):return [fmt(v) for v in x]
 return x

def erow(t,m):
 L=mp.log(m);b=L/2
 return [((1 if n==0 else mp.sqrt(2))*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-2*mp.pi*n/L)*b)+mp.sinc((t+2*mp.pi*n/L)*b))) for n in range(m+1)]

def prime_power(n):
 for p in range(2,n+1):
  if any(p%d==0 for d in range(2,int(p**.5)+1)):continue
  k=1;v=p
  while v<n:v*=p;k+=1
  if v==n:return p,k
 return None

def coefficients(m,world):
 if world=='DH':
  sys.path.insert(0,str(INPUT));import dh_matrix
  return dh_matrix.coeffs(m)[1]
 return [mp.mpf(0) if n<2 or not prime_power(n) else mp.log(prime_power(n)[0]) for n in range(m+1)]

def build(m,world,dps=120,order=128):
 mp.mp.dps=dps;L=mp.log(m);N=m;b=coefficients(m,world)
 gn,gw=mp.gauss_quadrature(order,'legendre');nodes=[((mp.mpf(p)+(x+1)/2)/8,w/16) for p in range(8) for x,w in zip(gn,gw)]
 sinmom=[mp.mpf(0)]*(N+1);diag=[mp.mpf(0)]*(N+1);primeS=[mp.mpf(0)]*(N+1);primeD=[mp.mpf(0)]*(N+1)
 shift=mp.mpf('1.5') if world=='DH' else mp.mpf('.5')
 for y,w in nodes:
  x=L*y;j=mp.exp(-shift*x)/(-mp.expm1(-2*x));wt=L*w*j
  co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(N+1):
   sinmom[n]+=wt*sn
   diag[n]+=wt*(2*y+2*(1-y)*(1-cn)+(sn/(mp.pi*n) if n else 0))
   cn,sn=cn*co-sn*si,sn*co+cn*si
 for k in range(2,m):
  y=mp.log(k)/L;weight=b[k]/mp.sqrt(k);co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(N+1):
   primeS[n]+=weight*sn;primeD[n]+=weight*(2*(1-y)*cn-(sn/(mp.pi*n) if n else 0))
   cn,sn=cn*co-sn*si,sn*co+cn*si
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*N;A=mp.zeros(N+1);H=mp.zeros(N+1)
 c=mp.log(5/mp.pi)+mp.digamma(mp.mpf('.75')) if world=='DH' else -mp.euler-mp.log(8*mp.pi)-mp.pi/2
 a=mp.exp(-L/2);tail=mp.atanh(a)+(-1 if world=='DH' else 1)*mp.atan(a)
 pole=mp.zeros(N+1)
 if world=='zeta':
  pv=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(N+1)])
  pole=pv*pv.T
 for i in range(N+1):
  H[i,i]=diag[i]+2*tail;A[i,i]=c+H[i,i]-primeD[i]+pole[i,i]
  for k in range(i+1,N+1):
   H[i,k]=H[k,i]=ds[i]*ds[k]/mp.pi*(i*sinmom[i]-k*sinmom[k])/(i*i-k*k)
   A[i,k]=A[k,i]=H[i,k]+ds[i]*ds[k]/mp.pi*(i*primeS[i]-k*primeS[k])/(i*i-k*k)+pole[i,k]
 return A,H,pole,c,b

def qcoeff(v,m):
 d=[mp.mpf(1)]+[mp.sqrt(2)]*m
 D=[2*x*x for x in v];S=[mp.mpf(0)]*(m+1)
 for n in range(1,m+1):
  S[n]=-v[n]**2/(mp.pi*n)-2*v[n]*d[n]*n/mp.pi*mp.fsum(v[k]*d[k]/(n*n-k*k) for k in range(m+1) if k!=n)
 return D,S

def qvalue(s,D,S,L):
 if s>=L:return mp.mpf(0)
 return mp.fsum(D[n]*(1-s/L)*mp.cos(2*mp.pi*n*s/L)+S[n]*mp.sin(2*mp.pi*n*s/L) for n in range(len(D)))

def int_exp(lam,lo,hi,power=0):
 def F(s):return mp.exp(lam*s)/lam if power==0 else mp.exp(lam*s)*(s/lam-1/(lam*lam))
 return F(hi)-F(lo)

def abel_ledger(v,m,b,reference=True):
 L=mp.log(m);D,S=qcoeff(v,m);fb=mp.fsum(v[n]*(1 if n==0 else mp.sqrt(2)) for n in range(m+1))/mp.sqrt(L)
 halfq=mp.mpf(0);minusqprime=mp.mpf(0);boundary=mp.mpf(0)
 for n in range(m+1):
  omega=2*mp.pi*n/L;lam=-mp.mpf('.5')+mp.j*omega
  moments=[]
  for power in (0,1):
   mom=mp.fsum(b[k]*int_exp(lam,mp.log(k),L,power) for k in range(2,m+1))
   if reference:mom+=int_exp(lam,0,L,power)-int_exp(mp.mpf('.5')+mp.j*omega,0,L,power)
   moments.append(mom)
  C=mp.re(moments[0]);Sm=mp.im(moments[0]);sC=mp.re(moments[1]);sS=mp.im(moments[1])
  halfq+=D[n]/2*(C-sC/L)+S[n]/2*Sm
  minusqprime+=D[n]/L*C+D[n]*omega*(Sm-sS/L)-S[n]*omega*C
  boundary+=2*fb/mp.sqrt(L)*(1 if n==0 else mp.sqrt(2))*v[n]*C
 continuum=mp.mpf(0);decaying_continuum=mp.mpf(0)
 for n in range(m+1):
  om=2*mp.pi*n/L;lam=mp.mpf('.5')+mp.j*om
  M0=int_exp(lam,0,L);M1=int_exp(lam,0,L,1)
  continuum+=D[n]*(mp.re(M0)-mp.re(M1)/L)+S[n]*mp.im(M0)
  Mm0=int_exp(-mp.mpf('.5')+mp.j*om,0,L);Mm1=int_exp(-mp.mpf('.5')+mp.j*om,0,L,1)
  decaying_continuum+=D[n]*(mp.re(Mm0)-mp.re(Mm1)/L)+S[n]*mp.im(Mm0)
 prime=mp.fsum(b[k]/mp.sqrt(k)*qvalue(mp.log(k),D,S,L) for k in range(2,m+1))
 return dict(reference_subtracted=reference,boundary_B=boundary,interior_I=minusqprime-boundary,half_Q=halfq,abel_sum=halfq+minusqprime,atom_sum=prime,continuum=continuum,decaying_continuum=decaying_continuum,abel_identity_residual=halfq+minusqprime-prime+(continuum if reference else 0),endpoint_f=fb)

def sampling(m,world,T):
 if world=='DH':
  z=json.loads((INPUT/'dh_zeros.json').read_text());rows=[]
  for a in z['critical_line_zeros']:
   g=mp.mpf(a['gamma'])
   if g<T:rows.append(erow(g,m))
  for a in z['off_line_pairs']:
   g=mp.mpf(a['gamma']);dd=mp.mpf(a['sigma_right'])-mp.mpf('.5')
   if g<T:
    v=erow(g+mp.j*dd,m);rows.extend([[mp.sqrt(2)*mp.re(t) for t in v],[mp.sqrt(2)*mp.im(t) for t in v]])
  return mp.matrix(rows)
 rows=[]
 zpath=INPUT/'zeta_zeros.csv'
 if not zpath.exists():zpath=INPUT.parent/'capacity_matrix_2026-11-02'/'zeros.csv'
 for a in csv.DictReader(zpath.open()):
  g=mp.mpf(a['gamma'])
  if g>=T:break
  rows.append(erow(g,m))
 return mp.matrix(rows)

def run(m,world):
 start=time.monotonic();mp.mp.dps=120
 A,H,pole,c,b=build(m,world);reconstruction_difference=mp.mpf(0)
 if world=='DH':
  pinned=json.loads((INPUT/'matrix_cells'/f'dh_m{m}_dps120_gl128.json').read_text())
  sourceA=mp.matrix(pinned['A']);reconstruction_difference=mp.norm(A-sourceA);A=sourceA
 else:
  export=Path(os.environ.get('DH_EXPORT',str(P/'matrix_exports')));export.mkdir(parents=True,exist_ok=True)
  (export/f'zeta_m{m}.json').write_text(json.dumps(fmt(dict(A=A,H=H,pole=pole,constant=c,dps=120,order=128)),indent=2)+'\n')
 L=mp.log(m);T=mp.mpf('1.1')*2*mp.pi*m/L;E=sampling(m,world,T)
 # Row equilibration preserves ker and improves accuracy of its numerical basis.
 EE=mp.matrix([[E[i,j]/mp.norm(E[i,:]) for j in range(m+1)] for i in range(E.rows)])
 U,s,V=mp.svd_r(EE,full_matrices=True);rank=min(E.rows,m+1);Ucomp=V[:rank,:].T;Q=V[rank:,:].T
 B=Ucomp.T*A*Ucomp;ev,Z=mp.eigsy(B);v=Ucomp*Z[:,0];v/=mp.norm(v)
 ray=(v.T*A*v)[0];delta=mp.sqrt(max(mp.eigsy((A*Q).T*(A*Q),eigvals_only=True))) if Q.cols else mp.mpf(0)
 full=mp.eigsy(A,eigvals_only=True)
 groups={'H':(v.T*H*v)[0],'constant_c':c,'pole':(v.T*pole*v)[0]}
 for group in ('p','p2','pk_ge3','nonprimepower'):
  for sign in ('positive_b','negative_b'):groups[group+'_'+sign]=mp.mpf(0)
 D,S=qcoeff(v,m)
 for n in range(2,m+1):
  if not b[n]:continue
  pp=prime_power(n);group='nonprimepower' if pp is None else ('p' if pp[1]==1 else 'p2' if pp[1]==2 else 'pk_ge3')
  sign='positive_b' if b[n]>0 else 'negative_b'
  groups[group+'_'+sign]+=-b[n]/mp.sqrt(n)*qvalue(mp.log(n),D,S,L)
 total=mp.fsum(groups.values());abel=abel_ledger(v,m,b)
 if world=='zeta':
  abel['H_plus']=groups['H']-4+abel['decaying_continuum']
  abel['pole_continuum_identity_residual']=groups['pole']-abel['continuum']-abel['decaying_continuum']
  abel['transformed_rayleigh']=abel['H_plus']+4+c-abel['abel_sum']
  abel['transformed_minus_rayleigh']=abel['transformed_rayleigh']-ray
  abel['abs_boundary_over_H_plus']=abs(abel['boundary_B'])/abel['H_plus']
  abel['abs_interior_over_H_plus']=abs(abel['interior_I'])/abel['H_plus']
 abel['boundary_over_abel_sum']=abel['boundary_B']/abel['abel_sum'] if abel['abel_sum'] else None
 abel['interior_over_abel_sum']=abel['interior_I']/abel['abel_sum'] if abel['abel_sum'] else None
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',source=('dh_matrix.py @ d268313 unchanged; saved pinned120dps A' if world=='DH' else 'literal physical even CCM q_even source @ d268313; moment recurrence with exact arch tail'),m=m,world=world,dps=120,order=128,kappa='1.1',T=T,q=E.rows,rank=rank,dim_J=Q.cols,row_scaled_sigma_min=s[rank-1],row_scaled_SVD_residual=mp.norm(EE-U[:,:rank]*mp.diag(s)*V[:rank,:]),compressed_minimum=ev[0],rayleigh=ray,full_minimum=full[0],R_full=-full[0],delta=delta,groups=groups,group_sum=total,group_sum_minus_rayleigh=total-ray,source_reconstruction_matrix_difference=reconstruction_difference,compressed_eigen_residual=mp.norm(B*Z[:,0]-ev[0]*Z[:,0]),E_Q_residual=mp.norm(E*Q),U_Q_orthogonality=mp.norm(Ucomp.T*Q),vector=v,abel=abel,seconds=time.monotonic()-start)
 (P/f'{world}_m{m}.json').write_text(json.dumps(fmt(out),indent=2)+'\n')
 print(world,m,'lambda',mp.nstr(ray,15),'delta',mp.nstr(delta,12),'ledger-residual',mp.nstr(total-ray,5),'Abel-residual',mp.nstr(abel['abel_identity_residual'],5),'seconds',time.monotonic()-start,flush=True)
 return out

if __name__=='__main__':run(int(sys.argv[1]),sys.argv[2])
