"""P5 only: counterterm-preserving kernel 2cosh deformation.
DIAGNOSTIC_NEVER_A_PROOF. Never regenerates a source or a quiet frame.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,csv,pickle,hashlib,time,argparse
import numpy as np
from scipy.linalg import eigvalsh,eigh
from scipy.special import roots_legendre
import mpmath as mp
OUT=Path(__file__).resolve().parent
ROOT=Path(os.environ.get('STIFFNESS_BASE','/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03'))
LOCAL=Path(os.environ.get('STIFFNESS_LOCAL',str(OUT.parent/'local')))
sys.path.insert(0,str(ROOT/'source'));import split
MS=[16,24,40,80,120,200,248,300]

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def serial(v):
 if isinstance(v,dict):return {k:serial(x)for k,x in v.items()}
 if isinstance(v,(list,tuple)):return [serial(x)for x in v]
 if isinstance(v,mp.matrix):return [[mp.nstr(v[i,j],115)for j in range(v.cols)]for i in range(v.rows)]
 if isinstance(v,mp.mpf):return mp.nstr(v,115)
 if isinstance(v,np.ndarray):return v.tolist()
 if isinstance(v,np.generic):return v.item()
 return v

def save(name,obj):(OUT/name).write_text(json.dumps(serial(obj),indent=2)+'\n')

class Kernels:
 def __init__(self,m,world='zeta',prec='float'):
  self.m=m;self.world=world;self.prec=prec;d=m+1
  if prec=='mp':
   g=split.g;f=split.f;L=g.log(m);pi=split.pi
   pairs=split.gauss(256);y=np.array([(f(p)+(z+1)/2)/8 for p in range(8)for z,w in pairs],object);qw=np.array([L*w/16 for p in range(8)for z,w in pairs],object)
   sin=lambda v:np.array([g.sin(x)for x in v],object);cos=lambda v:np.array([g.cos(x)for x in v],object);ex=lambda v:np.array([g.exp(x)for x in v],object)
   self.sinh=lambda v:np.array([g.sinh(x)for x in v],object);sqr=g.sqrt;self.cast=lambda x:f(str(x));self.zero=f(0)
   bs=split.coefficient(m)[1 if world=='dh' else 0];c=-g.const_euler()-g.log(8*pi/(5 if world=='dh' else 1))+(pi/2 if world=='dh' else -pi/2);z=g.exp(-L/2);tail=g.atanh(z)+(-g.atan(z)if world=='dh'else g.atan(z))
   s=L*y;warch=qw*ex(-s/(f(2)if world!='dh'else f(2)))*(ex(-s)if world=='dh'else 1)/np.array([-g.expm1(-2*x)for x in s],object)
   poles=np.array([4*g.sqrt(2)*(f(1)if n==0 else g.sqrt(2))*L**f('1.5')*g.sinh(L/4)/(L*L+16*pi*pi*n*n)for n in range(d)],object)
   pp=np.array([g.log(n)for n in range(2,m+1)],object);wa=np.array([bs[n]/g.sqrt(n)for n in range(2,m+1)],object)
   if world=='double2':wa[0]+=g.log(2)/g.sqrt(2)
   self.scale=f(1);self.pi=pi;self.ds=np.array([f(1)]+[g.sqrt(2)]*m,object);self.dtype=object
  else:
   L=np.log(m);pi=np.pi;z,w=roots_legendre(256);y=np.concatenate([(p+(z+1)/2)/8 for p in range(8)]);qw=np.tile(w*L/16,8);s=L*y
   sin=np.sin;cos=np.cos;ex=np.exp;self.sinh=np.sinh;sqr=np.sqrt;self.cast=float;self.zero=0.;self.pi=pi;self.ds=np.r_[1,np.full(m,np.sqrt(2))];self.dtype=float
   bs=[float(x)for x in split.coefficient(m)[1 if world=='dh'else 0]];c=-float(split.g.const_euler())-np.log(8*pi/(5 if world=='dh'else 1))+(pi/2 if world=='dh'else -pi/2);zz=np.exp(-L/2);tail=np.arctanh(zz)+(-np.arctan(zz)if world=='dh'else np.arctan(zz))
   warch=qw*np.exp(-(1.5 if world=='dh'else .5)*s)/(-np.expm1(-2*s));poles=np.array([4*np.sqrt(2)*(1 if n==0 else np.sqrt(2))*L**1.5*np.sinh(L/4)/(L*L+16*pi*pi*n*n)for n in range(d)])
   pp=np.log(np.arange(2,m+1));wa=np.array([bs[n]/np.sqrt(n)for n in range(2,m+1)])
   if world=='double2':wa[0]+=np.log(2)/np.sqrt(2)
  self.L=L;self.s=s;self.qw=qw;self.warch=warch;self.pp=pp;self.wa=wa
  self.wpole=qw*(ex(s/2)+ex(-s/2))if world!='dh'else qw*0
  self.S=[];self.C=[];self.Sa=[];self.Ca=[]
  for n in range(d):
   self.S.append(sin(2*pi*n*y));self.C.append(cos(2*pi*n*y));self.Sa.append(sin(2*pi*n*pp/L));self.Ca.append(cos(2*pi*n*pp/L))
  self.S=np.array(self.S);self.C=np.array(self.C);self.Sa=np.array(self.Sa);self.Ca=np.array(self.Ca)
  # Independent baseline reconstruction with the unchanged regularization.
  sm=self.S@warch;di=[]
  for n in range(d):
   term=2*y+2*(1-y)*(1-self.C[n])+(self.S[n]/(pi*n)if n else self.zero);di.append(np.dot(warch,term))
  base=self.form(sm,np.array([c+x+2*tail for x in di],self.dtype))+self.negQ(self.wa,atoms=True)
  if world!='dh':base+=np.outer(poles,poles)
  self.base=base
 def form(self,beta,diag):
  m=self.m;M=np.empty((m+1,m+1),self.dtype)
  for i in range(m+1):
   M[i,i]=diag[i]
   for j in range(i+1,m+1):M[i,j]=M[j,i]=self.ds[i]*self.ds[j]/self.pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
  return M
 def negQ(self,w,atoms=False):
  ss=self.Sa if atoms else self.S;cc=self.Ca if atoms else self.C;y=self.pp/self.L if atoms else self.s/self.L
  if atoms:w=w.copy();w[-1]=self.zero # exact birth Q(log m)=0, all worlds
  beta=ss@w;di=[]
  for n in range(self.m+1):di.append(-np.dot(w,2*(1-y)*cc[n]-(ss[n]/(self.pi*n)if n else self.zero)))
  return self.form(beta,np.array(di,self.dtype))
 def delta(self,a):
  a=self.cast(a);factor=4*self.sinh(a*self.s/2)**2;fa=4*self.sinh(a*self.pp/2)**2
  return self.negQ(factor*(self.warch-self.wpole))+self.negQ(fa*self.wa,atoms=True)
 def curvature(self):return self.negQ(self.s*self.s*(self.warch-self.wpole))+self.negQ(self.pp*self.pp*self.wa,atoms=True)
 def convert(self,M):return mp.matrix([[mp.mpf(str(v))for v in row]for row in M])if self.prec=='mp'else M

def derivative_rows(m,T,prec='float'):
 if prec=='mp':
  L=mp.log(m);zs=[mp.mpf(x['gamma'])for x in csv.DictReader((ROOT/'source_inputs/zeta_zeros.csv').open())if mp.mpf(x['gamma'])<T];out=[]
  for t in zs:
   rr=[]
   for n in range(m+1):
    den=t*t-(2*mp.pi*n/L)**2;rr.append(2*(1 if n==0 else mp.sqrt(2))/mp.sqrt(L)*((mp.sin(t*L/2)+t*L/2*mp.cos(t*L/2))/den-2*t*t*mp.sin(t*L/2)/(den*den)))
   out.append(rr)
  return mp.matrix(out),len(zs)
 L=np.log(m);t=np.array([float(x['gamma'])for x in csv.DictReader((ROOT/'source_inputs/zeta_zeros.csv').open())if float(x['gamma'])<T]);om=2*np.pi*np.arange(m+1)/L;den=t[:,None]**2-om**2;ds=np.r_[1,np.full(m,np.sqrt(2))]
 return 2*ds/np.sqrt(L)*((np.sin(t*L/2)+t*L/2*np.cos(t*L/2))[:,None]/den-2*t[:,None]**2*np.sin(t*L/2)[:,None]/den**2),len(t)

def bisect_float(fn,seed,limit=4.):
 base=fn(0.)
 if base<0:return dict(status='BASELINE_ALREADY_NEGATIVE',a_star=0.,value_at_zero=base)
 lo=0.;hi=max(float(seed),1e-12);vis=[]
 for _ in range(60):
  v=fn(hi);vis.append([hi,v])
  if v<0:break
  lo=hi;hi*=2
  if hi>limit:return dict(status='NO_NEGATIVE_IN_BOUNDED_DIAL',maximum_a=lo,samples=vis)
 else:return dict(status='BRACKET_BUDGET_EXHAUSTED',samples=vis)
 for _ in range(45):
  mid=(lo+hi)/2
  if fn(mid)<0:hi=mid
  else:lo=mid
 return dict(status='FIRST_SAMPLED_CROSSING_BISECTED_NOT_GLOBAL_MONOTONICITY_CERTIFICATE',a_star=hi,lower_a=lo,value_lower=fn(lo),value_upper=fn(hi),coarse_lower_a=.9*hi,coarse_upper_a=1.1*hi,coarse_lower_value=fn(.9*hi),coarse_upper_value=fn(1.1*hi),precision_note='binary point estimate only; fine bisection signs may be at roundoff',samples=vis)

def run_float(m):
 t0=time.monotonic();savepath=ROOT/'source'/f'zeta_m{m}.npz';z=np.load(savepath);A=z['A'];Q=np.load(ROOT/'quiet/frames'/f'zeta_m{m}.npz')['Q'];frame=json.loads((ROOT/'quiet/frames'/f'zeta_m{m}.json').read_text());K=Kernels(m);gate=float(np.max(abs(K.base-A)));tol=float(z['numeric_radius'])*2
 if gate>tol:save(f'p5_float_m{m}.json',dict(m=m,status='SOURCE_GATE_FAILED',gate=gate,tolerance=tol));return
 H=K.curvature();HC=Q.T@H@Q;AC=Q.T@A@Q;ev,V=eigh(AC);q=Q@V[:,0];lam=float(q@A@q);h=float(q@H@q);rows,nzeros=derivative_rows(m,float(frame['T']));E=rows@Q;low=-4*E.T@E;tail=HC-low
 eps=next(float(r['epsilon'])for r in csv.DictReader((ROOT/'SUMMARY.csv').open())if r['world']=='zeta'and int(r['m'])==m)
 seed=np.sqrt((max(0.,2*lam)+eps)/abs(h))if h<0 else 1e-5
 full=bisect_float(lambda a:eigvalsh(2*A+K.delta(a),subset_by_index=[0,0])[0]+eps,seed)
 trial=bisect_float(lambda a:float(q@(2*A+K.delta(a))@q)+eps,seed)
 controls=[]
 for world in ['dh','double2']:
  path=ROOT/'source'/f'{world}_m{m}.npz';zz=np.load(path);AA=zz['A'];KK=Kernels(m,world);err=float(np.max(abs(KK.base-AA)));tolerance=2*float(zz['numeric_radius']);minimum=float(eigvalsh(2*AA,subset_by_index=[0,0])[0]);controls.append(dict(world=world,a0_gate=err,tolerance=tolerance,gate_pass=err<=tolerance,a0_minimum=minimum,negative_detected=minimum< -eps))
 # Existing pinned low-quartet planted form, not an altered zeta source claim.
 gamma=2*np.pi/np.log(2);beta=.25;L=np.log(m);tt=gamma+1j*beta;om=2*np.pi*np.arange(m+1)/L;ds=np.r_[1,np.full(m,np.sqrt(2))];Eplant=2*ds*tt*np.sin(tt*L/2)/(np.sqrt(L)*(tt*tt-om*om));plant=4*np.real(np.outer(Eplant,Eplant));plantmin=float(eigvalsh(2*(A+plant),subset_by_index=[0,0])[0]);controls.append(dict(world='pinned_low_quartet_plant',gamma=gamma,beta=beta,a0_minimum=plantmin,negative_detected=plantmin< -eps,scope='algebraic planted control; quartet contribution at deformation a is 4 Re(E(gamma+i(beta+a))E(gamma+i(beta+a))^T + E(gamma+i(beta-a))E(gamma+i(beta-a))^T)'))
 out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',precision='binary64_calibration',m=m,epsilon=eps,source_gate_max_entry=gate,source_gate_tolerance=tol,source_hash=sha(savepath),a0_equals_2A_exact_by_preserved_baseline=True,curvature_definition='A_a=2A+a^2 H+O(a^4)',quiet_basis_diagonal=np.diag(HC),quiet_curvature_eigenvalues=eigvalsh(HC),quiet_basis_all_negative=bool(np.all(np.diag(HC)<0)),lowpart_diagonal=np.diag(low),source_minus_lowpart_diagonal=np.diag(tail),lowpart_compression_eigenvalues=eigvalsh(low),source_minus_lowpart_eigenvalues=eigvalsh(tail),source_minus_lowpart_frobenius_norm=float(np.linalg.norm(tail)),lowpart_known_positive_zero_count=nzeros,quiet_minimum=lam,qmin_curvature=h,registered_prediction=np.sqrt(lam/abs(h))if lam>0 and h<0 else None,corrected_threshold_prediction=np.sqrt((2*lam+eps)/abs(h))if 2*lam+eps>0 and h<0 else None,full_root=full,quiet_trial_root=trial,controls=controls,source_floor_note='tiny baseline quiet eigenvalues unresolved in binary64; roots use pinned epsilon only',seconds=time.monotonic()-t0)
 save(f'p5_float_m{m}.json',out);print('FLOAT',m,full.get('a_star'),trial.get('a_star'),'S4',out['quiet_basis_all_negative'],flush=True)

def bisect_mp(fn,seed):
 base=fn(mp.mpf(0))
 if base<0:return dict(status='BASELINE_ALREADY_NEGATIVE',a_star=mp.mpf(0),value_at_zero=base)
 lo=mp.mpf(0);hi=seed
 samples=[]
 for _ in range(48):
  v=fn(hi);samples.append([hi,v])
  if v<0:break
  lo=hi;hi*=2
  if hi>4:return dict(status='NO_NEGATIVE_IN_BOUNDED_DIAL',maximum_a=lo,samples=samples)
 else:return dict(status='BRACKET_BUDGET_EXHAUSTED',samples=samples)
 for _ in range(36):
  mid=(lo+hi)/2
  if fn(mid)<0:hi=mid
  else:lo=mid
 return dict(status='FIRST_SAMPLED_CROSSING_BISECTED_NOT_GLOBAL_MONOTONICITY_CERTIFICATE',a_star=hi,lower_a=lo,value_lower=fn(lo),value_upper=fn(hi),samples=samples)

def run_mp(m):
 t0=time.monotonic();mp.mp.dps=120;path=(LOCAL/'mp')/f'm{m}.pkl'
 with path.open('rb')as f:z=pickle.load(f)
 A=z['A'];Q=z['Q'];K=Kernels(m,prec='mp');base=K.convert(K.base);gate=max(abs(v)for v in base-A);tol=mp.mpf('1e-110')
 if gate>tol:save(f'p5_mp_m{m}.json',dict(m=m,status='SOURCE_GATE_FAILED',gate=gate,tolerance=tol));return
 H=K.convert(K.curvature());HC=Q.T*H*Q;AC=Q.T*A*Q;ev,V=mp.eigsy(AC);q=Q*V[:,0];lam=mp.fdot(q,A*q);h=mp.fdot(q,H*q);T=mp.mpf(z['quietdata']['T']);E,nzeros=derivative_rows(m,T,'mp');E=E*Q;low=-4*E.T*E;tail=HC-low;eps=mp.mpf('1e-100');I=mp.eye(m+1)
 def matrix(a):return 2*A+K.convert(K.delta(a))
 def mineig(a):return mp.eigsy(matrix(a),eigvals_only=True)[0]+eps
 seed=mp.sqrt((2*lam+eps)/abs(h))if h<0 and 2*lam+eps>0 else mp.mpf('1e-8')
 # Cholesky is the same finite SPD threshold test, substantially cheaper than
 # repeated all-spectrum MP solves; report final endpoint eigenvalues as well.
 def sign(a):
  try:mp.cholesky(matrix(a)+eps*I);return mp.mpf(1)
  except ValueError:return mp.mpf(-1)
 full=bisect_mp(sign,seed);trial=bisect_mp(lambda a:mp.fdot(q,matrix(a)*q)+eps,seed*mp.mpf('1.1'))
 if full.get('a_star') is not None:
  full['threshold_eigenvalue_lower']=mineig(full.get('lower_a',mp.mpf(0)));full['threshold_eigenvalue_upper']=mineig(full['a_star'])
 pred=mp.sqrt(lam/abs(h))if h<0 and lam>0 else None;correct=mp.sqrt((2*lam+eps)/abs(h))if h<0 and 2*lam+eps>0 else None
 curvature=mp.eigsy(HC,eigvals_only=True);di=[HC[i,i]for i in range(HC.rows)];out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',precision='mpmath120dps_source400bit_GL256_8panels',m=m,epsilon=eps,source_gate_max_entry=gate,source_gate_tolerance=tol,cache_hash=sha(path),a0_equals_2A_exact_by_preserved_baseline=True,quiet_basis_diagonal=di,quiet_curvature_eigenvalues=list(curvature),quiet_basis_all_negative=all(v<0 for v in di),lowpart_diagonal=[low[i,i]for i in range(low.rows)],source_minus_lowpart_diagonal=[tail[i,i]for i in range(tail.rows)],lowpart_compression_eigenvalues=list(mp.eigsy(low,eigvals_only=True)),source_minus_lowpart_eigenvalues=list(mp.eigsy(tail,eigvals_only=True)),source_minus_lowpart_frobenius_norm=mp.norm(tail),lowpart_known_positive_zero_count=nzeros,quiet_minimum=lam,qmin_curvature=h,registered_prediction=pred,corrected_threshold_prediction=correct,full_root=full,quiet_trial_root=trial,full_over_registered=full['a_star']/pred if pred and 'a_star'in full else None,full_over_corrected=full['a_star']/correct if correct and 'a_star'in full else None,source_floor_note='empirical ~1e-114 source floor; no interval source bound or precision chase',seconds=time.monotonic()-t0)
 save(f'p5_mp_m{m}.json',out);print('MP',m,mp.nstr(full.get('a_star'),8),'S4',all(v<0 for v in di),'sec',time.monotonic()-t0,flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['float','mp']);p.add_argument('m',type=int,nargs='+');a=p.parse_args()
 for m in a.m:(run_mp if a.mode=='mp'else run_float)(m)
