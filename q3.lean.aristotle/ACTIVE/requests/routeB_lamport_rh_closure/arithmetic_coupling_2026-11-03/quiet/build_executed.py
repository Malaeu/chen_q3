"""Literal-even κ1 quiet frames. Numerical span diagnostics, no rank certificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from pathlib import Path
import argparse,json,csv,time,hashlib,sys
sys.path.insert(0,os.environ.get('QUIET_DEPS','/workspace/conditioning_deps'))
import numpy as np,scipy.linalg as la,gmpy2 as g
from native_frame import frame
P=Path(__file__).resolve().parent
ZETA=Path(os.environ.get('QUIET_ZETA','/workspace/spike_trend/zeta_zeros.csv'));DH=Path(os.environ.get('QUIET_DH','/workspace/spike_trend/dh_census/dh_zeros_900_200dps.json'))
def events(world):
 if world=='zeta':return [(g.mpfr(r['gamma']),g.mpfr(0),1) for r in csv.DictReader(ZETA.open())]
 d=json.loads(DH.read_text());return sorted([(g.mpfr(r['gamma']),g.mpfr(0),1) for r in d['critical_line_zeros']]+[(g.mpfr(r['gamma']),g.mpfr(r['sigma_right'])-g.mpfr('.5'),2) for r in d['off_line_pairs']])
def rows(m,ev,L):
 freq=[(2*g.const_pi()*j/L)**2 for j in range(m+1)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m;out=[]
 for h,im,mult in ev:
  t=g.mpc(h,im);fac=2*t*g.sin(t*L/2)/g.sqrt(L) if mult==2 else g.mpfr(1);v=[fac*ds[j]/(t*t-freq[j]) for j in range(m+1)];out.append([x.real for x in v])
  if mult==2:out.append([x.imag for x in v])
 return out

def nullrows(m,ev,L):
 d=m+1;q=sum(x[2] for x in ev);r=d-q;ds=[g.mpfr(1)]+[g.sqrt(2)]*m;fac=[g.mpfr(g.fac(k)) for k in range(2*m+1)];w=[g.mpfr((-1)**m)/(fac[m]*fac[m])]+[g.mpfr((-1)**(m-j))*2/(ds[j]*fac[m-j]*fac[m+j]) for j in range(1,d)]
 for h,im,mult in ev:
  z=(g.mpc(h,im)*L/(2*g.const_pi()))**2
  for j in range(d):w[j]*=(g.mpfr(j*j)-z.real) if mult==1 else abs(g.mpfr(j*j)-z)**2
 scale=max(abs(x) for x in w);w=[x/scale for x in w]
 return [[w[j]*(g.mpfr(j*j)/m**2)**k for j in range(d)] for k in range(r)]
def make(m,world,bits=768,validate=False):
 start=time.monotonic();g.get_context().precision=bits;L=g.log(m);omega=2*g.const_pi()*m/L;all_ev=events(world);ev=[x for x in all_ev if x[0]<omega];q=sum(x[2] for x in ev);n=m+1;r=n-q;assert q<n and r>0
 method='ROW_MGS' if q<=r else 'NULL_POLYNOMIAL_MGS';raw=rows(m,ev,L) if q<=r else nullrows(m,ev,L);ff,piv=frame(raw,bits);whole,_=la.qr(ff.T,mode='full')
 if q<=r:U=whole[:,:q];Q=whole[:,q:]
 else:Q=whole[:,:r];U=whole[:,r:]
 rec=dict(world=world,m=m,dimension=n,kappa=1,T=str(omega),cutoff='strict gamma<T; complete off-line orbit included simultaneously',q=q,r=r,rank_assumption=q,rank_status='NUMERICAL_ALGEBRAIC_DISTINCT_NODES; no tolerance truncation',method=method,bits=bits,smallest_relative_mgs_pivot=float(min(piv)),orth_U=float(la.norm(U.T@U-np.eye(q),2)),orth_Q=float(la.norm(Q.T@Q-np.eye(r),2)),cross=float(la.norm(U.T@Q,2)),MP_frame_float_orthogonality=float(la.norm(ff@ff.T-np.eye(len(ff)),2)),quartets_below_T=sum(x[2]==2 for x in ev),largest_included_gamma=str(ev[-1][0]) if ev else None,next_excluded_gamma=str(next(x[0] for x in all_ev if x[0]>=omega)),zero_input_sha256=hashlib.sha256((ZETA if world=='zeta' else DH).read_bytes()).hexdigest(),status='DIAGNOSTIC_NEVER_A_PROOF')
 if validate:
  alt,_=frame(nullrows(m,ev,L) if q<=r else rows(m,ev,L),bits);basis=alt.T;target=Q if q<=r else U;rec['dual_row_projector_difference']=float(la.norm(basis@basis.T-target@target.T,2));rec['dual_row_orthogonality']=float(la.norm(alt@alt.T-np.eye(len(alt)),2));assert rec['dual_row_projector_difference']<1e-10
 rec['seconds']=time.monotonic()-start;dest=P/'frames';dest.mkdir(exist_ok=True);np.savez_compressed(dest/f'{world}_m{m}.npz',Q=Q,U=U);(dest/f'{world}_m{m}.json').write_text(json.dumps(rec,indent=2)+'\n');print(world,m,q,r,method,rec['seconds'],flush=True)
 return rec
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--m',type=int,nargs='+');a.add_argument('--all',action='store_true');a.add_argument('--validate',action='store_true');a.add_argument('--bits',type=int,default=768);q=a.parse_args()
 for m in (range(16,301) if q.all else q.m):
  for world in ['zeta','dh']:
   if q.all and (P/'frames'/f'{world}_m{m}.json').exists():continue
   make(m,world,q.bits,q.validate)
