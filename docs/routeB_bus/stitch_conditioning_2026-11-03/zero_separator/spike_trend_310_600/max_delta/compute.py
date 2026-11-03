"""κ=1 maximal residual under nested quiet spaces; finite numerical diagnostic."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,csv,time,hashlib,argparse
import numpy as np,scipy.linalg as la,gmpy2 as g
P=Path(__file__).resolve().parent;ROOT=P.parent;sys.path.insert(0,str(ROOT))
from native_frame import frame
from scan_extended import last_null
DH=Path(os.environ.get('DH_BASELINE_TABLE',str(ROOT/'source_inputs/dh_zeros_600_200dps.json')))
def events(world):
 if world=='plant':
  ev=[(g.mpfr(x['gamma']),g.mpfr(0),1) for x in csv.DictReader((ROOT/'zeta_zeros.csv').open())];ev.append((2*g.const_pi()/g.log(2),g.mpfr('.25'),2))
 else:
  z=json.loads(DH.read_text());ev=[(g.mpfr(x['gamma']),g.mpfr(0),1) for x in z['critical_line_zeros']];ev.extend((g.mpfr(x['gamma']),g.mpfr(x['sigma_right'])-g.mpfr('.5'),2)for x in z['off_line_pairs'])
 return sorted(ev)
def getQ(world,m,bits,method):
 g.get_context().precision=bits;L=g.log(m);T=2*g.const_pi()*m/L;ev=[e for e in events(world) if e[0]<T];q=sum(e[2] for e in ev);d=m+1
 assert 0<q<d
 if method=='null':Q=last_null(ev,q,m,bits);pivot=None
 else:
  freq=[(2*g.const_pi()*j/L)**2 for j in range(d)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m;rows=[]
  for h,im,mult in ev:
   t=g.mpc(h,im);fac=2*t*g.sin(t*L/2)/g.sqrt(L) if mult==2 else g.mpfr(1);row=[fac*ds[j]/(t*t-freq[j]) for j in range(d)];rows.append([v.real for v in row])
   if mult==2:rows.append([v.imag for v in row])
  uf,piv=frame(rows,bits);whole,_=la.qr(uf.T,mode='full');Q=whole[:,q:];pivot=float(min(piv))
 return Q,q,dict(T=str(T),quartets=sum(v[2]==2 for v in ev),min_frame_pivot=pivot)
def run(task):
 world,m,bits,method=task;start=time.monotonic();Q,q,more=getQ(world,m,bits,method);src=ROOT/'matrices'/f'{world}_m{m}.npz';z=np.load(src);A=z['A'];e=z['eigenvalues'];sv=la.svdvals(A@Q);guard=max(float(z['numeric_radius']),1000*np.finfo(float).eps*(m+1)*max(1.,abs(e[0]),abs(e[-1])));r=m+1-q
 a=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,kappa=1,q=q,r=r,bits=bits,method=method,delta=float(sv[0]),sigma_1=float(sv[0]),sigma_2=float(sv[1]) if len(sv)>1 else None,lambda_r=float(e[r]),gap=float(e[r]-sv[0]),numeric_guard=guard,Q_orthogonality=float(la.norm(Q.T@Q-np.eye(r),2)),maximality='J shrinks with increasing kappa, hence operator norm delta cannot increase; kappa1 is maximal over kappa>=1',source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),events_source=str(DH if world=='dh' else ROOT/'zeta_zeros.csv'),seconds=time.monotonic()-start,**more)
 (P/f'{world}_m{m}.json').write_text(json.dumps(a,indent=2)+'\n');print(world,m,bits,method,'q',q,'delta',a['delta'],'seconds',a['seconds'],flush=True);return a

def pilot():
 out=[]
 for m in [310,600]:
  qs=[]
  for bits in [768,1024]:
   t=time.monotonic();Q,q,meta=getQ('dh',m,bits,'null');qs.append(Q);print('PILOTNULL',m,bits,q,time.monotonic()-t,flush=True)
  proj=la.norm(qs[0]@qs[0].T-qs[1]@qs[1].T,2);a=np.load(ROOT/'matrices'/f'dh_m{m}.npz')['A'];deltas=[float(la.norm(a@Q,2))for Q in qs];rowdiff=None
  if m==310:
   t=time.monotonic();Qr,_,_=getQ('dh',m,768,'row');rowdiff=float(la.norm(Qr@Qr.T-qs[0]@qs[0].T,2));print('PILOTROW',m,time.monotonic()-t,flush=True)
  out.append(dict(m=m,q=q,projector_768_1024=float(proj),delta_768=deltas[0],delta_1024=deltas[1],projector_null_vs_row=rowdiff))
 (P/'VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');a=p.parse_args()
 if a.pilot:pilot()
 else:
  from concurrent.futures import ProcessPoolExecutor
  todo=[(w,m,768,'null' if w=='dh' else 'row') for m in range(310,601,10) for w in ['plant','dh'] if not (P/f'{w}_m{m}.json').exists()]
  with ProcessPoolExecutor(max_workers=2) as pool:list(pool.map(run,todo))
