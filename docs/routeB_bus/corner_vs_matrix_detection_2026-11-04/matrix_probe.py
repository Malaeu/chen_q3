"""Literal CCM finite diagnostic. All saved eigenvalues are unscaled physical A+Q."""
import os
os.environ['OPENBLAS_NUM_THREADS']='2'
from pathlib import Path
import sys,json,time,argparse,hashlib
import numpy as np
from scipy.linalg import eigh,eigvalsh
from threadpoolctl import threadpool_limits
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'builder'))
from source_float import build
AS=[('0',0.),('1/20',.05),('1/10',.1),('1/3',1/3)]
GAMMAS=[14,50,200,800]

def cutoff(m):
 L=np.log(m);return (1+(1+np.log(L))/(4*L))*2*np.pi*m/L

def coefficients(m,a,gamma):
 L=np.log(m);n=np.arange(m+1);omega=2*np.pi*n/L;d=np.full(m+1,np.sqrt(2.));d[0]=1
 z=gamma+1j*a;b=L/2
 # Independent stable entire continuation, equivalent to the owner quotient.
 return d*(-1.)**n/np.sqrt(L)*b*(np.sinc((z-omega)*b/np.pi)+np.sinc((z+omega)*b/np.pi))

def atomic(f,d):
 f.parent.mkdir(parents=True,exist_ok=True);t=f.with_suffix('.tmp');t.write_text(json.dumps(d,indent=2)+'\n');t.replace(f)

def run_cell(m,gammas,positive_cases=None):
 cell=P/'matrix_cells'/f'm{m}.json';old=json.loads(cell.read_text()) if cell.exists() else None
 sha=hashlib.sha256((P/'builder/source_float.py').read_bytes()).hexdigest()
 if old:assert old['builder_sha256']==sha
 existing={(r['a'],r['gamma']) for r in old['cases']} if old else set()
 todo=[(name,a,gamma) for gamma in gammas for name,a in AS if (name,gamma) not in existing and (name=='0' or positive_cases is None or (name,gamma) in positive_cases)]
 if not todo:return old
 start=time.perf_counter();A,meta=build(m)
 with threadpool_limits(limits=2):base=float(eigvalsh(A,subset_by_index=[0,0],check_finite=False,driver='evr')[0])
 assert base>=-1e-12,('UNPLANTED_CONTROL_FAILED',m,base)
 out=old or dict(m=m,dimension=m+1,L=float(np.log(m)),T=float(cutoff(m)),Omega=float(2*np.pi*m/np.log(m)),unplanted_lambda_min=base,source_meta=meta,builder_sha256=sha,cases=[])
 for name,a,gamma in todo:
  assert cutoff(m)>gamma
  c=coefficients(m,a,gamma);Q=4*(np.outer(c.real,c.real)-np.outer(c.imag,c.imag));B=A+Q
  with threadpool_limits(limits=2):vals,vec=eigh(B,subset_by_index=[0,0],check_finite=False,driver='evr',overwrite_a=True)
  value=float(vals[0]);v=vec[:,0];v*=1 if v[np.argmax(abs(v))]>=0 else -1
  residual=float(np.linalg.norm(A@v+4*(c.real*np.dot(c.real,v)-c.imag*np.dot(c.imag,v))-value*v))
  omega=2*np.pi*np.arange(m+1)/np.log(m);weights=v*v;peak=int(np.argmax(weights));indices=np.argsort(weights)[-10:][::-1]
  detection=bool(value < -1e-6);corner=float(A[0,0]+Q[0,0])
  if name=='0':assert not detection and corner>=0,('A0_CONTROL_FAILED',m,gamma,value,corner)
  row=dict(a=name,gamma=gamma,lambda_min=value,detected=detection,corner_float=corner,peak_mode=peak,peak_frequency=float(omega[peak]),frequency_bin=float(2*np.pi/np.log(m)),peak_deviation=float(abs(omega[peak]-gamma)),peak_within_one_bin=bool(abs(omega[peak]-gamma)<=2*np.pi/np.log(m)),gamma_above_Omega=bool(gamma>omega[-1]),centroid_frequency=float(np.dot(weights,omega)),top_modes=[dict(mode=int(i),frequency=float(omega[i]),energy=float(weights[i])) for i in indices],residual_l2=residual,vector_squared_norm=float(np.dot(v,v)))
  if detection:
   prior=[]
   for f in (P/'vectors').glob(f'g{gamma}_a{name.replace("/","_")}_m*.json'):
    prior.append(int(f.stem.rsplit('m',1)[1]))
   if not prior or m<min(prior):
    path=P/'vectors'/f'g{gamma}_a{name.replace("/","_")}_m{m}.json';atomic(path,dict(m=m,a=name,gamma=gamma,lambda_float=value,vector=v.tolist(),basis='j0..m physical orthonormal cosine',builder_sha256=sha))
    row['saved_vector']=str(path.relative_to(P))
  out['cases'].append(row);atomic(cell,out)
 out['wall_seconds_latest_update']=time.perf_counter()-start;atomic(cell,out)
 print(json.dumps(dict(m=m,baseline=base,case_count=len(out['cases']),seconds=out['wall_seconds_latest_update'])),flush=True)
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=['first','checkpoints'],default='first');args=ap.parse_args()
 assert json.loads((P/'gate/gate.json').read_text())['pass']
 assert json.loads((P/'PRE_RUN_RECEIPT.json').read_text())['confirmed_remote_prediction_commit']
 corners=json.loads((P/'corner_summary.json').read_text());admit={r['gamma']:r['m_admit'] for r in corners['cases'] if r['a']=='0'}
 if args.stage=='first':
  for gamma in GAMMAS:run_cell(admit[gamma],[gamma])
 else:
  for m in sorted(set([16,32,64,80,128,208,256,512,1024,2048,3000]+list(admit.values()))):
   run_cell(m,[gamma for gamma in GAMMAS if m>=admit[gamma]])
if __name__=='__main__':main()
