"""Evaluate only retained oldbounds capable of changing the restricted maximum."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,importlib.util,json,math,csv,hashlib,time
import numpy as np,scipy.linalg as la,gmpy2 as g
from common import *
from restrict import calculate
LOCAL=Path(os.environ.get('PAIR_LOCAL','/workspace/pair_aware/local'));LOCAL.mkdir(exist_ok=True)
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
# All helpers are imported verbatim from the pinned packet.
sys.path.insert(0,str(HIGH));from native_frame import frame
engines={'mid':module('pair_mid_source',MID/'matrix_engine/engine.py'),'high':module('pair_high_source',HIGH/'matrix_engine/source.py')}
def get_matrix(w,m):
 candidates=[LOCAL/'matrices'/f'{w}_m{m}.npz',LOCAL/'adaptive_matrices'/f'{w}_m{m}.npz',LOCAL/'control_delta'/f'{w}_m{m}_A.npz']
 for p in candidates:
  if p.exists():z=np.load(p);return z['A'],p
 rg=region(m);assert rg in engines;g.get_context().precision=400;allA=engines[rg].build(m,192 if rg=='mid'else 256);dest=LOCAL/'adaptive_matrices';dest.mkdir(exist_ok=True)
 for world,A in allA.items():
  a=np.array(A,float);np.savez_compressed(dest/f'{world}_m{m}.npz',A=a,eigenvalues=la.eigvalsh(a))
 p=dest/f'{w}_m{m}.npz';return np.load(p)['A'],p

def constraints(w,m,q):
 g.get_context().precision=768;L=g.log(m);freq=[(2*g.const_pi()*j/L)**2 for j in range(m+1)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m;rows=[]
 for e in events(w,region(m)):
  if len(rows)>=q:break
  h=g.mpfr(e['gamma_decimal'])if e['gamma_decimal']!='2*pi/log(2)'else 2*g.const_pi()/g.log(2);t=g.mpc(h,g.mpfr(e['beta_decimal']));fac=2*t*g.sin(t*L/2)/g.sqrt(L)if e['mult']==2 else g.mpfr(1);v=[fac*ds[j]/(t*t-freq[j])for j in range(m+1)];rows.append([x.real for x in v])
  if e['mult']==2:rows.append([x.imag for x in v])
 assert len(rows)==q;return rows

def main():
 gate=json.loads((P/'baseline_manifest.json').read_text());assert gate['status']=='SEVEN_BASELINE_GATES_PASS';D=dataset();requests=list(csv.DictReader((P/'ADAPTIVE_REQUESTS.csv').open()));tasks=sorted(set((x['world'],int(x['m']))for x in requests));extra={};log=[]
 for w,m in tasks:
  checkpoint=LOCAL/'adaptive_cells'/f'{w}_m{m}.json';checkpoint.parent.mkdir(exist_ok=True)
  if checkpoint.exists():records=json.loads(checkpoint.read_text());extra.update({(w,m,x['q']):x['replacement']for x in records});log+=records;continue
  start=time.time();d=D[w,m];A,path=get_matrix(w,m);todo=sorted({int(x['q'])for x in requests if x['world']==w and int(x['m'])==m});raw=constraints(w,m,max(todo));uf,pivs=frame(raw,768);whole,_=la.qr(uf.T,mode='full');records=[]
  # Ascending q: lambda_r decreases. Every newincumbent prunes later requests.
  for q in todo:
   needed=False
   for theta in THETAS:
    r=calculate(d,theta,extra)
    if q in r['forbidden']:continue
    s=next(x for x in d['sectors']if x['q']==q);inc=max(r['best']['gap']if r['best']else -math.inf,d['guard'])
    if s['upper']>inc+2*d['guard']and s['lambda_r']>d['guard']:needed=True
   if not needed:continue
   s=next(x for x in d['sectors']if x['q']==q);Q=whole[:,q:];delta=float(la.svdvals(A@Q)[0]);gap=s['lambda_r']-delta;replacement=dict(delta=delta,gap=gap,kind='evaluated',method='PINNED_MPFR_FRAME_ADAPTIVE_BOUND_REFINEMENT',status='PASS_NUMERIC'if gap>d['guard']else'FAIL_NUMERIC'if gap< -d['guard']else'UNRESOLVED_NUMERIC_FLOOR');extra[w,m,q]=replacement
   r=dict(world=w,m=m,q=q,lambda_r=s['lambda_r'],delta=delta,gap=gap,guard=d['guard'],old_absolute_upper=s['upper'],within_old_upper=gap<=s['upper']+d['guard'],source_path=str(path),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),frame_orthogonality=float(la.norm(uf@uf.T-np.eye(len(uf)),2)),replacement=replacement);assert r['within_old_upper'];records.append(r)
  checkpoint.write_text(json.dumps(records,indent=2)+'\n');log+=records;print(w,m,'replayed',len(records),'of',len(todo),'qseconds',time.time()-start,flush=True)
 (P/'ADAPTIVE_REFINEMENTS.json').write_text(json.dumps(log,indent=2)+'\n');write_csv('ADAPTIVE_REFINEMENTS.csv',[{k:v for k,v in x.items()if k!='replacement'}for x in log]);print('COMPLETE',len(log),'residual refinements')
if __name__=='__main__':main()
