"""Pinned-source baseline gate; no production-source edits or new recipe.
Rebuild authorized 400bit GL256/8panel matrices locally, replay original
768bit scan and compare original guards. DIAGNOSTIC_NEVER_A_PROOF.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,csv,time,hashlib,shutil
import numpy as np
import scipy.linalg as la
ROOT=Path(os.environ.get('PAIR_BASE','/workspace/stiffness/repo/docs/routeB_bus/stitch_conditioning_2026-11-03/zero_separator'));HIGH=ROOT/'spike_trend_310_600';EXT=ROOT/'extension_121_300';LOCAL=Path(os.environ.get('PAIR_LOCAL','/workspace/pair_aware/local'));OUT=Path(__file__).resolve().parent
for name in ['native','matrices','scan_cells','dh_census']:(LOCAL/name).mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(HIGH));import native_frame
native_frame.P=LOCAL/'native'
def copy_once(src,dst):
 if not dst.exists()or src.read_bytes()!=dst.read_bytes():shutil.copyfile(src,dst)
copy_once(HIGH/'frame.c',native_frame.P/'frame.c')
import scan_extended as scan
sys.path.insert(0,str(HIGH/'matrix_engine'));import source
scan.P=LOCAL
(LOCAL/'dh_census').mkdir(exist_ok=True);copy_once(HIGH/'zeta_zeros.csv',LOCAL/'zeta_zeros.csv');copy_once(HIGH/'dh_census/dh_zeros_900_200dps.json',LOCAL/'dh_census/dh_zeros_900_200dps.json')

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def original(world,m):return json.loads(((EXT if m==248 else HIGH)/'scan_cells'/f'{world}_m{m}.json').read_text())
def build(m):
 if all((LOCAL/'matrices'/f'{w}_m{m}.npz').exists()for w in ['zeta','dh','plant']):return
 source.g.get_context().precision=400;t=time.monotonic();allA=source.build(m,256)
 for w,M in allA.items():
  A=np.array(M,float);ev=la.eigvalsh(A);radius=64*np.finfo(float).eps*(m+1)*max(1.,max(abs(ev)));path=LOCAL/'matrices'/f'{w}_m{m}.npz';np.savez_compressed(path,A=A,eigenvalues=ev,lambda_=ev,m=m,numeric_radius=radius)
  meta=(EXT if m==248 else HIGH)/'matrix_metadata'/f'{w}_m{m}.json';z=json.loads(meta.read_text());z['regeneration_recipe']={'source_py_sha256':sha(HIGH/'matrix_engine/source.py'),'bits':400,'GL_order':256,'panels':8,'saved_local_only':True,'source_metadata_reference_sha256':sha(meta),'numeric_radius_regenerated':radius,'source_build_seconds':time.monotonic()-t};path.with_suffix('.json').write_text(json.dumps(z,indent=2)+'\n')
 print('SOURCE_READY',m,'sec',time.monotonic()-t,flush=True)
def selected(world,m,old,A,ev):
 source.g.get_context().precision=768;oq=old['summary']['best_q'];osum=old['summary'];method=osum['best_candidate_method'];events=scan.events(world)
 if method=='CAUCHY_NULL_POLYNOMIAL':Q=scan.last_null(events,oq,m,768)
 else:
  g=source.g;L=g.log(m);freq=[(2*g.const_pi()*j/L)**2 for j in range(m+1)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m;rows=[]
  for h,im,mult in events:
   if len(rows)>=oq:break
   t=g.mpc(h,im);fac=2*t*g.sin(t*L/2)/g.sqrt(L)if mult==2 else g.mpfr(1);row=[fac*ds[j]/(t*t-freq[j])for j in range(m+1)];rows.append([v.real for v in row])
   if mult==2:rows.append([v.imag for v in row])
  assert len(rows)==oq;uf,piv=native_frame.frame(rows,768);whole,_=la.qr(uf.T,mode='full');Q=whole[:,oq:]
 delta=float(la.norm(A@Q,2));r=m+1-oq;lam=float(ev[r]);return dict(q=oq,r=r,lambda_r=lam,delta=delta,gap=lam-delta,method=method)
def run(world,m):
 build(m);old=original(world,m);orig=old['summary'];path=LOCAL/'matrices'/f'{world}_m{m}.npz';z=np.load(path);A=z['A'];ev=z['eigenvalues'];direct=selected(world,m,old,A,ev);full=scan.run((world,m,768));guard=orig['numeric_guard'];checks={k:abs(direct[k]-orig[{'lambda_r':'best_lambda_r','delta':'best_delta','gap':'best_gap'}[k]])<=guard for k in ['lambda_r','delta','gap']};checks['full_best_gap']=abs(full['best_gap']-orig['best_gap'])<=guard
 out=dict(status='BASELINE_GATE_PASS'if all(checks.values())else'BASELINE_GATE_FAIL',world=world,m=m,original_guard=guard,source_recipe='unchanged high source.build(m,256),400bits,8panels',original_selected=orig,regenerated_selected=direct,regenerated_full_scan_summary=full,checks=checks,regenerated_A_sha256=sha(path),original_scan_sha256=sha((EXT if m==248 else HIGH)/'scan_cells'/f'{world}_m{m}.json'),source_py_sha256=sha(HIGH/'matrix_engine/source.py'),native_frame_py_sha256=sha(HIGH/'native_frame.py'),native_frame_c_sha256=sha(HIGH/'frame.c'),scope='absolute replay within original heuristic guard; relative differences of floor delta/gaps are unscored; no changed precision/recipe')
 (OUT/f'baseline_{world}_m{m}.json').write_text(json.dumps(out,indent=2,default=lambda x:x.item()if isinstance(x,np.generic)else str(x))+'\n');print('BASELINE',world,m,out['status'],checks,flush=True)
 if not all(checks.values()):raise ArithmeticError('Baseline gate failed; dependent tasks stop')
if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--m',type=int,nargs='+',default=[248,310,600]);args=ap.parse_args()
 for m in args.m:
  for w in (['zeta']if m==248 else ['zeta','dh','plant']):run(w,m)
