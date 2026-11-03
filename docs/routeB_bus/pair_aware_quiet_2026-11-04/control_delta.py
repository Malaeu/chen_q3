"""Fill exactly missing original-kappa1 control residuals; no changed source.
DIAGNOSTIC_NEVER_A_PROOF; fixed numerical point zeros, no root enclosure.
Only compact receipts are output; generated dense arrays stay under LOCAL.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,time,json,csv,hashlib,shutil,argparse,importlib.util
import numpy as np
import scipy.linalg as la
import gmpy2 as g
OUT=Path(__file__).resolve().parent
BASE=Path(os.environ.get('PAIR_SEPARATOR_BASE','/workspace/stiffness/repo/docs/routeB_bus/stitch_conditioning_2026-11-03/zero_separator')).resolve()
MID=BASE/'extension_121_300'
LOCAL=Path(os.environ.get('PAIR_CONTROL_LOCAL',str(OUT.parent/'local/control_delta'))).resolve();LOCAL.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(MID));import native_frame
native_frame.P=LOCAL/'native';native_frame.P.mkdir(exist_ok=True)
shutil.copyfile(MID/'frame.c',native_frame.P/'frame.c')
spec=importlib.util.spec_from_file_location('control_mid_engine',MID/'matrix_engine/engine.py');engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
spec=importlib.util.spec_from_file_location('control_mid_scan',MID/'scan_extended.py');scan=importlib.util.module_from_spec(spec);spec.loader.exec_module(scan)
scan.P=MID

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def serial(x):
 if isinstance(x,np.generic):return x.item()
 raise TypeError(type(x).__name__)

def missing_tasks():
 jobs=[];existing=[]
 for m in range(121,301):
  worlds=[]
  for world in ['dh','plant']:
   p=MID/'scan_cells'/f'{world}_m{m}.json';z=json.loads(p.read_text());first=min(z['evaluated']+z['bounded'],key=lambda x:x['q'])
   if 'delta' not in first:worlds.append(world)
   else:existing.append(dict(world=world,m=m,q=first['q'],r=first['r'],delta=first['delta'],source='original_first_sector_receipt',receipt_sha256=sha(p)))
  if worlds:jobs.append((m,worlds))
 assert sum(len(w) for _,w in jobs)==300
 assert sum('dh' in w for _,w in jobs)==180
 assert sum('plant' in w for _,w in jobs)==120
 return jobs,existing

def rows_at_one(world,m):
 g.get_context().precision=768;L=g.log(m);omega=2*g.const_pi()*m/L;ds=[g.mpfr(1)]+[g.sqrt(2)]*m;freq=[(2*g.const_pi()*j/L)**2 for j in range(m+1)];rows=[];physical=[];labels=[]
 for h,im,mult in scan.events(world):
  if h>=omega:break
  t=g.mpc(h,im);fac=2*t*g.sin(t*L/2)/g.sqrt(L);rational=[ds[j]/(t*t-freq[j]) for j in range(m+1)]
  # Reproduce ORIGINAL row-MGS exactly, including critical-row scalar cancellation.
  if mult==1:
   rows.append([v.real for v in rational]);physical.append([float((fac*v).real) for v in rational]);labels.append(dict(height=str(h),imaginary_shift='0',part='line'))
  else:
   values=[fac*v for v in rational]
   rows.append([v.real for v in values]);rows.append([v.imag for v in values]);physical.append([float(v.real) for v in values]);physical.append([float(v.imag) for v in values]);labels.extend([dict(height=str(h),imaginary_shift=str(im),part='real'),dict(height=str(h),imaginary_shift=str(im),part='imag')])
 return rows,np.array(physical),labels,float(omega)

def run_one(m,world,A,ev,npz_path,build_seconds):
 start=time.monotonic();old_path=MID/'scan_cells'/f'{world}_m{m}.json';old=json.loads(old_path.read_text());first=min(old['evaluated']+old['bounded'],key=lambda x:x['q']);assert 'delta' not in first
 rows,E,labels,omega=rows_at_one(world,m);q=len(rows);d=m+1;assert q==first['q'] and d-q==first['r'];uf,pivots=native_frame.frame(rows,768);whole,_=la.qr(uf.T,mode='full');Q=whole[:,q:];AQ=A@Q;delta=float(la.norm(AQ,2));norm=float(la.norm(A,2));guard=max(float(64*np.finfo(float).eps*d*max(1.,max(abs(ev)))),1000*np.finfo(float).eps*d*max(1,norm));meta_path=MID/'matrix_metadata'/f'{world}_m{m}.json';meta=json.loads(meta_path.read_text())
 E_norm=float(la.norm(E,2));e_res=float(la.norm(E@Q,2));orth=float(la.norm(Q.T@Q-np.eye(d-q),2));frameorth=float(la.norm(uf@uf.T-np.eye(q),2));delta_svd=float(la.svdvals(AQ)[0]);matrix_array_hash=hashlib.sha256(np.ascontiguousarray(A).tobytes()).hexdigest();Q_array_hash=hashlib.sha256(np.ascontiguousarray(Q).tobytes()).hexdigest()
 localnpz=LOCAL/f'{world}_m{m}_Q_AQ.npz';np.savez_compressed(localnpz,Q=Q,AQ=AQ)
 original_qguard=old['summary']['numeric_guard'];out=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,kappa=1,q=q,r=d-q,delta=delta,delta_repeated_svd=delta_svd,delta_svd_difference=abs(delta-delta_svd),baseline_lambda_min=float(ev[0]),baseline_lambda_max=float(ev[-1]),original_negative_count_range=meta['negative_count_range'],regenerated_resolved_negative_count=int(np.sum(ev < -guard)),numeric_guard=guard,original_numeric_guard=original_qguard,source_bits=400,source_GL_order=192,source_panels=8,frame_bits=768,frame_method='UNCHANGED_MPFR_ORDERED_TWICE_REORTHOGONALIZED_MGS_THEN_ORDERED_FLOAT_QR',row_scalar_convention='critical nonzero physical scalar cancels; quartets retain complex scalar before real/imag split; exactly original scan_extended',constraint_EQ_norm=e_res,constraint_E_norm=E_norm,constraint_relative=e_res/max(1.,E_norm),Q_orthogonality_norm=orth,ordered_frame_orthogonality_norm=frameorth,minimum_relative_MGS_pivot=float(min(pivots)),Omega=omega,strict_inclusion='height<Omega; quartet rows enter atomically',row_labels=labels,first_sector_original=first,source_A_array_sha256=matrix_array_hash,Q_array_sha256=Q_array_hash,local_source_npz_sha256=sha(npz_path),local_Q_AQ_npz_sha256=sha(localnpz),source_engine_sha256=sha(MID/'matrix_engine/engine.py'),native_frame_py_sha256=sha(MID/'native_frame.py'),native_frame_c_sha256=sha(MID/'frame.c'),scan_extended_py_sha256=sha(MID/'scan_extended.py'),source_metadata_sha256=sha(meta_path),original_sector_receipt_sha256=sha(old_path),zeta_census_sha256=sha(MID/'zeta_zeros.csv'),DH_census_sha256=sha(MID/'dh_census/dh_zeros_600_200dps.json'),matrix_build_seconds=build_seconds,residual_seconds=time.monotonic()-start,guard_status='heuristic float and empirical source rules; not interval certification',local_large_arrays_committed=False)
 outpath=OUT/f'control_delta_{world}_m{m}.json';outpath.write_text(json.dumps(out,indent=2,default=serial)+'\n');print('CONTROL_DELTA',world,m,'q',q,'r',d-q,'delta',delta,'lambda_min',ev[0],'source_sec',round(build_seconds,2),'resid_sec',round(out['residual_seconds'],2),flush=True)
 return out

def run_m(job):
 m,worlds=job;needed=[w for w in worlds if not(OUT/f'control_delta_{w}_m{m}.json').exists()]
 if not needed:return []
 start=time.monotonic();g.get_context().precision=400;allA=engine.build(m,192);build_seconds=time.monotonic()-start;result=[]
 for world in needed:
  A=np.array(allA[world],float);ev=la.eigvalsh(A);npz=LOCAL/f'{world}_m{m}_A.npz';np.savez_compressed(npz,A=A,eigenvalues=ev)
  result.append(run_one(m,world,A,ev,npz,build_seconds))
 return result

def require_gate(path):
 if not path.exists():raise RuntimeError('BASELINE_GATE_NOT_AVAILABLE: no dependent regeneration allowed')
 z=json.loads(path.read_text());status=str(z.get('status',''))
 if 'PASS' not in status or 'FAIL' in status or len(z.get('tasks',[]))!=7 or not all(t.get('status')=='BASELINE_GATE_PASS' for t in z.get('tasks',[])):raise RuntimeError('BASELINE_GATE_NOT_PASS: '+status)
 return dict(path=str(path),sha256=sha(path),payload=z)

def aggregate(gate):
 rows=[]
 for p in sorted(OUT.glob('control_delta_*_m*.json')):
  z=json.loads(p.read_text())
  if 'delta' not in z or 'kappa' not in z:continue
  meta=json.loads((MID/'matrix_metadata'/f"{z['world']}_m{z['m']}.json").read_text());oldmin=float(meta['float_minimum']);guard=float(z['original_numeric_guard']);z.update(original_baseline_lambda_min=oldmin,baseline_lambda_min_difference=abs(z['baseline_lambda_min']-oldmin),baseline_lambda_min_matches_original_guard=abs(z['baseline_lambda_min']-oldmin)<=guard,delta_max_original_kappa1=z['delta'])
  p.write_text(json.dumps(z,indent=2)+'\n')
  rows.append({k:z[k] for k in ['world','m','kappa','q','r','delta','delta_max_original_kappa1','baseline_lambda_min','original_baseline_lambda_min','baseline_lambda_min_difference','baseline_lambda_min_matches_original_guard','numeric_guard','original_numeric_guard','constraint_EQ_norm','constraint_relative','Q_orthogonality_norm','ordered_frame_orthogonality_norm','minimum_relative_MGS_pivot','source_A_array_sha256','Q_array_sha256','source_engine_sha256','source_GL_order','source_bits','frame_bits','matrix_build_seconds','residual_seconds']})
 if rows:
  with (OUT/'control_delta_missing.csv').open('w') as f:w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
 jobs,existing=missing_tasks();expected={(w,m) for m,ww in jobs for w in ww};actual={(z['world'],z['m']) for z in rows};receipt=dict(status='DIAGNOSTIC_NEVER_A_PROOF',baseline_gate=gate,expected_missing_rows=300,completed_missing_rows=len(actual),missing_DH_expected=180,missing_plant_expected=120,completed_by_world={w:sum(z['world']==w for z in rows) for w in ['dh','plant']},all_regenerated_baseline_minima_match_original_guard=all(z['baseline_lambda_min_matches_original_guard'] for z in rows),maximum_constraint_relative=max((z['constraint_relative'] for z in rows),default=None),maximum_Q_orthogonality_norm=max((z['Q_orthogonality_norm'] for z in rows),default=None),remaining_rows=[dict(world=w,m=m) for w,m in sorted(expected-actual)],existing_original_plant_first_sectors=existing,source_recipe='unchanged mid engine.build(m,192),400bit GL192 eight panels',frame_recipe='unchanged scan physical row convention; native768bit2passorderedMGS thenfloatQR',large_arrays_local_only=True,quadrature_pilot_change=False)
 (OUT/'control_delta_COVERAGE.json').write_text(json.dumps(receipt,indent=2)+'\n');return receipt

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--gate',type=Path,default=OUT/'baseline_manifest.json');ap.add_argument('--pilot',action='store_true');ap.add_argument('--workers',type=int,default=2);ap.add_argument('--aggregate-only',action='store_true');args=ap.parse_args();jobs,_=missing_tasks()
 if args.aggregate_only:print(json.dumps(aggregate(require_gate(args.gate) if args.gate.exists() else None),indent=2));raise SystemExit
 gate=require_gate(args.gate);native_frame.load()
 selected=[jobs[0],jobs[-1]] if args.pilot else jobs
 if args.workers==1:
  for job in selected:run_m(job)
 else:
  from concurrent.futures import ProcessPoolExecutor
  with ProcessPoolExecutor(max_workers=min(args.workers,2)) as pool:list(pool.map(run_m,selected))
 z=aggregate(gate);print('COVERAGE',z['completed_missing_rows'],'of',z['expected_missing_rows'],flush=True)
