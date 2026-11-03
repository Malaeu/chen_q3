"""One cheap existing-sector floor candidate per weak restriction.
DIAGNOSTIC_NEVER_A_PROOF. Same400bit source and768bit null frame; no precision chase.
New point information is applied to the unrestricted baseline too, never pair gain.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,csv,time,hashlib,shutil,importlib.util,argparse
import numpy as np
import scipy.linalg as la
import gmpy2 as g
from common import *
from restrict import calculate
from finalize import extras
import adaptive
OUT=Path(__file__).resolve().parent
LOCAL=Path(os.environ.get('PAIR_ENVELOPE_LOCAL',str(OUT.parent/'local/envelope_complete'))).resolve();LOCAL.mkdir(parents=True,exist_ok=True)

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
# Native implementation is unchanged; generated library is local, never pinned-source mutation.
import native_frame
native_frame.P=LOCAL/'native';native_frame.P.mkdir(exist_ok=True);shutil.copyfile(MID/'frame.c',native_frame.P/'frame.c')
scans={'mid':module('envelope_mid_scan',MID/'scan_extended.py'),'high':module('envelope_high_scan',HIGH/'scan_extended.py')}

def exact_events(w,m):
 g.get_context().precision=768;out=[]
 for e in events(w,region(m)):
  h=g.mpfr(e['gamma_decimal'])if e['gamma_decimal']!='2*pi/log(2)'else 2*g.const_pi()/g.log(2)
  out.append((h,g.mpfr(e['beta_decimal']),e['mult']))
 return out

def source_order(path,m):
 sidecar=Path(path).with_suffix('.json')
 if sidecar.exists():
  meta=json.loads(sidecar.read_text());recipe=meta.get('regeneration_recipe')or{}
  if recipe.get('GL_order')is not None:return int(recipe['GL_order'])
  if meta.get('GL_order')is not None:return int(meta['GL_order'])
 return 192 if region(m)=='mid'else 256

def plan(requests=None):
 D=dataset();extra=extras();selected={};choices=[]
 frozen=Path(requests)if requests else OUT/'envelope_complete_requests.csv'
 if frozen.exists():
  for raw in csv.DictReader(frozen.open()):
   choice=dict(raw)
   for key in ('m','q','r'):choice[key]=int(choice[key])
   for key in ('theta','lambda_r','guard'):choice[key]=float(choice[key])
   choice['already_measured']=str(choice['already_measured']).lower()=='true';choices.append(choice)
  weak=choices
 else:
  if requests:raise FileNotFoundError('Frozen requests not found: '+str(frozen))
  weak=[x for x in csv.DictReader((P/'SUMMARY.csv').open())if x['maximum_envelope_tight']=='False'and x['status']!='EMPTY_ADMISSIBLE']
  for x in weak:
   w=x['world'];m=int(x['m']);theta=float(x['theta']);d=D[w,m];r=calculate(d,theta,extra);ss=r['remaining'];eligible=[s for s in ss if s['lambda_r']>=-d['guard']];s=max(eligible or ss,key=lambda s:s['q']);choice=dict(world=w,m=m,theta=theta,q=s['q'],r=s['r'],lambda_r=s['lambda_r'],guard=d['guard'],already_measured='gap'in s,rule='largestq with originallambda_r>=-guard; fallbacklargestq',original_status=s['status']);choices.append(choice)
 for choice in choices:
  if not choice['already_measured']:selected.setdefault((choice['world'],choice['m'],choice['q']),[]).append(choice['theta'])
 tasks=[]
 for m in sorted({m for w,m,q in selected}):
  tasks.append((m,[(w,sorted(q for ww,mm,q in selected if ww==w and mm==m))for w in sorted({ww for ww,mm,q in selected if mm==m})]))
 return D,extra,weak,selected,choices,tasks

def run_group(job):
 m,worldqs=job;D=dataset();records=[]
 for w,qs in worldqs:
  checkpoint=LOCAL/f'{w}_m{m}.json'
  if checkpoint.exists():records+=json.loads(checkpoint.read_text());continue
  t=time.monotonic();A,path=adaptive.get_matrix(w,m);g.get_context().precision=768;ev=exact_events(w,m);cell=[];d=D[w,m];scan=scans[region(m)]
  for q in qs:
   s=next(s for s in d['sectors']if s['q']==q);assert 'gap'not in s
   qstart=time.monotonic();Q=scan.last_null(ev,q,m,768);delta=float(la.svdvals(A@Q)[0]);gap=s['lambda_r']-delta;guard=d['guard'];old_upper=s['upper'];assert gap<=old_upper+guard,(w,m,q,gap,old_upper,guard)
   prior=s['status'];robust_failure=w in('dh','plant')and d['nminus_lower']>0 and prior in('NO_SEPARATOR_NUMERIC','SPECTRAL_NECESSARY_FAIL')
   status=prior if robust_failure else('PASS_NUMERIC'if gap>guard else'FAIL_NUMERIC'if gap< -guard else'UNRESOLVED_NUMERIC_FLOOR')
   if robust_failure:assert gap<=guard
   repl=dict(delta=delta,gap=gap,kind='evaluated',method='PINNED_768BIT_CAUCHY_NULL_WEAK_ENVELOPE_POINT_REFINEMENT',status=status)
   dest=LOCAL/f'{w}_m{m}_q{q}.npz';np.savez_compressed(dest,Q=Q,AQ=A@Q)
   record=dict(world=w,m=m,q=q,r=s['r'],lambda_r=s['lambda_r'],delta=delta,gap=gap,guard=guard,old_absolute_upper=old_upper,within_old_upper=True,source_path=str(path),source_sha256=sha(path),source_A_array_sha256=hashlib.sha256(np.ascontiguousarray(A).tobytes()).hexdigest(),Q_array_sha256=hashlib.sha256(np.ascontiguousarray(Q).tobytes()).hexdigest(),local_Q_AQ_sha256=sha(dest),Q_orthogonality=float(la.norm(Q.T@Q-np.eye(s['r']),2)),frame_bits=768,source_bits=400,source_GL_order=source_order(path,m),source_panels=8,null_constructor_sha256=sha((MID if region(m)=='mid'else HIGH)/'scan_extended.py'),event_decimal_convention='FULL gamma_decimal and exact beta_decimal from pinned sigma; plant2*pi/log2 evaluated at768bits',original_candidate_status=prior,robust_control_failure_preserved=robust_failure,minimum_relative_MGS_pivot='not returned by unchanged last_null; original constructor discards it',replacement=repl,seconds=time.monotonic()-qstart,interpretation='NEW_POINT_INFORMATION_ALSO_APPLIES_TO_UNRESTRICTED_BASELINE_NOT_PAIR_IMPROVEMENT')
   cell.append(record);print('ENVELOPE',w,m,'q',q,'r',s['r'],'gap',gap,'status',status,'sec',round(record['seconds'],3),flush=True)
  checkpoint.write_text(json.dumps(cell,indent=2)+'\n');records+=cell;print('GROUP_WORLD_DONE',w,m,'seconds',round(time.monotonic()-t,3),flush=True)
 return records

def finish(records,initial):
 D,extra,weak,selected,choices,tasks=initial
 for r in records:extra[r['world'],r['m'],r['q']]=r['replacement']
 check=[]
 for(w,m),d in D.items():
  ub=calculate(d,0.,extra);u=ub['best'];assert not u or u['gap']<=d['original_upper']+d['guard']
  for theta in THETAS:
   rr=calculate(d,theta,extra);tight=rr['lower']is not None and rr['upper']-rr['lower']<=4.01*d['guard'];check.append(dict(world=w,m=m,theta=theta,status=rr['status'],empty=rr['status']=='EMPTY_ADMISSIBLE',maximum_envelope_tight=tight,lower=rr['lower'],upper=rr['upper'],guard=d['guard']))
 (OUT/'envelope_complete.json').write_text(json.dumps(records,indent=2)+'\n')
 write_csv('envelope_complete.csv',[{k:v for k,v in r.items()if k!='replacement'}for r in records]);write_csv('envelope_complete_requests.csv',choices);write_csv('envelope_complete_coverage.csv',check)
 broad=[r for r in check if not r['empty']and not r['maximum_envelope_tight']];receipt=dict(status='ALL_NONEMPTY_MAXIMUM_ENVELOPES_TIGHT'if not broad else'REMAINING_BROAD_ENVELOPES',weak_initial_rows=len(weak),distinct_initial_requested_points=len(selected),completed_points=len(records),r_max=max(r['r']for r in records),original_source_recipes_preserved=True,precision_increase=False,all_new_points_within_original_absolute_upper=all(r['within_old_upper']for r in records),new_point_information_applied_unrestricted=True,remaining_broad_rows=broad,rows=2835,empty_rows=sum(r['empty']for r in check),tight_nonempty_rows=sum(not r['empty']and r['maximum_envelope_tight']for r in check),source_arrays_local_only=True)
 (OUT/'envelope_complete_STATUS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--requests',type=Path,help='Frozen envelope_complete_requests.csv/ENVELOPE_REQUESTS.csv; prevents request reselection after finalize');args=ap.parse_args()
 gate=json.loads((OUT/'baseline_manifest.json').read_text());assert gate['status']=='SEVEN_BASELINE_GATES_PASS';initial=plan(args.requests);native_frame.load()
 from concurrent.futures import ProcessPoolExecutor
 with ProcessPoolExecutor(max_workers=2)as pool:records=[r for group in pool.map(run_group,initial[-1])for r in group]
 finish(records,initial)
