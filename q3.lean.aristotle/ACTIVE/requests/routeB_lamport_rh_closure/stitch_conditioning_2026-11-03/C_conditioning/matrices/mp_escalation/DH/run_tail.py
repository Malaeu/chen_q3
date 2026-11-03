"""One owner-authorized,300CPU-second missing-only DH tail; identical source/method."""
from pathlib import Path
import sys,json,time,signal,resource,importlib.util,hashlib
P=Path(__file__).resolve().parent;HELPER=P.parent/'batch_mp.py';MATS=P.parents[1]
class BudgetExpired(Exception):pass

def main():
 started=time.process_time();requested=[];skipped=[];existing={}
 if (P/'TAIL_RECEIPT.json').exists():
  old=json.loads((P/'TAIL_RECEIPT.json').read_text())
  if old.get('status')!='RUNNING':print('NOOP: the single authorized tail attempt is already closed');return
  raise RuntimeError('Prior tail attempt still RUNNING; reconcile instead of relaunching')
 primary=json.loads((P/'RUN_RECEIPT.json').read_text());assert primary['status'] in ['COMPLETE','PARTIAL_CPU_BUDGET']
 for m in range(16,121):
  meta=json.loads((MATS/f'cell_dh_m{m}.json').read_text());file=P/f'mp_cell_dh_m{m}_dps100_GL160.json'
  if meta.get('mp_eigenvalues') or file.exists():skipped.append(m)
  else:assert meta.get('matrix_cache') is None,m;requested.append(m)
  if file.exists():existing[file.name]=hashlib.sha256(file.read_bytes()).hexdigest()
 budget=min(300,int(900-primary.get('controller_observed_CPU_seconds',600)-5));assert budget>0
 receipt=dict(status='RUNNING',authority='Parent allowed one measured300CPU missing-only tail; this phase uses the remaining900total budget.',requested=requested,skipped_existing=skipped,existing_sha256=existing,budget_CPU_seconds=budget,helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest())
 (P/'TAIL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 if not requested:
  receipt.update(status='NO_WORK',completed=[],unfinished=[],worker_CPU_seconds=time.process_time()-started);(P/'TAIL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print('NOOP all requested DH spectra already cached');return
 def alarm(sig,frame):raise BudgetExpired('300CPU seconds reached; preserve completed checkpoints')
 signal.signal(signal.SIGXCPU,alarm);resource.setrlimit(resource.RLIMIT_CPU,(budget,budget+30))
 spec=importlib.util.spec_from_file_location('shared_batch',HELPER);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 failure=None;cell_costs=[]
 try:
  status='COMPLETE'
  for m in requested:
   elapsed=time.process_time()-started
   if elapsed>=budget or (cell_costs and elapsed+max(cell_costs)>budget):status='PARTIAL_CPU_BUDGET';break
   sys.argv=[str(HELPER),'--ms',str(m),'--worlds','dh','--dps','100','--order','160','--label','DH_tail','--out',str(P)]
   before=time.process_time();mod.main();cell_costs.append(time.process_time()-before)
 except BudgetExpired as e:status='PARTIAL_CPU_BUDGET';failure=str(e)
 except Exception as e:status='FAILED';failure=repr(e)
 done=[]
 for file in P.glob('mp_cell_dh_m*_dps100_GL160.json'):
  r=json.loads(file.read_text());r['quadrature_status']='Fresh MP100 DH source, GL160; diagnostic quadrature, not an interval certificate';file.write_text(json.dumps(r,indent=2)+'\n');done.append(r['m'])
 for name,h in existing.items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h,name
 receipt.update(status=status,completed=[m for m in sorted(done) if m in requested],unfinished=[m for m in requested if m not in done],worker_CPU_seconds=time.process_time()-started,failure=failure,existing_files_unchanged=True,per_cell_CPU_seconds=cell_costs,explicit_between_cell_budget_checks=True)
 (P/'TAIL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
 if status=='FAILED':raise RuntimeError(failure)
if __name__=='__main__':main()
