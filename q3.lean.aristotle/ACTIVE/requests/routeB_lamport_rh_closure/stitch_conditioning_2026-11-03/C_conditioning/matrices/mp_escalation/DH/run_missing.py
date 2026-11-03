"""Bounded native DH full-spectrum replay, checkpoints before CPU budget close."""
from pathlib import Path
import sys,json,time,signal,resource,importlib.util,hashlib
P=Path(__file__).resolve().parent;HELPER=P.parent/'batch_mp.py';MATS=P.parents[1]
class BudgetExpired(Exception):pass

def main():
 started=time.process_time();requested=[];skipped=[]
 for m in range(16,121):
  meta=json.loads((MATS/f'cell_dh_m{m}.json').read_text())
  if meta.get('mp_eigenvalues') or (P/f'mp_cell_dh_m{m}_dps100_GL160.json').exists():skipped.append(m)
  else:
   assert meta.get('matrix_cache') is None,m
   requested.append(m)
 if not requested:print('NOOP all requested DH spectra already cached; preserving completed receipts');return
 receipt=dict(status='RUNNING',requested=requested,skipped_existing=skipped,budget_CPU_seconds=600,helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest())
 (P/'RUN_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 if not requested:print('NOOP all requested DH spectra already cached');return
 def alarm(sig,frame):raise BudgetExpired('600 CPU seconds reached; preserve completed checkpoints')
 signal.signal(signal.SIGXCPU,alarm);resource.setrlimit(resource.RLIMIT_CPU,(600,630))
 spec=importlib.util.spec_from_file_location('shared_batch',HELPER);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 sys.argv=[str(HELPER),'--ms',*map(str,requested),'--worlds','dh','--dps','100','--order','160','--label','DH_missing','--out',str(P)]
 failure=None
 try:mod.main();status='COMPLETE'
 except BudgetExpired as e:status='PARTIAL_CPU_BUDGET';failure=str(e)
 except Exception as e:status='FAILED';failure=repr(e)
 done=[]
 for f in P.glob('mp_cell_dh_m*_dps100_GL160.json'):
  r=json.loads(f.read_text());r['quadrature_status']='Fresh MP100 DH source, GL160; diagnostic quadrature, not an interval certificate';f.write_text(json.dumps(r,indent=2)+'\n');done.append(r['m'])
 receipt.update(status=status,completed=sorted(done),unfinished=[m for m in requested if m not in done],worker_CPU_seconds=time.process_time()-started,failure=failure)
 (P/'RUN_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
 if status=='FAILED':raise RuntimeError(failure)
if __name__=='__main__':main()
