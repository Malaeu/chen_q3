"""Owner authorized final119-only originalmpmath100/GL160 run,120CPUhardwatch."""
from pathlib import Path
import sys,json,time,threading,os,hashlib,importlib.util
P=Path(__file__).resolve().parent;HELPER=P.parent/'batch_mp.py'
def main():
 target=P/'mp_cell_dh_m119_dps100_GL160.json'
 if target.exists():print('NOOP119alreadycomplete');return
 start=time.process_time();wall=time.perf_counter();stop=threading.Event()
 receipt=dict(status='RUNNING',authority='Parent explicitly authorized final119-only originalmethod replay under a separate120CPU extension, after preserved prior budgets.',m=119,dps=100,GL=160,eig_method='original mpmath eigsy',CPU_budget_seconds=120,wall_watch_seconds=240,helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest())
 (P/'FINAL119_ORIGINAL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 def watch():
  while not stop.wait(.1):
   if time.process_time()-start>=120 or time.perf_counter()-wall>=240:
    receipt.update(status='TIMEOUT',CPU_seconds=time.process_time()-start,wall_seconds=time.perf_counter()-wall);(P/'FINAL119_ORIGINAL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');os._exit(124)
 thread=threading.Thread(target=watch,daemon=True);thread.start()
 spec=importlib.util.spec_from_file_location('original_batch_final',HELPER);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 sys.argv=[str(HELPER),'--ms','119','--worlds','dh','--dps','100','--order','160','--label','DH_final_original','--out',str(P)]
 mod.main();stop.set();z=json.loads(target.read_text());assert z['world']=='dh' and z['m']==119 and len(z['eigenvalues'])==120
 z['quadrature_status']='Fresh MP100 DH source, GL160; diagnostic quadrature, not an interval certificate';target.write_text(json.dumps(z,indent=2)+'\n')
 receipt.update(status='COMPLETE',CPU_seconds=time.process_time()-start,wall_seconds=time.perf_counter()-wall,output_sha256=hashlib.sha256(target.read_bytes()).hexdigest());(P/'FINAL119_ORIGINAL_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
