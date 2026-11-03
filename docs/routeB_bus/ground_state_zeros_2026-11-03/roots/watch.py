"""Consume streaming spectral cells until the full requested integer grid is present.
A cell with an unresolved parity is recorded as unresolved, never assigned a ground.
"""
from pathlib import Path
import argparse,subprocess,sys,time,json,hashlib
from checkpoint_receipts import load_checkpoint
P=Path(__file__).resolve().parent;BASE=P.parent

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=2);ap.add_argument('--defer-aggregate',action='store_true');a=ap.parse_args();sweep=0
 while True:
  sweep+=1;start=time.monotonic()
  code=subprocess.call([sys.executable,str(P/'batch.py'),'--workers',str(a.workers)])
  if not a.defer_aggregate:subprocess.check_call([sys.executable,str(P/'aggregate.py')])
  checkpoint=load_checkpoint();sources=list(checkpoint['sources'].values());resolved=0;unresolved=[];pending=[]
  receipts={f"{r['world']}|{r['m']}|{r['parity']}":r['source_vector_sha256'] for r in checkpoint['roots'].values() if r['census_schema_version']>=4 and r['root_output_digits']>=180 and r['has_replay_floor']}
  for d in sources:
   required=['even'] if d.get('even_ground_resolved') else []
   if d.get('ground_resolved') and d.get('global_ground_parity')=='odd':required.append('odd')
   for parity in required:
    if receipts.get(f"{d['world']}|{d['m']}|{parity}")!=d['source_sha256']:pending.append(dict(world=d['world'],m=d['m'],parity=parity))
   if d.get('even_ground_resolved'):resolved+=1
   else:unresolved.append(dict(world=d['world'],m=d['m'],parity='even',status=d['status']))
  files=sources
  status=dict(sweep=sweep,source_cells=len(files),resolved_even_cells=resolved,unresolved_even_cells=unresolved,pending_root_cells=pending,pending_root_count=len(pending),expected_source_cells=3*285,last_batch_exit=code,sweep_seconds=time.monotonic()-start,status='RUNNING')
  if len(files)==855 and not pending:
   if a.defer_aggregate:subprocess.check_call([sys.executable,str(P/'aggregate.py')])
   status['status']='FINISHED_WITH_EXPLICIT_UNRESOLVED_CELLS' if unresolved else 'FINISHED_ALL_SOURCE_CELLS'
   (P/'watch_status.json').write_text(json.dumps(status,indent=2)+'\n');print(json.dumps(status),flush=True);break
  (P/'watch_status.json').write_text(json.dumps(status,indent=2)+'\n');print(json.dumps({k:v for k,v in status.items() if k not in ('unresolved_even_cells','pending_root_cells')}),flush=True)
  time.sleep(15)
if __name__=='__main__':main()
