"""Bounded local-process batch runner; atomic results retain input hashes."""
from pathlib import Path
import argparse,json,hashlib,sys,traceback,time
from concurrent.futures import ProcessPoolExecutor,as_completed
sys.path.insert(0,str(Path(__file__).resolve().parent))
from census import run,BASE,OUT
from checkpoint_receipts import load_checkpoint
BATCH_PRODUCER_SHA256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def job(path,parity,repeat,force=False):
    if not force:
        d=json.loads(Path(path).read_text());existing=OUT/'results'/f"{d['world']}_{parity}_m{d['m']}.json"
        if existing.exists():
            x=json.loads(existing.read_text())
            if x.get('census_schema_version',0)>=4 and x.get('source_vector_sha256')==hashlib.sha256(Path(path).read_bytes()).hexdigest():return dict(path=path,parity=parity,status='DONE',already_current=True)
    try:
        wall_start=time.monotonic();cpu_start=time.process_time();result=run(path,parity,repeat)
        receipt=dict(world=result['world'],m=result['m'],parity=parity,cpu_seconds=time.process_time()-cpu_start,wall_seconds=time.monotonic()-wall_start,source_vector_sha256=result['source_vector_sha256'],census_producer_sha256=result.get('census_producer_sha256'),batch_wrapper_sha256=BATCH_PRODUCER_SHA256,scope='Observed runtime for an ordinary authorized cell, not a benchmark or numerical method change.')
        folder=OUT/'runtime_receipts';folder.mkdir(exist_ok=True);target=folder/f"{result['world']}_{parity}_m{result['m']}.json";tmp=target.with_suffix('.tmp');tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(target)
        return dict(path=path,parity=parity,status='DONE')
    except Exception as e:
        row=dict(path=path,parity=parity,status='FAILED_NO_ROOT_CLAIM',error=repr(e),traceback=traceback.format_exc());f=OUT/'failures';f.mkdir(exist_ok=True);(f/(Path(path).stem+'_'+parity+'.json')).write_text(json.dumps(row,indent=2)+'\n');return row

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=2);ap.add_argument('--ms',type=int,nargs='+');ap.add_argument('--all-parities',action='store_true');ap.add_argument('--repeat',action='store_true');ap.add_argument('--force',action='store_true');a=ap.parse_args();jobs=[]
    checkpoint=load_checkpoint()
    for d in sorted(checkpoint['sources'].values(),key=lambda q:(q['m'],q['world'])):
        p=Path(d['path'])
        if a.ms and d['m'] not in a.ms:continue
        ps=['even'];gp=d.get('global_ground_parity')
        if a.all_parities:ps.append('odd')
        elif d.get('ground_resolved') and gp=='odd':ps.append('odd')
        for parity in ps:
            if not d.get(parity+'_ground_resolved',d.get('ground_resolved')):continue
            result=OUT/'results'/f"{d['world']}_{parity}_m{d['m']}.json";old=checkpoint['roots'].get(str(result))
            if old and not a.force and old.get('census_schema_version',0)>=4 and old.get('root_output_digits',0)>=180 and old.get('has_replay_floor') and old.get('source_vector_sha256')==d['source_sha256']:continue
            jobs.append((str(p),parity,a.repeat,a.force))
    print(json.dumps(dict(jobs=len(jobs),workers=a.workers)),flush=True)
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        futures=[pool.submit(job,*j) for j in jobs]
        for f in as_completed(futures):
            r=f.result()
            if r['status']!='DONE':print(json.dumps(r),flush=True)
    print(json.dumps(dict(status='BATCH_FINISHED',jobs=len(jobs))),flush=True)
if __name__=='__main__':main()
