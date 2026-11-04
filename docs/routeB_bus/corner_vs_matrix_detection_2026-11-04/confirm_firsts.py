"""Fresh >=77-digit negative Rayleigh witnesses for first raw detections."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,hashlib,time,multiprocessing,concurrent.futures
from decimal import Decimal
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'builder'))

def job(t):
 from rayleigh_pinned import evaluate
 a,gamma,m=t;vfile=P/'vectors'/f'g{gamma}_a{a.replace("/","_")}_m{m}.json';raw=vfile.read_bytes();v=json.loads(raw)
 out=evaluate(m,v['vector'],a=a,gamma=gamma,bits=256)
 out.update(a=a,gamma=gamma,lambda_float=v['lambda_float'],vector_path=str(vfile.relative_to(P)),vector_file_sha256=hashlib.sha256(raw).hexdigest(),helper_sha256=hashlib.sha256((P/'builder/rayleigh_pinned.py').read_bytes()).hexdigest())
 assert Decimal(out['total_rayleigh'])<Decimal('-1e-6'),out
 out['status']='PASS_HIGH_PRECISION_NEGATIVE_WITNESS';dst=P/'confirmation'/f'g{gamma}_a{a.replace("/","_")}_m{m}.json';dst.parent.mkdir(exist_ok=True);tmp=dst.with_suffix('.tmp');tmp.write_text(json.dumps(out,indent=2)+'\n');tmp.replace(dst)
 return dict(a=a,gamma=gamma,m=m,total_rayleigh=out['total_rayleigh'],CPU_seconds=out['cpu_seconds'])

def main():
 d=json.loads((P/'prefix_summary.json').read_text());assert d['status']=='COMPLETE_INTEGER_FIRST_DETECTIONS'
 tasks=[(a,g['gamma'],m) for g in d['groups'] for a,m in g['first'].items()]
 with concurrent.futures.ProcessPoolExecutor(max_workers=2,mp_context=multiprocessing.get_context('spawn')) as pool:
  for r in pool.map(job,tasks):print(json.dumps(r),flush=True)
 files=sorted((P/'confirmation').glob('g*_a*_m*.json'));assert len(files)==12
 result=dict(status='ALL_12_FIRST_DETECTIONS_CONFIRMED_AT_HIGH_PRECISION',cases=12,bits=256,working_bits=296,scope='Fresh full pinned source and fixed binary64 vector. Negative Rayleigh witness proves numerical detection sign; not a complete high-precision eigenvalue ordering/interval certificate.',files=[str(f.relative_to(P)) for f in files])
 (P/'confirmation_summary.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
