"""Recover only absent B100 cells after the execution-environment outage."""
import stitch as s
from stitch import *
import hashlib

def main():
 mp.mp.dps=100;start=time.monotonic();specs=[(m,w,c) for m in [16,24,32,40] for w in ['zeta','dh','plant'] for c in ['kappa1','cquarter','chalf']]
 path=lambda m,w,c:P/f'cell_{w}_m{m}_{c}_dps100.json'
 existing={str(path(m,w,c).name):hashlib.sha256(path(m,w,c).read_bytes()).hexdigest() for m,w,c in specs if path(m,w,c).exists()}
 missing=[(m,w,c) for m,w,c in specs if not path(m,w,c).exists()]
 if not missing and (P/'metrics_dps100.csv').exists():
  print('NOOP: all36 cell checkpoints and assembled100-digit metrics already exist; preserving recovery receipt.',flush=True);return
 receipt=dict(status='DIAGNOSTIC_NEVER_A_PROOF',reason='Execution-environment outage terminated primary100-digit process; no live PID observed.',existing_count=len(existing),existing_sha256=existing,missing_cells=missing,method='Resume only absent cell files; assemble completed metrics from immutable existing and resumed checkpoints.')
 (P/'RESUME100.json').write_text(json.dumps(receipt,indent=2)+'\n');print('RESUME missing',missing,flush=True)
 # Exact-result memoization only: repeated identical inertia inputs need no new eigensolve.
 original=s.inertia;cache={}
 def memo(A,guard):
  key=(A.rows,A.cols,fmt(guard),hashlib.sha256('|'.join(fmt(x) for x in A).encode()).hexdigest())
  if key not in cache:cache[key]=original(A,guard)
  return cache[key]
 s.inertia=memo
 cs=dict(kappa1=mp.mpf(0),cquarter=mp.mpf(1)/4,chalf=mp.mpf(1)/2)
 for m,w in sorted(set((m,w) for m,w,c in missing)):
  ctx=s.common(m,w,100)
  for _,_,c in [x for x in missing if x[0]==m and x[1]==w]:s.one(m,w,100,cs[c],c,ctx)
 for name,h in existing.items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h,name
 rows=[json.loads(path(m,w,c).read_text())['metrics'] for m,w,c in specs]
 with (P/'metrics_dps100.csv').open('w',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=rows[0]);writer.writeheader();writer.writerows(rows)
 receipt.update(completed=True,resume_seconds=time.monotonic()-start,total_rows=len(rows),existing_files_unchanged=True);(P/'RESUME100.json').write_text(json.dumps(receipt,indent=2)+'\n')
 (P/'run_dps100.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',dps=100,rows=len(rows),resumed=True,resume_seconds=receipt['resume_seconds'],recomputed_cells=len(missing)),indent=2)+'\n');print('COMPLETE',receipt['resume_seconds'],flush=True)
if __name__=='__main__':main()
