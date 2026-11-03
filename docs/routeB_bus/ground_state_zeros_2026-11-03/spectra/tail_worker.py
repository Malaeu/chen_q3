"""Scheduling only: disjoint immutable m ownership, same reviewed producer."""
import run,json,sys,time,os,hashlib,traceback
from pathlib import Path
role=sys.argv[1];P=run.P;plan=json.loads((P/'tail_schedule_manifest.json').read_text());owned=plan['owned_m'][role]
assert set(plan['owned_m']['even']).isdisjoint(plan['owned_m']['odd'])
assert set(plan['owned_m']['even']+plan['owned_m']['odd']).isdisjoint(plan['owned_m']['late'])
for name,h in plan['producer_hashes'].items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h,(name,'producer changed')
claims=P/'tail_claims';claims.mkdir(exist_ok=True)
def claim(path,data):
 try:fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL)
 except FileExistsError:raise RuntimeError(('exclusive scheduling claim already exists',str(path)))
 with os.fdopen(fd,'w') as f:json.dump(data,f)
who=dict(pid=os.getpid(),role=role);rolefile=claims/f'role_{role}.json';claim(rolefile,who);start=time.monotonic();done=[];skipped=[]
try:
 for m in owned:
  paths=[run.V/f'{w}_m{m}.json' for w in ['zeta','dh','plant']]
  if all(p.exists() and json.loads(p.read_text()).get('v_even0_low') is not None for p in paths):skipped.append(m);continue
  cell=claims/f'm{m}.json';claim(cell,dict(**who,m=m))
  try:run.run(m);done.append(m)
  except Exception as exc:
   run.atomic(P/f'failure_m{m}.json',dict(m=m,status='FAILED_NO_GROUND_CLAIM',error=str(exc),traceback=traceback.format_exc()));print('FAILED',m,repr(exc),flush=True)
  finally:cell.unlink()
 run.atomic(P/f'tail_{role}_complete.json',dict(role=role,owned_m=owned,computed_m=done,skipped_m=skipped,seconds=time.monotonic()-start))
 if role in ['even','odd']:run.atomic(P/f'shard{0 if role=="even" else 1}_complete.json',dict(role=role,owned_m=owned,computed_m=done,seconds=time.monotonic()-start))
finally:rolefile.unlink()
