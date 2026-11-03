"""Freeze only after all producers exit and the complete final checks pass."""
from pathlib import Path
import json,hashlib,datetime
P=Path(__file__).resolve().parent
checks=json.loads((P/'FINAL_CHECKS.json').read_text());complete=json.loads((P/'completeness.json').read_text())
assert checks['status']=='COMPLETE_855_NUMERICAL_GROUND_CELLS' and complete['completed_world_cells']==855
for i in [0,1]:assert (P/f'shard{i}_complete.json').exists()
if (P/'tail_schedule_manifest.json').exists():
 for role in ['even','odd','late']:assert (P/f'tail_{role}_complete.json').exists()
active=[]
for d in Path('/proc').iterdir():
 if not d.name.isdigit():continue
 try:
  args=(d/'cmdline').read_bytes().decode().split('\0')
  if len(args)>1 and Path(args[0]).name.startswith('python') and args[1] in [str(P/n) for n in ['shard.py','tail_worker.py','finish.py','watch_finish.py']]:active.append(int(d.name))
 except (FileNotFoundError,ProcessLookupError,PermissionError):pass
assert not active, ('producers still active',active)
proofs=[]
for name in ['pre_shifted_adoption_snapshot.json','pre_tail_schedule_snapshot.json']:
 snapshot=P/name
 if snapshot.exists():
  old=json.loads(snapshot.read_text());changed=[n for n,a in old.items() if hashlib.sha256((P/'vectors'/n).read_bytes()).hexdigest()!=a['raw_sha256']]
  proofs.append(dict(snapshot=name,preexisting_world_files=len(old),changed_files=changed,all_raw_SHA_unchanged=not changed))
(P/'PRESERVATION_FINAL.json').write_text(json.dumps(dict(checks=proofs,all_pass=all(x['all_raw_SHA_unchanged'] for x in proofs)),indent=2)+'\n')
assert all(x['all_raw_SHA_unchanged'] for x in proofs), 'preexisting world file changed'
entries=[]
for f in sorted(P.rglob('*')):
 if f.is_file() and f.name!='FROZEN_MANIFEST.json':
  raw=f.read_bytes();entries.append(dict(path=str(f.relative_to(P)),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
manifest=dict(status='FROZEN_COMPLETE_SPECTRA_SUBTREE',created_UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),world_cells=855,integer_m_count=285,integer_range=[16,300],all_producers_exited=True,preferred_HIGH_native_full_lowest_two_unchanged=True,LOW_refinement_second_pair_not_computed_qualification_preserved=True,file_count_excluding_manifest=len(entries),bytes_excluding_manifest=sum(e['bytes'] for e in entries),excluded_files=['FROZEN_MANIFEST.json'],mutation_contract='No later writes without notifying the parent; do not rerun producer/finalization scripts against this frozen subtree.',files=entries)
out=P/'FROZEN_MANIFEST.json';out.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status=manifest['status'],file_count=manifest['file_count_excluding_manifest'],bytes=manifest['bytes_excluding_manifest'],manifest_sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
