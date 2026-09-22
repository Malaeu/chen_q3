import dataclasses,hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path.cwd()))
from orchestrator import team_records as tr
from orchestrator.tests.test_workflow_runtime import TeamRecordsTests as T
current=T.provenance_assignment();current['assignment_id']='Z_CURRENT_RESULT'
old=T.provenance_assignment();old['assignment_id']='A_OLD_LAUNCH'
raw=b'legacy assignments\n'
for a in [old,current]:
 raw,_=tr.prepare_assignment(raw,a,hashlib.sha256(raw).hexdigest())
rows=tr.read_registry(raw,'assignments')
issue_raw,_=tr.prepare_report(b'legacy issues\n',T.report(),hashlib.sha256(b'legacy issues\n').hexdigest())
issues=tr.read_registry(issue_raw,'issues')
ctx=T.provenance_context(current)
result=ctx.observations[current['assignment_id']][1]
event=T.transition(issues,'CONFIRMED_BUG',actor='reporter-task',evidence=[{'locator':result['output_locator'],'sha256':result['output_sha256']}])
print('CURRENT_ONLY',tr.validate_issue_event_actor(event,rows,ctx)['assignment_id'])
oldctx=T.provenance_context(old)
combined=dataclasses.replace(ctx,observations={**ctx.observations,old['assignment_id']:oldctx.observations[old['assignment_id']][:1]})
try:
 tr.validate_issue_event_actor(event,rows,combined)
except tr.TeamRecordError as exc:
 print('WITH_UNRELATED_OLD_LAUNCH',str(exc))
 assert 'NATIVE_OBSERVATION_MISSING' in str(exc)
else:
 raise AssertionError('expected reproduction did not occur')
print('REPRODUCED_CURRENT_SOURCE')
