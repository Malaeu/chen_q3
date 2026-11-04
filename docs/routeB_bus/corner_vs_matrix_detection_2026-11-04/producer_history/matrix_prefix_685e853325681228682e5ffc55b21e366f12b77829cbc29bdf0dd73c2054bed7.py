"""Consecutive integer prefixes; no monotonicity assumption or skipped firsts."""
from pathlib import Path
import json,time
from matrix_probe import run_cell,GAMMAS,AS,cutoff,atomic,P
corners=json.loads((P/'corner_summary.json').read_text());admit={r['gamma']:r['m_admit'] for r in corners['cases'] if r['a']=='0'}
started=time.process_time();summaries=[]
for gamma in GAMMAS:
 first={name:None for name,a in AS if name!='0'};last=None;reason='COMPLETE_FIRSTS'
 for m in range(admit[gamma],3001):
  # Every actual matrix-grid cell includes every admissible parameter and a0.
  d=run_cell(m,[g for g in GAMMAS if m>=admit[g]])
  for r in d['cases']:
   if r['gamma']==gamma and r['a']!='0' and r['detected'] and first[r['a']] is None:first[r['a']]=m
  last=m
  atomic(P/'prefix_status.json',dict(current_gamma=gamma,through_m=m,first=first,completed=summaries,CPU_seconds=time.process_time()-started,preregistration='bc9204929faccc66f952ff9df9273e0b94afed4e'))
  if all(x is not None for x in first.values()):break
  if time.process_time()-started>600:reason='FEASIBLE_CPU_CAP_600_SECONDS';break
 summaries.append(dict(gamma=gamma,m_admit=admit[gamma],consecutive_through=last,first=first,status=reason))
atomic(P/'prefix_summary.json',dict(status='COMPLETE_INTEGER_FIRST_DETECTIONS' if all(all(v is not None for v in r['first'].values()) for r in summaries) else 'PREFIX_CENSORED_AT_FEASIBLE_CAP',groups=summaries,CPU_seconds=time.process_time()-started,source='Each group starts exactly at first admissible integer, visits every integer until all three detections or explicitcap; float detection threshold -1e-6, MP confirmation pending'))
print(json.dumps(summaries,indent=2),flush=True)
