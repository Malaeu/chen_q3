"""Consume independently replayed MP full spectra without changing pinned float A."""
from pathlib import Path
import json,hashlib,re
import mpmath as mp
mp.mp.dps=110
P=Path(__file__).resolve().parent;records=[]
chosen={}
for path in (P/'matrices/mp_escalation').rglob('*GL*.json'):
 try:a=json.loads(path.read_text())
 except json.JSONDecodeError:continue
 if not a.get('eigenvalues'):continue
 key=(a.get('world','zeta'),a.get('m'));priority=(int(a.get('GL',0)),path.name.startswith('mp_cell'))
 if key not in chosen or priority>chosen[key][0]:chosen[key]=(priority,path,a)
for _,path,a in chosen.values():
 values=a.get('eigenvalues');m=a.get('m');world=a.get('world','zeta')
 if m is None:
  match=re.search(r'_m(\d+)_',path.name);m=int(match.group(1)) if match else None
 if not values or m is None:continue
 cp=P/'cells'/f'{world}_m{m}.json'
 if not cp.exists():continue
 cell=json.loads(cp.read_text());receipt=str(path.relative_to(P));sourcehash=hashlib.sha256(path.read_bytes()).hexdigest()
 for r in cell['rows']:
  index=r['r'];lam=mp.mpf(values[index]);guard=mp.mpf(a.get('roundoff_heuristic','0'));resolved=abs(lam)>guard;r['lambda_r_preferred']=mp.nstr(lam,100) if resolved else None;r['lambda_r_status']='REPLAY_MP_FULL_SPECTRUM' if resolved else 'UNRESOLVED_MP_ROUNDOFF';r['lambda_r_replay_roundoff_guard']=str(guard);r['lambda_r_replay_point_value']=mp.nstr(lam,100);r['lambda_r_replay_provenance']={k:v for k,v in a.items() if k in ['dps','GL','GL_scope','eigenvalue_method','source','source_sha256','source_metadata','quadrature_status','roundoff_heuristic']};r['lambda_r_replay_source']=receipt;r['lambda_r_replay_sha256']=sourcehash
  sm2=r.get('sigma_min_squared');lam=mp.mpf(values[index]);r['twice_sigma_squared_over_lambda_r']=mp.nstr(2*mp.mpf(sm2)/lam,100) if sm2 is not None and lam and resolved else None
 tmp=cp.with_suffix('.lambda.tmp');tmp.write_text(json.dumps(cell,indent=2)+'\n');tmp.replace(cp);records.append(dict(world=world,m=m,source=receipt,sha256=sourcehash))
(P/'lambda_replay.json').write_text(json.dumps(records,indent=2)+'\n');print(records)
