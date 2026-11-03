"""C=2 rank-sector lookup only, from the same saved counts; no new projector."""
from core import *
mp.mp.dps=80
for path in (P/'cells').glob('*_m*.json'):
 cell=json.loads(path.read_text());m=cell['m'];world=cell['world'];d=m+1;omega=2*mp.pi*m/mp.log(m);base=next(r for r in cell['rows'] if r['variant']=='base');count=base['N_A2'];target=d-count;ev=events(world);cumulative=0;lo=hi=None
 if target==0:lo=mp.mpf(0);hi=mp.mpf(ev[0]['gamma'])
 for i,e in enumerate(ev[:-1]):
  cumulative+=1 if e['kind']=='line' else 2
  if cumulative==target:lo=mp.mpf(e['gamma']);hi=mp.mpf(ev[i+1]['gamma']);break
 found=[r for r in cell['rows'] if r['q']==target];guards=[r['delta_less_than_2'] for r in found]
 a=dict(B=None,threshold_name='C=2',mu=2,signed_count=count,count_unresolved=base['N_A2_unresolved'],target_rank=target,kappa_sector_left=mp.nstr(lo/omega,65)if lo is not None else None,kappa_sector_right=mp.nstr(hi/omega,65)if hi is not None else None,status='UNRESOLVED_THRESHOLD_COUNT' if base['N_A2_unresolved'] else('EXACT_RANK_SECTOR' if lo is not None else'NO_HEIGHT_CUTOFF_REALIZES_TARGET_RANK'),left_boundary_strict=True,right_boundary_included=True,existing_same_rank_projector_cases=len(found),existing_same_rank_delta_lt2_any=any(guards)if found else None,no_new_projector=True)
 cell['adaptive_thresholds']=[x for x in cell['adaptive_thresholds'] if x.get('threshold_name')!='C=2']+[a];temp=path.with_suffix('.c2.tmp');temp.write_text(json.dumps(cell,indent=2)+'\n');temp.replace(path)
