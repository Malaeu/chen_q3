from pathlib import Path
import json,csv,statistics,math,collections
from common import *
from restrict import calculate

def extras():
 xs=json.loads((P/'ADAPTIVE_REFINEMENTS.json').read_text())
 for name in ['envelope_complete.json','ENVELOPE_REFINEMENTS.json']:
  if(P/name).exists():xs+=json.loads((P/name).read_text())
 return {(x['world'],x['m'],x['q']):x['replacement']for x in xs}
def main():
 D=dataset();extra=extras();rows=[];changes=[];details=[]
 for(w,m),d in D.items():
  unrestricted=calculate(d,0.,extra);ub=unrestricted['best'];assert not ub or ub['gap']<=d['original_upper']+d['guard'],(w,m,'publishedenvelopebroken')
  if ub and ub['gap']>d['original_gap']+d['guard']:changes.append(dict(world=w,m=m,published_status=d['original_status'],published_measured_gap=d['original_gap'],published_upper=d['original_upper'],refined_status=unrestricted['status'],refined_measured_gap=ub['gap'],interpretation='INFORMATION_REFINEMENT_INSIDE_OLD_ENVELOPE_NOT_PAIR_IMPROVEMENT'))
  previous=math.inf
  for theta in THETAS:
   r=calculate(d,theta,extra);b=r['best'];point=b['gap']if b else None
   if point is not None:
    assert point<=ub['gap']+1e-14;assert point<=previous+1e-14;previous=point
   q=b['q']if b else None
   row=dict(world=w,m=m,theta=theta,region=d['region'],original_status=d['original_status'],original_gap=d['original_gap'],original_lower=d['original_lower'],original_upper=d['original_upper'],original_q=d['original_q'],refined_unrestricted_status=unrestricted['status'],refined_unrestricted_measured_gap=ub['gap']if ub else None,refined_unrestricted_lower=unrestricted['lower'],refined_unrestricted_upper=unrestricted['upper'],pair_count=len(r['pairs']),forbidden_sectors=sum(s['q']in r['forbidden']for s in d['sectors']),original_winner_excluded=d['original_q']in r['forbidden'],allowed_sectors=r['allowed'],status=r['status'],best_measured_gap=point,best_measured_q=q,delta=b['delta']if b else None,lambda_r=b['lambda_r']if b else None,max_gap_lower=r['lower'],max_gap_upper=r['upper'],guard=d['guard'],bound_width=r['upper']-r['lower']if r['upper']is not None and r['lower']is not None else None,maximum_envelope_tight=r['upper']-r['lower']<=4.01*d['guard']if r['upper']is not None and r['lower']is not None else False)
   rows.append(row);details.append(dict(world=w,m=m,theta=theta,forbidden_q=sorted(r['forbidden']),allowed_q=[s['q']for s in r['remaining']],all_allowed_event_clusters_remain_whole=True))
 write_csv('SUMMARY.csv',rows);write_csv('BASELINE_INFORMATION_REFINEMENTS.csv',changes);(P/'RESTRICTION_MAP.json').write_text(json.dumps(details,indent=2)+'\n')
 counts=[];blocks=[]
 for w in['zeta','plant','dh']:
  for theta in THETAS:
   for group,lo,hi in[('integer16_300',16,300),('high310_600',310,600),('all',16,600)]:
    rr=[x for x in rows if x['world']==w and x['theta']==theta and lo<=x['m']<=hi];counts.append(dict(world=w,theta=theta,grid=group,cells=len(rr),original_yes=sum(x['original_status']=='YES_NUMERIC'for x in rr),original_unresolved=sum(x['original_status']=='UNRESOLVED'for x in rr),pair_yes=sum(x['status']=='YES_NUMERIC'for x in rr),pair_unresolved=sum(x['status']=='UNRESOLVED'for x in rr),pair_no=sum(x['status']=='NO_NUMERIC'for x in rr),empty=sum(x['status']=='EMPTY_ADMISSIBLE'for x in rr),lost_resolved_positive=sum(x['original_status']=='YES_NUMERIC'and x['status']!='YES_NUMERIC'for x in rr),gained_positive_from_original_unresolved=sum(x['original_status']=='UNRESOLVED'and x['status']=='YES_NUMERIC'for x in rr)))
   for start in range(310,600,50):
    rr=[x for x in rows if x['world']==w and x['theta']==theta and start<=x['m']<=start+40];assert len(rr)==5
    blocks.append(dict(world=w,theta=theta,m_start=start,m_end=start+40,median_original_measured=statistics.median(x['original_gap']for x in rr),median_original_lower=statistics.median(x['original_lower']for x in rr),median_original_upper=statistics.median(x['original_upper']for x in rr),median_pair_measured=statistics.median(x['best_measured_gap']for x in rr)if all(x['best_measured_gap']is not None for x in rr)else None,point_count=sum(x['best_measured_gap']is not None for x in rr),median_pair_lower=statistics.median(x['max_gap_lower']if x['max_gap_lower']is not None else -math.inf for x in rr),median_pair_upper=statistics.median(x['max_gap_upper']if x['max_gap_upper']is not None else -math.inf for x in rr),resolved_positive_count=sum(x['status']=='YES_NUMERIC'for x in rr),unresolved_count=sum(x['status']=='UNRESOLVED'for x in rr)))
 write_csv('COUNTS.csv',counts);write_csv('BLOCK_MEDIANS.csv',blocks)
 print('T2complete',len(rows),'cells; informationrefined',len(changes))
 for x in counts:
  if x['world']=='zeta'and x['grid']=='high310_600':print(x)
if __name__=='__main__':main()
