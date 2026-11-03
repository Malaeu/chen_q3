"""Frozen-baseline spike/pair overlay; descriptive deterministic contingencies."""
from pathlib import Path
import json,csv,math,statistics,collections
from common import *

def deltas():
 D=dataset();out={}
 for key,d in D.items():
  s=d['sectors'][0]
  if'delta'in s:out[key]=dict(delta=s['delta'],q=s['q'],method='PINNED_FIRST_ADMISSIBLE_SECTOR')
 for x in csv.DictReader((HIGH/'max_delta/MAX_DELTA.csv').open()):out[x['world'],int(x['m'])]=dict(delta=float(x['delta']),q=int(x['q']),method='PINNED_INDEPENDENT_HIGH_MAX_DELTA')
 for x in csv.DictReader((P/'control_delta_missing.csv').open()):out[x['world'],int(x['m'])]=dict(delta=float(x['delta']),q=int(x['q']),method='NEW_SAME_RECIPE_ORIGINAL_KAPPA1_RESIDUAL')
 assert len(out)==945,('missingdeltamax',set(D)-set(out))
 for k,d in out.items():assert d['q']==D[k]['sectors'][0]['q'],k
 return out

def correlation(rows,outcome,exposure):
 a=sum(bool(x[outcome])and bool(x[exposure])for x in rows);b=sum(bool(x[outcome])and not bool(x[exposure])for x in rows);c=sum(not bool(x[outcome])and bool(x[exposure])for x in rows);d=len(rows)-a-b-c;den=math.sqrt((a+b)*(c+d)*(a+c)*(b+d));return dict(outcome_and_pair=a,outcome_without_pair=b,not_outcome_and_pair=c,neither=d,outcome_n=a+b,coverage_given_outcome=a/(a+b)if a+b else None,phi=(a*d-b*c)/den if den else None)

def main():
 D=dataset();dm=deltas();rows=[];spikes=[]
 for(w,m),d in D.items():
  grid=list(range(16,301))if m<=300 else list(range(310,601,10));idx=grid.index(m);neighbors=[j for j in range(max(0,idx-5),min(len(grid),idx+6))if j!=idx];logs=[math.log(max(dm[w,grid[j]]['delta'],1e-300))for j in neighbors];med=statistics.median(logs);mad=statistics.median(abs(z-med)for z in logs);scale=1.4826*max(mad,.05);res=math.log(max(dm[w,m]['delta'],1e-300))-med;blind=len(logs)>=4 and res>3*scale and dm[w,m]['delta']>100*d['guard'];known=(w=='zeta'and m==248);unresolved=d['original_status']=='UNRESOLVED';Om=2*math.pi*m/math.log(m);T=Om*d['original_best']['kappa'];allp=event_pairs(w,region(m));nearestOm=min(allp,key=lambda x:abs(x['pair_midpoint']-Om));nearestT=min(allp,key=lambda x:abs(x['pair_midpoint']-T))
  for theta in THETAS:
   ps=pairs_for(w,m,theta);row=dict(world=w,m=m,theta=theta,region=region(m),original_status=d['original_status'],original_optimal_q=d['original_q'],original_gap=d['original_gap'],delta_max_original=dm[w,m]['delta'],delta_source=dm[w,m]['method'],log_residual=res,local_MAD=mad,robust_scale=scale,spike_score=res/scale,blind_spike=blind,known_m248_calibration=known,original_unresolved=unresolved,blind_spike_or_unresolved=blind or unresolved,owner_spike_or_unresolved=blind or known or unresolved,pair_count=len(ps),pair_straddles_Omega=any(x['straddles_Omega']for x in ps),pair_straddles_original_optimum=any(x['straddles_original_optimum']for x in ps),nearest_Omega_left=nearestOm['left_ordinal'],nearest_Omega_right=nearestOm['right_ordinal'],nearest_Omega_normalized_gap=nearestOm['normalized_gap'],nearest_Omega_midpoint_distance=abs(nearestOm['pair_midpoint']-Om),nearest_opt_left=nearestT['left_ordinal'],nearest_opt_right=nearestT['right_ordinal'],nearest_opt_normalized_gap=nearestT['normalized_gap'],nearest_opt_midpoint_distance=abs(nearestT['pair_midpoint']-T))
   rows.append(row)
   if blind or known:spikes.append(row|dict(Omega=Om,original_T=T,nearest_pair_left_gamma=nearestOm['left_gamma'],nearest_pair_right_gamma=nearestOm['right_gamma']))
 write_csv('OVERLAY.csv',rows);write_csv('SPIKES_AND_NEAREST_PAIRS.csv',spikes);write_csv('ORIGINAL_DELTA_MAX.csv',[dict(world=k[0],m=k[1],**v)for k,v in dm.items()]);tables=[]
 for w in['zeta','plant','dh']:
  for theta in THETAS:
   for group,lo,hi in[('integer16_300',16,300),('high310_600',310,600),('all',16,600)]:
    rr=[x for x in rows if x['world']==w and x['theta']==theta and lo<=x['m']<=hi]
    for outcome in['blind_spike','original_unresolved','blind_spike_or_unresolved','owner_spike_or_unresolved']:
     for exposure in['pair_straddles_Omega','pair_straddles_original_optimum']:tables.append(dict(world=w,theta=theta,grid=group,cells=len(rr),outcome=outcome,exposure=exposure,**correlation(rr,outcome,exposure)))
 write_csv('CONTINGENCY.csv',tables);headline=next(x for x in tables if x['world']=='zeta'and x['theta']==.6 and x['grid']=='all'and x['outcome']=='owner_spike_or_unresolved'and x['exposure']=='pair_straddles_original_optimum');blind=next(x for x in tables if x['world']=='zeta'and x['theta']==.6 and x['grid']=='all'and x['outcome']=='blind_spike_or_unresolved'and x['exposure']=='pair_straddles_original_optimum');r=dict(primary_L2=headline,blind_L2=blind,L2_pass=headline['coverage_given_outcome']>=.7,spike_definition='local logmedian/MAD predeclared; anchor248 separateflag; descriptive postselection');(P/'L2_SCORE.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
