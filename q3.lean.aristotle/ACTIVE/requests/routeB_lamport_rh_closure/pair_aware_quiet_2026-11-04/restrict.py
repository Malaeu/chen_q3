"""Reoptimize the SAME sectors by deleting frozen close-pair splits."""
from pathlib import Path
import json,math
from common import *

def calculate(d,theta,extra=None):
 pairs=pairs_for(d['world'],d['m'],theta);forbidden={p['split_q']for p in pairs};allowed=[dict(s)for s in d['sectors']if s['q']not in forbidden]
 if extra:
  allowed=[dict(s,**extra[(d['world'],d['m'],s['q'])])if(d['world'],d['m'],s['q'])in extra else s for s in allowed]
 evaluated=[s for s in allowed if'gap'in s];bounded=[s for s in allowed if'gap'not in s]
 if not allowed:return dict(status='EMPTY_ADMISSIBLE',allowed=0,lower=None,upper=None,best=None,pairs=pairs,forbidden=forbidden,remaining=allowed)
 best=max(evaluated,key=lambda s:s['gap'])if evaluated else None;guard=d['guard'];lower=best['gap']-guard if best else None;upper=max([s['gap']+guard for s in evaluated]+[s['upper']+guard for s in bounded]);maxpoint=best['gap']if best else None
 passes=[s for s in evaluated if s['gap']>guard and not s['status'].startswith('SPECTRAL_NECESSARY')]
 def excluded(s):
  return s['status']in ['SPECTRAL_NECESSARY_FAIL','NO_SEPARATOR_NUMERIC']or('gap'in s and s['gap']< -guard)
 if passes:status='YES_NUMERIC'
 elif all(excluded(s)for s in allowed):status='NO_NUMERIC'
 else:status='UNRESOLVED'
 # Reuse absolute upperbounds; never stale incumbent classifications as failure.
 return dict(status=status,allowed=len(allowed),lower=lower,upper=upper,best=best,pairs=pairs,forbidden=forbidden,remaining=allowed,bounded=bounded,passing_sectors=len(passes),best_measured=maxpoint)

def main():
 data=dataset();rows=[];needs=[];details=[];baselines=[]
 for(w,m),d in data.items():
  es=[s for s in d['sectors']if'gap'in s];measured=max(es,key=lambda s:s['gap']);err=abs(measured['gap']-d['original_gap']);assert err<=d['guard'],(w,m,err);baselines.append(dict(world=w,m=m,selected_q=d['original_q'],original_gap=d['original_gap'],restored_max_evaluated=measured['gap'],difference=err,guard=d['guard'],pass_gate=True))
  for theta in THETAS:
   r=calculate(d,theta);best=r.get('best');rows.append(dict(world=w,m=m,theta=theta,region=d['region'],original_status=d['original_status'],original_gap=d['original_gap'],original_lower=d['original_lower'],original_upper=d['original_upper'],original_q=d['original_q'],pair_count=len(r['pairs']),forbidden_sectors=sum(s['q']in r['forbidden']for s in d['sectors']),original_winner_excluded=d['original_q']in r['forbidden'],allowed_sectors=r['allowed'],status=r['status'],best_measured_gap=best['gap']if best else None,best_measured_q=best['q']if best else None,delta=best['delta']if best else None,lambda_r=best['lambda_r']if best else None,max_gap_lower=r['lower'],max_gap_upper=r['upper'],guard=d['guard'],bound_width=r['upper']-r['lower']if r['upper']is not None and r['lower']is not None else None))
   # Re-evaluate only old bounded sectors that can change a positive verdict/max.
   # Do not chase floor max values. Necessary-rejected controlbounds staybounds.
   if r['allowed']:
    incumbent=max(best['gap']if best else -math.inf,d['guard'])
    for s in r.get('bounded',[]):
     if s['status']=='NO_SEPARATOR_NUMERIC':continue
     if s['lambda_r']>d['guard'] and s['upper']>incumbent+2*d['guard']:needs.append(dict(world=w,m=m,q=s['q'],r=s['r'],lambda_r=s['lambda_r'],theta=theta,old_upper=s['upper'],incumbent=incumbent,guard=d['guard']))
   details.append(dict(world=w,m=m,theta=theta,forbidden_q=sorted(r['forbidden']),allowed_q=[s['q']for s in r['remaining']]))
 write_csv('SUMMARY_INITIAL.csv',rows);write_csv('ADAPTIVE_REQUESTS.csv',needs);write_csv('BASELINE_SCALAR_RESTORE.csv',baselines);(P/'RESTRICTION_MAP.json').write_text(json.dumps(details,indent=2)+'\n');print('2835restrictions;',len(needs),'bounded requests;',len({(x['world'],x['m'])for x in needs}),'cells need additional same-recipe residuals')
if __name__=='__main__':main()
