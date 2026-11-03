"""Aggregate the complete sector scan, never equating C=2 with zero."""
from pathlib import Path
import csv,json,gzip,io,hashlib
P=Path(__file__).resolve().parent
def write_csv(path,rows):
 with path.open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
allrows=[];summaries=[]
for w in ['zeta','plant','dh']:
 for m in range(16,121):
  j=json.loads((P/'cells'/f'{w}_m{m}.json').read_text());s=j['summary'];rs=j['sectors'];allrows.extend(rs)
  for name,group in [('ge1',[r for r in rs if r['intersects_kappa_ge1']]),('admissible',[r for r in rs if r['necessary_gap']>r['numeric_guard']]),('ge1_admissible',[r for r in rs if r['intersects_kappa_ge1'] and r['necessary_gap']>r['numeric_guard']])]:
   best=max(group,key=lambda r:r['gap'])if group else None
   for k in ['r','delta','lambda_r','gap','status','kappa_mid','kappa_left_open','kappa_right_closed']:s['best_'+name+'_'+k]=best[k]if best else None
  s['ge1_pass_below_C2']=sum(r['status']=='PASS_NUMERIC' and r['intersects_kappa_ge1'] and r['lambda_r_category']=='POSITIVE_BELOW_C2'for r in rs)
  s['ge1_pass_delta_below_C2']=sum(r['status']=='PASS_NUMERIC' and r['intersects_kappa_ge1'] and r['delta']+r['numeric_guard']<2 for r in rs)
  summaries.append(s)
write_csv(P/'separator_summary.csv',summaries)
buf=io.StringIO(newline='');w=csv.DictWriter(buf,fieldnames=list(allrows[0]));w.writeheader();w.writerows(allrows)
with (P/'all_sectors.csv.gz').open('wb')as f:
 with gzip.GzipFile(fileobj=f,mode='wb',mtime=0)as z:z.write(buf.getvalue().encode())
summary={}
for world in ['zeta','plant','dh']:
 ss=[s for s in summaries if s['world']==world];rr=[r for r in allrows if r['world']==world];info={}
 for status in ['YES_NUMERIC','NO_NUMERIC','UNRESOLVED']:
  info['any_'+status]=[s['m']for s in ss if s['separator_any_kappa']==status];info['ge1_'+status]=[s['m']for s in ss if s['separator_kappa_ge1']==status]
 info['ge1_pass_below_C2_m']=[s['m']for s in ss if s['ge1_pass_below_C2']];info['ge1_pass_delta_below_C2_m']=[s['m']for s in ss if s['ge1_pass_delta_below_C2']]
 info['ge1_positive_below_C2_sectors']=sum(r['intersects_kappa_ge1'] and r['lambda_r_category']=='POSITIVE_BELOW_C2'for r in rr)
 info['largest_MGS_frame_float_orthogonality']=max(s['MP_frame_float_orthogonality']for s in ss);summary[world]=info
summary['cells']=len(summaries);summary['sectors']=len(allrows);summary['status']='DIAGNOSTIC_NEVER_A_PROOF';(P/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
