"""Descriptive, fixed-grid fits. Censored numerical gaps are not exact zeros."""
from pathlib import Path
import csv,json,collections,hashlib
import numpy as np
from scipy.stats import linregress,theilslopes
P=Path(__file__).resolve().parent
def write(path,rows):
 keys=list(dict.fromkeys(k for r in rows for k in r))
 with path.open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
controls={(r['world'],int(r['m'])):r for r in csv.DictReader((P/'max_delta/MAX_DELTA.csv').open())};rows=[];ledger=[];metadata=[]
for m in range(310,601,10):
 for world in ['zeta','plant','dh']:
  j=json.loads((P/'scan_cells'/f'{world}_m{m}.json').read_text());r=dict(j['summary']);r.pop('n_minus_lower');r.pop('n_minus_upper');r.pop('source_zero_guard')
  for kind in ['evaluated','bounded']:
   ledger.extend(dict(world=world,m=m,kind=kind,**s)for s in j[kind])
  if world=='zeta':first=min(j['evaluated']+j['bounded'],key=lambda s:s['q']);assert 'delta'in first;r['max_delta_kappa_ge1']=first['delta'];r['max_delta_q']=first['q'];r['lambda_at_kappa1']=first['lambda_r']
  else:a=controls[(world,m)];r['max_delta_kappa_ge1']=float(a['delta']);r['max_delta_q']=int(a['q']);r['lambda_at_kappa1']=float(a['lambda_r'])
  r['best_gap_sign_resolved']=r['separator_kappa_ge1']=='YES_NUMERIC';r['best_level_status']='UNRESOLVED_AT_ZERO'if abs(r['best_lambda_r'])<=r['numeric_guard']else'RESOLVED';r['gap_for_descriptive_medians']=r['best_gap']if r['best_gap_sign_resolved']else 0.0
  bulk=[s for s in j['evaluated']if s['lambda_r']>.01 and s['delta']>r['numeric_guard']];r['best_resolved_bulk_gap_lambda_gt_001']=max((s['gap']for s in bulk),default=None);r['trace']=float(np.trace(np.load(P/'matrices'/f'{world}_m{m}.npz')['A']));r['conditional_trace_floor_at_best']= -r['trace']/(m+1-2*r['best_r'])if 0<r['best_r']<(m+1)/2 else None;rows.append(r)
write(P/'SUMMARY.csv',rows);write(P/'all_sector_receipts.csv',ledger)
bins=[];fits=[]
for world in ['zeta','plant','dh']:
 ss=[r for r in rows if r['world']==world]
 for start in range(310,601,50):
  group=[r for r in ss if start<=r['m']<start+50];x=np.mean(np.log([r['m']for r in group]));bins.append(dict(world=world,m_start=start,m_end=start+40,n=len(group),log_m_geomean=float(x),m_geomean=float(np.exp(x)),max_delta=max(r['max_delta_kappa_ge1']for r in group),median_delta=float(np.median([r['max_delta_kappa_ge1']for r in group])),median_best_gap=float(np.median([r['gap_for_descriptive_medians']for r in group])),median_gap_lower=float(np.median([r['max_gap_lower_bound']for r in group])),median_gap_upper=float(np.median([r['max_gap_upper_bound']for r in group])),resolved_passes=sum(r['best_gap_sign_resolved']for r in group)))
def fit(world,response,x,y,scope):
 x=np.array(x);y=np.array(y);a=linregress(x,y);ts=theilslopes(y,x);loo=[linregress(np.delete(x,i),np.delete(y,i)).slope for i in range(len(x))]
 fits.append(dict(world=world,response=response,scope=scope,n=len(x),model='response=intercept+slope*log(m)',intercept=float(a.intercept),slope=float(a.slope),R_squared=float(a.rvalue*a.rvalue),Theil_Sen_slope=float(ts.slope),leave_one_out_slope_min=float(min(loo)),leave_one_out_slope_max=float(max(loo)),status='DESCRIPTIVE_DETERMINISTIC_GRID_NO_ASYMPTOTIC_OR_PROBABILITY_CLAIM'))
for world in ['zeta','plant','dh']:
 ss=[r for r in rows if r['world']==world];bb=[r for r in bins if r['world']==world]
 fit(world,'delta_max_over_kappa',[np.log(r['m'])for r in ss],[r['max_delta_kappa_ge1']for r in ss],'30 individual m values')
 fit(world,'five_sample_block_max_delta',[r['log_m_geomean']for r in bb],[r['max_delta']for r in bb],'six nonoverlapping five-m blocks')
 if world=='zeta':fit(world,'five_sample_block_median_best_gap',[r['log_m_geomean']for r in bb],[r['median_best_gap']for r in bb],'six nonoverlapping five-m blocks; unresolved gaps plotted at0 with brackets retained')
write(P/'BINS.csv',bins);write(P/'FITS.csv',fits)
status={w:dict(collections.Counter(r['separator_kappa_ge1']for r in rows if r['world']==w))for w in ['zeta','plant','dh']};z=[r for r in rows if r['world']=='zeta'];summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',cells=len(rows),m_grid=list(range(310,601,10)),sectors=len(ledger),evaluated=sum(r['evaluated_sectors']for r in rows),bounded=sum(r['bounded_sectors']for r in rows),separator_statuses=status,zeta_unresolved_m=[r['m']for r in z if r['separator_kappa_ge1']=='UNRESOLVED'],all_max_gap_brackets_within4guards=all(r['best_gap_resolved']for r in rows),max_numeric_guard=max(r['numeric_guard']for r in rows),binning='six fixed five-sample blocks310..350,...,560..600; medians of the best-per-m gaps, NOT median over kappa sectors',unresolved_gap_rule='Use0 only for plotting/descriptive medians; CSV retains lower/upper bracket and UNRESOLVED label. No exact zero/nonexistence inferred.',fits=fits)
replay=P/'precision_replay/scan_cells/zeta_m600.json'
if replay.exists():
 new=json.loads(replay.read_text());old=json.loads((P/'scan_cells/zeta_m600.json').read_text());summary['zeta600_768_1024_check']=dict(status_same=new['summary']['separator_kappa_ge1']==old['summary']['separator_kappa_ge1'],best_gap_difference=new['summary']['best_gap']-old['summary']['best_gap'],max_evaluated_delta_difference=max(abs(a['delta']-b['delta'])for a,b in zip(new['evaluated'],old['evaluated'])),scope='frame arithmetic only; does not resolve source/eigenvalue floor')
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
fig,ax=plt.subplots(1,2,figsize=(11,4),layout='constrained');colors={'zeta':'#168b89','plant':'#df755d','dh':'#777777'}
for world in colors:
 ss=[r for r in rows if r['world']==world];ax[0].plot([np.log(r['m'])for r in ss],[r['max_delta_kappa_ge1']for r in ss],'.-',label=world,color=colors[world],lw=.8,alpha=.8)
ax[0].set(xlabel='log m',ylabel='max over kappa>=1 ||A Q|| = delta(kappa=1)');ax[0].legend()
ok=[r for r in z if r['best_gap_sign_resolved']];no=[r for r in z if not r['best_gap_sign_resolved']];ax[1].scatter([np.log(r['m'])for r in ok],[r['best_gap']for r in ok],color=colors['zeta'],s=22,label='resolved zeta gap');ax[1].scatter([np.log(r['m'])for r in no],[0 for r in no],marker='v',color='#777777',s=22,label='unresolved at numeric floor')
bb=[r for r in bins if r['world']=='zeta'];ax[1].plot([r['log_m_geomean']for r in bb],[r['median_best_gap']for r in bb],'o-',color=colors['plant'],label='five-sample medians');ff=next(r for r in fits if r['response']=='five_sample_block_median_best_gap');x=np.array([np.log(310),np.log(600)]);ax[1].plot(x,ff['intercept']+ff['slope']*x,'--',color='#444444',lw=1,label='descriptive affine fit');ax[1].axhline(0,color='#aaa',lw=.7);ax[1].set(xlabel='log m',ylabel='max over kappa of (lambda_r - delta)');ax[1].legend(fontsize=8)
fig.suptitle('Literal even CCM: diagnostic grid, not an asymptotic law');fig.savefig(P/'TREND.png',dpi=180);fig.savefig(P/'TREND.svg');plt.close(fig)
