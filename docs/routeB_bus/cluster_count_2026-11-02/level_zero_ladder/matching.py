"""Explicit ordinal and Fourier-root matchings. DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
import csv,json,math
import mpmath as mp
import numpy as np
from scipy.optimize import linear_sum_assignment
P=Path(__file__).resolve().parent
BUS=P.parents[1]
mp.mp.dps=140
def write(name,rows):
 with (P/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def fmt(x):return mp.nstr(x,100)
def main():
 z=[mp.mpf(r['gamma']) for r in csv.DictReader((BUS/'lowcluster_2026-11-02/ladder_limit/identify/zero_height_local/zeros.csv').open())]
 rootrows=list(csv.DictReader((P/'roots.csv').open()))
 matches=[];costrows=[];summary=[];curves={}
 for m in (16,24,32,40):
  dps=160 if m==32 else 180
  cell=json.loads(next(P.glob(f'cell_m{m}_dps{dps}_gl*.json')).read_text())
  ev=list(map(mp.mpf,cell['lambda_']));omega=2*mp.pi*m/mp.log(m)
  roots={i:[r for r in rootrows if int(r['m'])==m and int(r['i'])==i] for i in range(m+1)}
  for B in (2,4,8):
   ids=[i for i,e in enumerate(ev) if e>=mp.mpf(m)**(-B)];q=len(ids)
   gaps=[z[1]-z[0] if j==0 else min(z[j]-z[j-1],z[j+1]-z[j]) for j in range(q)]
   near={};cost=np.zeros((q,q))
   for a,i in enumerate(ids):
    for j in range(q):
     rr=min(roots[i],key=lambda r:abs(mp.mpf(r['t_root'])-z[j]))
     t=mp.mpf(rr['t_root']);near[a,j]=rr;cost[a,j]=float(abs(t-z[j])/gaps[j])
     costrows.append(dict(m=m,B=B,i=i,j=j+1,gamma=fmt(z[j]),nearest_root=fmt(t),root_kind=rr['kind'],distance=fmt(abs(t-z[j])),distance_over_local_spacing=cost[a,j]))
   aa,jj=linear_sum_assignment(cost)
   assignments={'ordinal':list(zip(range(q),range(q))),
     'root_bijective':list(zip(aa.tolist(),jj.tolist())),
     'root_independent':[(int(np.argmin(cost[:,j])),j) for j in range(q)]}
   for method,pairs in assignments.items():
    group=[]
    for a,j in pairs:
     i=ids[a];rr=near[a,j];t=mp.mpf(rr['t_root'])
     row=dict(m=m,B=B,method=method,i=i,lifted_rank=a+1,j=j+1,lambda_i=fmt(ev[i]),log_lambda=fmt(mp.log(ev[i])),gamma=fmt(z[j]),modal_cutoff=fmt(omega),x=fmt(z[j]/omega),nearest_real_fourier_zero=fmt(t),signed_zero_offset=fmt(t-z[j]),absolute_zero_distance=fmt(abs(t-z[j])),distance_over_local_spacing=cost[a,j],root_kind=rr['kind'])
     group.append(row);matches.append(row)
    summary.append(dict(m=m,B=B,method=method,cluster_count=m+1-q,lifted_count=q,distinct_levels_used=len(set(a for a,j in pairs)),ordinal_agreements=sum(a==j for a,j in pairs),median_distance=float(np.median([float(r['absolute_zero_distance']) for r in group])),maximum_distance=max(float(r['absolute_zero_distance']) for r in group),median_spacing_distance=float(np.median([r['distance_over_local_spacing'] for r in group])),maximum_spacing_distance=max(r['distance_over_local_spacing'] for r in group),structural_matches=sum(r['root_kind']=='structural_exterior' for r in group)))
   curves[m,B]=(np.array([float(z[j]/omega) for j in range(q)]),np.array([float(mp.log(ev[i])) for i in ids]))
 write('matches.csv',matches);write('matching_costs.csv',costrows);write('matching_summary.csv',summary)
 collapse=[];models=[]
 for B in (2,4,8):
  data=[curves[m,B] for m in (16,24,32,40)]
  lo=max(x[0] for x,y in data);hi=min(x[-1] for x,y in data);grid=np.linspace(lo,hi,401)
  ys=np.array([np.interp(grid,x,y) for x,y in data]);spread=np.ptp(ys,axis=0)
  upper=spread[(grid>=.6)&(grid<=1)]
  collapse.append(dict(B=B,x_common_min=lo,x_common_max=hi,grid_points=len(grid),median_log_spread=float(np.median(spread)),max_log_spread=float(max(spread)),median_lambda_factor=float(np.exp(np.median(spread))),max_lambda_factor=float(np.exp(max(spread))),rms_deviation_from_mean_log_curve=float(np.sqrt(np.mean((ys-ys.mean(axis=0))**2))),bulk_x_min=.6,bulk_x_max=1,bulk_median_lambda_factor=float(np.exp(np.median(upper))),bulk_max_lambda_factor=float(np.exp(max(upper)))))
  for degree in (2,):
   for with_m in (False,True):
    def features(x,m):return np.array([[1,t,t*t]+([math.log(m)] if with_m else []) for t in x])
    rmses=[]
    for held in (16,24,32,40):
     xx=[];yy=[]
     for m in (16,24,32,40):
      if m==held:continue
      x,y=curves[m,B];xx.extend(features(x,m));yy.extend(y)
     coef=np.linalg.lstsq(np.array(xx),np.array(yy),rcond=None)[0]
     x,y=curves[held,B];err=features(x,held)@coef-y;rmses.append(float(np.sqrt(np.mean(err*err))))
    xx=np.concatenate([features(curves[m,B][0],m) for m in (16,24,32,40)]);yy=np.concatenate([curves[m,B][1] for m in (16,24,32,40)])
    coef=np.linalg.lstsq(xx,yy,rcond=None)[0]
    models.append(dict(B=B,model='log lambda=a+b*x+c*x^2'+('+d*log(m)' if with_m else ''),coefficients=coef.tolist(),leave_one_m_out_log_RMSE=dict(zip(('16','24','32','40'),rmses)),mean_heldout_log_RMSE=float(np.mean(rmses))))
 write('collapse.csv',collapse);(P/'simple_models.json').write_text(json.dumps(models,indent=2)+'\n')
 print(json.dumps(collapse,indent=2))
if __name__=='__main__':main()
