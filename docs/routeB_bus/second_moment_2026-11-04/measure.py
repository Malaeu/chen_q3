"""Requested raw second moments, exact census weights and interpretation gates."""
import os,math,csv,json,statistics,collections
from pathlib import Path
import numpy as np
P=Path(__file__).resolve().parent
BASE=Path(os.environ.get('SECOND_BASE','/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03'))
Z=[float(x['gamma']) for x in csv.DictReader((BASE/'source_inputs/zeta_zeros.csv').open())];D=json.loads((BASE/'source_inputs/dh_zeros_900_200dps.json').read_text());GAMMA_STAR=Z[0]
def events(w):
 if w=='dh':return sorted([(float(x['gamma']),1,1)for x in D['critical_line_zeros']]+[(float(x['gamma']),2,0)for x in D['off_line_pairs']])
 ev=[(x,1,1)for x in Z]
 if w=='plant':ev.append((2*math.pi/math.log(2),2,0))
 return sorted(ev)
def counts(w,T):
 ev=[e for e in events(w)if e[0]<T];N=sum(x[1]for x in ev);line=sum(x[2]for x in ev);distinct=N
 return N,line,distinct,len(ev)
def write(n,rs):
 keys=list(dict.fromkeys(k for r in rs for k in r))
 with(P/n).open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rs)
def main():
 data=list(csv.DictReader((P/'SOURCE_MOMENTS.csv').open()));assert len(data)==855,len(data);out=[]
 for d in data:
  m=int(d['m']);w=d['world'];L=math.log(m);F=float(d['Frob2']);tr=float(d['trace'])
  for cutoff,kappa in [('primary',1+(1+math.log(L))/(4*L)),('kappa1',1.)]:
   T=kappa*2*math.pi*m/L;N,line,nd,heights=counts(w,T);lam=L/(L-math.log(L)+math.log(kappa))
   for convention,sigma in [('L_plus_inv_gamma',L+1/GAMMA_STAR),('2L',2*L),('L',L)]:
    v=F/(sigma*sigma*N);raw1=2-v;rawd=(3-v)/2;finite_phi=(4*tr/sigma-F/(sigma*sigma))/N;finite1=finite_phi-2;finited=(finite_phi-1)/2;tol=1e-10*max(1,abs(raw1),abs(rawd));viol1=raw1>line/N+tol;viold=rawd>nd/N+tol
    out.append(dict(world=w,m=m,cutoff=cutoff,kappa=kappa,T=T,L=L,sigma_convention=convention,sigma=sigma,gamma_star_diagnostic=GAMMA_STAR,N_upper_with_multiplicity=N,N_on_line_simple=line,N_distinct_complex=nd,N_distinct_heights=heights,census_simple_on_line_fraction=line/N,census_distinct_fraction=nd/N,trace=tr,Frob2=F,v=v,raw_simple_lower=raw1,raw_distinct_lower=rawd,raw_simple_violation=viol1,raw_distinct_violation=viold,raw_sanity_pass=not(viol1 or viold),sanity_tolerance=tol,trace_ratio=tr/(sigma*N),finite_unpaid_simple_score=finite1,finite_unpaid_distinct_score=finited,finite_unpaid_simple_violation=finite1>line/N+tol,finite_unpaid_distinct_violation=finited>nd/N+tol,lambda_eff=lam,Gabor_reference_only=1/lam+lam/3,paid_tail_scope='COFINAL_PRIMARY_ONLY_NOT_A_FINITE_ENCLOSURE'if cutoff=='primary'else'OUTSIDE_POSITIVE_C_TAIL_THEOREM'))
 assert len(out)==5130
 # Userkill switch: raw-score interpretation stops for anyviolating convention.
 flags={s:any(not r['raw_sanity_pass']for r in out if r['sigma_convention']==s)for s in ['L_plus_inv_gamma','2L','L']}
 for r in out:r['convention_interpretation_stopped']=flags[r['sigma_convention']]
 write('SUMMARY.csv',out);write('SANITY_VIOLATIONS.csv',[r for r in out if not r['raw_sanity_pass']]);stops=[];blocks=[];fits=[]
 for w in ['zeta','dh','plant']:
  for cutoff in ['primary','kappa1']:
   for s in flags:
    rr=[r for r in out if r['world']==w and r['cutoff']==cutoff and r['sigma_convention']==s];bad=[r for r in rr if not r['raw_sanity_pass']];stops.append(dict(world=w,cutoff=cutoff,sigma_convention=s,cells=len(rr),violations=len(bad),first_violation_m=min((r['m']for r in bad),default=None),interpretation_stopped=flags[s],v_min=min(r['v']for r in rr),v_max=max(r['v']for r in rr),finite_unpaid_violations=sum(r['finite_unpaid_simple_violation']or r['finite_unpaid_distinct_violation']for r in rr)))
    for start in [100,150,200,250,300]:
     rs=[r for r in rr if start<=r['m']<=min(start+49,300)];blocks.append(dict(world=w,cutoff=cutoff,sigma_convention=s,m_start=start,m_end=min(start+49,300),n=len(rs),median_v=statistics.median(r['v']for r in rs),min_v=min(r['v']for r in rs),max_v=max(r['v']for r in rs),median_trace_ratio=statistics.median(r['trace_ratio']for r in rs)))
    rs=[r for r in rr if r['m']>=80];y=np.array([r['v']for r in rs]);X=np.c_[np.ones(len(rs)),1/np.log([r['m']for r in rs])];coef=np.linalg.lstsq(X,y,rcond=None)[0];res=y-X@coef;fits.append(dict(world=w,cutoff=cutoff,sigma_convention=s,model='v=a+b/log(m), descriptive within80..300 only',a=coef[0],b=coef[1],RMSE=float(np.sqrt(np.mean(res**2))),R_squared=float(1-np.sum(res**2)/np.sum((y-np.mean(y))**2)),extrapolation_claim=False))
 write('SANITY_SUMMARY.csv',stops);write('BLOCK_MEDIANS.csv',blocks);write('FINITE_FITS.csv',fits)
 r=[r for r in out if r['world']=='zeta'and r['cutoff']=='primary'and r['sigma_convention']=='L_plus_inv_gamma'];v1=[x for x in r if x['m']>=80];v2=statistics.median(x['v']for x in r if x['m']>=200)
 dec=list(csv.DictReader((P/'DECOMPOSITION.csv').open()));v3=next(float(x['value'])for x in dec if x['world']=='zeta'and x['m']=='300'and x['component']=='B_offdiagonal')/next(x['Frob2']for x in r if x['m']==300)
 score=dict(V1_pass=all(1<=x['v']<=1.6 for x in v1),V1_range=[min(x['v']for x in v1),max(x['v']for x in v1)],V2_pass=v2<4/3,V2_median_200_300=v2,V3_pass=abs(v3)>=.2,V3_signed_share_m300=v3,V4_pass=all(x['raw_sanity_pass']for x in out),stopped_conventions=flags,scope='raw measured diagnostics; interpretation stops retained')
 (P/'SCORES.json').write_text(json.dumps(score,indent=2)+'\n');print(json.dumps(score,indent=2))
if __name__=='__main__':main()
