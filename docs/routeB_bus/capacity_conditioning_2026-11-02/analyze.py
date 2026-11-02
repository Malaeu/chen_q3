"""Combine capacity-conditioning sectors and local gaps; numerical diagnostic."""
from pathlib import Path
import sys,csv,json,hashlib
import mpmath as mp
import numpy as np
from scipy.stats import rankdata
P=Path(__file__).resolve().parent;BASE=P.parent
sys.path.insert(0,str(BASE/'capacity_matrix_2026-11-02'))
from capacity import Erow
mp.mp.dps=160
MS=list(range(16,41))+[60,80]
zeros=[mp.mpf(r['gamma']) for r in csv.DictReader((BASE/'capacity_matrix_2026-11-02/zeros.csv').open())]
def fmt(x):return mp.nstr(x,100)
def save(name,rows):
 with (P/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
def main():
 cases=[];gaps=[];grid=[];files=[]
 for m in MS:
  path=P/f'cell_m{m}_dps{100 if m<=40 else 120}_gl128.json';data=json.loads(path.read_text());L=mp.log(m);omega=2*mp.pi/L;Omega=m*omega
  files.append(dict(path=path.name,sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
  for r in data['all_sectors']:
   for k in r['kappas']:grid.append(dict(m=m,kappa=k,q=r['q'],r=r['r'],saturates=r['saturates'],count_minus_r=r['count_minus_r'],delta=r['delta'],lambda_r_over_delta=r['lambda_r_over_delta']))
  for r in data['passing_sectors']:
   q=r['q'];E=mp.matrix([Erow(g,m) for g in zeros[:q]]);norms=[mp.norm(E[k,:]) for k in range(q)];weak=list(map(mp.mpf,r['weak_left_vector']));mass=[x*x for x in weak];order=sorted(range(q),key=lambda j:mass[j],reverse=True);a,b=order[:2];pair=max(range(q-1),key=lambda j:mass[j]+mass[j+1]);adjcorr=abs(mp.fdot(E[pair,:],E[pair+1,:])/(norms[pair]*norms[pair+1]));topcorr=abs(mp.fdot(E[a,:],E[b,:])/(norms[a]*norms[b]));local=[]
   for j in range(q):
    options=([j-1] if j else [])+[j+1];neighbor=min(options,key=lambda k:abs(zeros[j]-zeros[k]));g=abs(zeros[j]-zeros[neighbor]);ng=g/omega
    gr=dict(m=m,q=q,k=j+1,gamma=fmt(zeros[j]),nearest_zero_index=neighbor+1,neighbor_is_included=neighbor<q,gap=fmt(g),normalized_gap=fmt(ng),flag_below_0p3=ng<mp.mpf('.3'),weak_left_component=fmt(weak[j]),weak_left_weight=fmt(mass[j]),raw_row_norm=fmt(norms[j]));gaps.append(gr);local.append(gr)
   minimum=min(local,key=lambda x:mp.mpf(x['normalized_gap']));ss=mp.mpf(r['sigma_min_squared']);lr=mp.mpf(r['lambda_r']);all_s=list(map(mp.mpf,r['raw_singular_values']));peak=order[0];nearest_mode=int(mp.nint(zeros[peak]/omega));left=max(mp.mpf(1),zeros[q-1]/Omega);right=min(mp.mpf('1.4'),zeros[q]/Omega)
   cases.append(dict(m=m,q=q,r=r['r'],kappa_grid=','.join(r['kappas']),kappa_left=fmt(left),kappa_right=fmt(right),left_included=left==1 and zeros[q-1]<Omega,sigma_min=fmt(mp.sqrt(ss)),sigma_min_squared=fmt(ss),twice_sigma_min_squared=fmt(2*ss),lambda_r=fmt(lr),twice_sigma_min_squared_over_lambda_r=fmt(2*ss/lr),delta=r['delta'],lambda_r_over_delta=r['lambda_r_over_delta'],minimum_normalized_gap=minimum['normalized_gap'],minimum_gap_zero_index=minimum['k'],minimum_gap_neighbor_index=minimum['nearest_zero_index'],minimum_gap_neighbor_included=minimum['neighbor_is_included'],any_gap_below_0p3=any(x['flag_below_0p3'] for x in local),top_two_indices=f'{a+1},{b+1}',top_two_weights=f'{fmt(mass[a])},{fmt(mass[b])}',top_two_total_mass=fmt(mass[a]+mass[b]),top_two_absolute_row_correlation=fmt(topcorr),adjacent_pair_indices=f'{pair+1},{pair+2}',adjacent_pair_weights=f'{fmt(mass[pair])},{fmt(mass[pair+1])}',adjacent_pair_mass=fmt(mass[pair]+mass[pair+1]),adjacent_pair_normalized_gap=fmt((zeros[pair+1]-zeros[pair])/omega),adjacent_pair_absolute_row_correlation=fmt(adjcorr),weak_peak_zero_index=peak+1,weak_peak_gamma=fmt(zeros[peak]),weak_peak_weight=fmt(mass[peak]),weak_peak_row_norm=fmt(norms[peak]),weak_peak_nearest_mode=nearest_mode,weak_peak_nearest_mode_is_exterior=nearest_mode>m,weak_peak_distance_in_mode_units=fmt(abs(zeros[peak]/omega-nearest_mode)),weak_peak_sinc_factor_absolute=fmt(abs(mp.sin(zeros[peak]*L/2))),relative_singular_squared_gap=fmt((all_s[-2]**2-ss)/ss),weak_vector_norm_error=fmt(abs(mp.fsum(mass)-1))))
 save('all_cases.csv',cases);save('all_local_gaps.csv',gaps);save('all_grid.csv',grid)
 cor=[]
 for name,subset in [('m16_to40',[x for x in cases if x['m']<=40]),('all_including60_80',cases)]:
  x=np.array([float(r['minimum_normalized_gap']) for r in subset]);y=np.array([float(r['sigma_min']) for r in subset]);ly=np.log10(y)
  cor.append(dict(sample=name,unique_m_q_sectors=len(subset),distinct_m=len(set(r['m'] for r in subset)),pearson_sigma_vs_min_gap=float(np.corrcoef(x,y)[0,1]),pearson_log10_sigma_vs_min_gap=float(np.corrcoef(x,ly)[0,1]),spearman_sigma_vs_min_gap=float(np.corrcoef(rankdata(x),rankdata(y))[0,1]),minimum_normalized_gap=min(x),flagged_sectors=sum(r['any_gap_below_0p3'] for r in subset),note='One row per(m,q), not perduplicated κ. Observational, correlated sectors; no significance test or causal conclusion.'))
 save('correlations.csv',cor)
 (P/'analysis_metadata.json').write_text(json.dumps(dict(context_commit='e724ae65ed39a8ba8b8f07c928d790ea9820342a',m_values=MS,unique_passing_sectors=len(cases),source_files=files,local_gap_convention='nearest positive zero, includes neighbor outside cutoff; first positive zero usesnext; strict normalized gap<0.3',zero_table_sha256=hashlib.sha256((BASE/'capacity_matrix_2026-11-02/zeros.csv').read_bytes()).hexdigest()),indent=2)+'\n')
 print(json.dumps(cor,indent=2))
if __name__=='__main__':main()
