"""Lossless scalar tables and finite diagnostics; no quantifier or proof."""
from core import *
import numpy as np
from collections import Counter,defaultdict
from scipy.stats import spearmanr

def csvout(name,rows):
 if not rows:return
 keys=list(dict.fromkeys(k for row in rows for k in row))
 with (P/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)

def main():
 mp.mp.dps=80;cells=[json.loads(p.read_text()) for p in sorted((P/'cells').glob('*_m*.json'))];rows=sum([c['rows'] for c in cells],[]);base=[r for r in rows if r['variant']=='base'];edge=[r for r in rows if r['edge_zero']];adapt=[dict(world=c['world'],m=c['m'],**a) for c in cells for a in c['adaptive_thresholds']]
 csvout('conditioning.csv',base);csvout('EDGE_ZERO_sensitivity.csv',edge);csvout('adaptive_kappa_sectors.csv',adapt)
 gp=[]
 for r in base:
  ev=[e for e in events(r['world']) if mp.mpf(e['gamma'])<mp.mpf(r['T'])];L=mp.mpf(r['L'])
  for i,e in enumerate(ev):
   g=mp.mpf(e['gamma']);gaps=[]
   if i:gaps.append(g-mp.mpf(ev[i-1]['gamma']))
   if i+1<len(ev):gaps.append(mp.mpf(ev[i+1]['gamma'])-g)
   gap=min(gaps) if gaps else None;normalized=gap*L/(2*mp.pi) if gap is not None else None
   coordinate=g*L/(2*mp.pi);nearest=int(mp.nint(coordinate))
   gp.append(dict(window_mode_coordinate=mp.nstr(coordinate,40),nearest_lattice_index=nearest,distance_to_nearest_mode=mp.nstr(abs(coordinate-nearest),40),nearest_mode_is_external=nearest>r['m'],world=r['world'],m=r['m'],cut=r['cut'],T=r['T'],gamma=e['gamma'],kind=e['kind'],raw_condition_count=1 if e['kind']=='line' else 2,multiplicity=e['multiplicity'],nearest_included_gap=mp.nstr(gap,40) if gap is not None else None,normalized_included_gap=mp.nstr(normalized,40) if normalized is not None else None,Lehmer_flag_under_requested_threshold=normalized<mp.mpf('.3') if normalized is not None else None))
 csvout('all_included_zero_gaps.csv',gp)
 pair=[]
 for r in rows:
  m=r['m'];cut=r['cut']
  if (cut=='c_half' and 53<=m<=57) or (cut=='c_quarter' and 63<=m<=67) or(cut=='kappa_one' and 75<=m<=80):
   pair.append(r)
 csvout('pair_111_entry.csv',pair)
 samegap=[]
 for c in cells:
  bs=[r for r in c['rows'] if r['variant']=='base']
  for i,a in enumerate(bs):
   for b in bs[i+1:]:
    if a.get('sigma_min') and b.get('sigma_min') and a['min_gap_left']==b['min_gap_left'] and a['min_gap_right']==b['min_gap_right']:
     sa,sb=mp.mpf(a['sigma_min']),mp.mpf(b['sigma_min']);factor=max(sa,sb)/min(sa,sb)
     samegap.append(dict(world=c['world'],m=c['m'],cut_a=a['cut'],cut_b=b['cut'],same_gap_left=a['min_gap_left'],same_gap_right=a['min_gap_right'],same_min_gap=a['min_included_normalized_gap'],sigma_a=a['sigma_min'],sigma_b=b['sigma_min'],sigma_factor=mp.nstr(factor,30),q_a=a['q'],q_b=b['q']))
 csvout('same_gap_different_conditioning.csv',samegap)
 paired=[];lookup={(c['world'],c['m']):c for c in cells}
 for m in range(16,121):
  if ('zeta',m) not in lookup or ('plant',m) not in lookup:continue
  z={(r['cut'],r['variant']):r for r in lookup['zeta',m]['rows']};w={(r['cut'],r['variant']):r for r in lookup['plant',m]['rows']}
  for key,a in z.items():
   if key not in w:continue
   b=w[key];paired.append(dict(m=m,cut=key[0],variant=key[1],zeta_q=a['q'],plant_q=b['q'],zeta_r=a['r'],plant_r=b['r'],zeta_N_A2=a['N_A2'],plant_N_A2=b['N_A2'],zeta_defect=a['count_minus_r'],plant_defect=b['count_minus_r'],defect_increment=b['count_minus_r']-a['count_minus_r'],N_increment=b['N_A2']-a['N_A2'],r_increment=b['r']-a['r'],zeta_delta=a['delta'],plant_delta=b['delta'],count_unresolved=a['N_A2_unresolved']+b['N_A2_unresolved']))
 csvout('paired_planted_index.csv',paired)
 summary=[]
 for world in ['zeta','dh','plant']:
  for cut,c in [('c_quarter','.25'),('c_half','.5'),('kappa_one','0')]:
   rr=[r for r in base if r['world']==world and r['cut']==cut];resolved=[r for r in rr if r.get('sigma_min')];lr=[r for r in rr if r.get('lambda_r_preferred') is not None]
   cors=[r for r in resolved if r.get('min_included_normalized_gap') is not None];corr=spearmanr([float(r['min_included_normalized_gap']) for r in cors],[float(mp.log10(mp.mpf(r['sigma_min']))) for r in cors]).statistic if len(cors)>2 else None
   summary.append(dict(world=world,cut=cut,cells=len(rr),expected_cells=105,missing_m=[m for m in range(16,121) if m not in {r['m'] for r in rr}],J_zero=sum(r['r']==0 for r in rr),sigma_resolved=len(resolved),sigma_status_counts=dict(Counter(r.get('sigma_status') for r in rr)),lambda_r_status_counts=dict(Counter(r['lambda_r_status'] for r in rr)),delta_lt2=sum(r['delta_less_than_2'] for r in rr),negative_defect_m=[r['m'] for r in rr if r['count_minus_r']<0],Schur_status_counts=dict(Counter(r['Schur_status'] for r in rr)),min_sigma=min((float(r['sigma_min']) for r in resolved),default=None),max_sigma=max((float(r['sigma_min']) for r in resolved),default=None),min_normalized_gap=min((float(r['min_included_normalized_gap']) for r in rr if r['min_included_normalized_gap'] is not None),default=None),descriptive_spearman_log_sigma_gap=corr))
 overall=dict(status='DIAGNOSTIC_NEVER_A_PROOF',cells=len(cells),expected_cells=315,base_rows=len(base),all_rows=len(rows),EDGE_ZERO_base_rows=sum(r['edge_zero'] for r in base),EDGE_ZERO_sensitivity_rows=sum(r['variant']!='base' for r in edge),EDGE_ZERO_table_rows=len(edge),Schur_identity_status_counts=dict(Counter(r['Schur_status'] for r in rows)),max_E_kernel_residual=max((r['E_kernel_residual'] for r in rows),default=0),max_frame_orthogonality=max((r['Q_orthogonality'] for r in rows),default=0),summary=summary,max_same_gap_sigma_factor=max((float(r['sigma_factor']) for r in samegap),default=0),within_source_asymptotic_regime=False,precision_note='Float radius is diagnostic, not an interval enclosure; MP σ rows retain method/residual/dps. Tiny uncached lambda_r explicitly unresolved.')
 overall['paired_planted_rows']=len(paired);overall['paired_planted_difference_counts']=dict(Counter(str((r['defect_increment'],r['N_increment'],r['r_increment'])) for r in paired));overall['paired_planted_unresolved_rows']=sum(r['count_unresolved']>0 for r in paired)
 (P/'summary.json').write_text(json.dumps(overall,indent=2)+'\n');print(json.dumps(overall,indent=2))
if __name__=='__main__':main()
