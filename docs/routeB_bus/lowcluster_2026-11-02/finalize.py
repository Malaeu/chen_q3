"""Combine independently computed F and exterior X; no closure reconstruction of X."""
import json,csv,hashlib
from pathlib import Path
import mpmath as mp
mp.mp.dps=160
P=Path(__file__).resolve().parent

def fmt(x):return mp.nstr(x,90)
def load_cell(m,dps=100,order=128):
 r=json.loads((P/f'core_m{m}_dps{dps}_gl{order}.json').read_text());x=json.loads((P/f'exterior_m{m}_dps{dps}_gl{order}.json').read_text())
 V=mp.matrix(r['V']);A=mp.matrix(r['A']);lam=list(map(mp.mpf,r['lambda_']));a=list(map(mp.mpf,r['a']));Z=mp.mpf(r['Z']);F=list(map(mp.mpf,r['F']));X=list(V.T*mp.matrix(x['X']))
 # No numerical zero cutoff: all computed nonzero levels are retained.
 # Exact nonzeroness is not claimed by this floating diagnostic.
 zero=[i for i in range(1,m+1) if lam[i]==0];z=mp.fsum(a[i]**2 for i in zero)
 levels=[];terms=[]
 for i in range(m+1):
  T=-Z*lam[i]*a[i];closure=F[i]+X[i]-T
  term=(F[i]+X[i])**2/(Z*lam[i])**2 if lam[i]!=0 else None
  terms.append(term)
  ratio=abs(X[i]/F[i]) if F[i]!=0 else (mp.inf if X[i]!=0 else None)
  levels.append(dict(m=m,i=i,lambda_i=fmt(lam[i]),a_i=fmt(a[i]),F_i=fmt(F[i]),X_i_independent=fmt(X[i]),T_expected=fmt(T),closure_residual=fmt(closure),closure_relative=fmt(abs(closure/T)) if T else None,full_inverse_weighted_term=fmt(term) if term is not None else None,X_over_F=fmt(ratio) if ratio is not None else None))
 S=mp.fsum(terms[i] for i in range(1,m+1) if i not in zero)+z
 Sf=mp.fsum(F[i]**2/(Z*lam[i])**2 for i in range(1,m+1) if i not in zero)+z
 target=1-a[0]**2
 ratios=[(abs(X[i]/F[i]),i) for i in range(1,m+1) if F[i]!=0];ratio,idx=max(ratios)
 Fstab=max(abs(mp.mpf(r['F_partials'][-1][i])-mp.mpf(r['F_partials'][-2][i])) for i in range(m+1))
 summ=dict(m=m,dps=dps,order=order,Z=fmt(Z),lambda0=fmt(lam[0]),one_minus_a0_squared=fmt(target),S_independent=fmt(S),S_difference=fmt(S-target),S_F_only=fmt(Sf),z_numeric=fmt(z),zero_levels=zero,max_X_over_F=fmt(ratio),max_ratio_level=idx,max_closure_relative=fmt(max(mp.mpf(v['closure_relative']) for v in levels if v['closure_relative'] is not None)),max_closure_absolute=fmt(max(abs(F[i]+X[i]+Z*lam[i]*a[i]) for i in range(m+1))),F_stability_160_to_192_max_absolute=fmt(Fstab),entry_ctrl=r['entry_ctrl'],eigen_residual=r['eigen_residual'],min_abs_eigenvalue=fmt(min(abs(l) for l in lam)),ladder_rank=r['ladder']['ladder_rank'])
 bands=[]
 for B in (2,4,8):
  threshold=mp.mpf(m)**(-B)
  for band in ('low','high'):
   inds=[i for i in range(1,m+1) if i not in zero and ((abs(lam[i])<threshold)==(band=='low'))]
   bands.append(dict(m=m,B=B,threshold=fmt(threshold),band=band,excited_level_count=len(inds),indices=';'.join(map(str,inds)),S_band=fmt(mp.fsum(terms[i] for i in inds)),overlap_band=fmt(mp.fsum(a[i]**2 for i in inds)),zero_mass_added_to_total=fmt(z)))
 angles=[]
 for c in r['ladder']['clusters']:
  forced=max(0,r['ladder']['ladder_rank']+c['k']+1-(m+1))
  for i,(ang,cs,sn) in enumerate(zip(c['canonical_angles_degrees'],c['canonical_cosines'],c['canonical_sines_from_residual'])):
   angles.append(dict(m=m,k=c['k'],angle_index=i,angle_degrees_raw=ang,angle_degrees_display='0 (dimension-forced)' if i<forced else ang,cosine=cs,sine=sn,cluster_dimension=c['cluster_dimension'],ladder_rank=c['ladder_rank'],forced_intersection_dimension=forced,unmatched_cluster_dimensions=c['unmatched_cluster_dimensions'],unmatched_ladder_dimensions=c['unmatched_ladder_dimensions']))
 return dict(summary=summ,levels=levels,bands=bands,angles=angles,core=r,exterior=x)

def writecsv(name,rows):
 with (P/name).open('w') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)

cells=[load_cell(m) for m in (12,16,20,24)]
for key in ('levels','bands','angles'):writecsv(key+'.csv',[r for c in cells for r in c[key]])
writecsv('summary.csv',[c['summary'] for c in cells])
validation=load_cell(24,140,160);base=cells[-1]
checks={}
for key in ('lambda_i','a_i','F_i','X_i_independent','full_inverse_weighted_term','X_over_F'):
 vals=[]
 for lo,hi in zip(base['levels'],validation['levels']):
  aa,bb=mp.mpf(lo[key]),mp.mpf(hi[key]);vals.append(abs((aa-bb)/bb) if bb else abs(aa-bb))
 checks[key+'_max_relative']=fmt(max(vals))
checks['principal_angles_max_absolute_degrees']=fmt(max(abs(mp.mpf(a['angle_degrees_raw'])-mp.mpf(b['angle_degrees_raw'])) for a,b in zip(base['angles'],validation['angles'])))
checks['m24_140_summary']=validation['summary']
(P/'validation.json').write_text(json.dumps(checks,indent=2)+'\n')
(P/'results.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',summaries=[c['summary'] for c in cells],validation=checks),indent=2)+'\n')
lines=['# Low-cluster canary','', '**DIAGNOSTIC_NEVER_A_PROOF — K7.** Literal even CCM, N=m, L=log m. No cofinal or RH claim.','', 'Source: `PROSHKA_VERDICT_NOESCAPE_F_ONLY_2026-11-02.md`, inbox commit `777c504c07512487b758e41aab120edd686f27d3`, Git blob `c2633b50199981b80da01610c64e2239c0494e82`; definitions: NOESCAPE (4.7)–(4.14), SHA256 `fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded`.','', '## Full even-sector sums','', 'Every even level i=0..m is in levels.csv. The sums below exclude i=0 and include every computed nonzero excited eigenvalue, without a small-eigenvalue cutoff. All computed eigenvalues are positive and resolved relative to the eigensolver residual. No numerical zero modes were observed, so z=0 in this diagnostic; this is not an interval-certified kernel classification.','', '| m | 1−a0² | S from independent F+X | S_F | max excited |X/F| | level | max relative closure |','|---|---|---|---|---|---|---|']
# Escape literal bars in the table header.
lines[-2]='| m | 1−a0² | S from independent F+X | S_F | max excited X/F magnitude | level | max relative closure |'
for c in cells:
 r=c['summary'];lines.append('| '+' | '.join([str(r['m'])]+[mp.nstr(mp.mpf(r[k]),12) for k in ('one_minus_a0_squared','S_independent','S_F_only','max_X_over_F')]+[str(r['max_ratio_level']),mp.nstr(mp.mpf(r['max_closure_relative']),6)])+' |')
lines+=['', '## Polynomial bands','', 'Low means 0<|lambda_i|<m^(-B), excited levels only; high is its complement among nonzero excited levels. Each pair of rows sums to S (z=0).','', '| m | B | low count | low sum | high count | high sum |','|---|---|---|---|---|---|']
for c in cells:
 for j in range(0,6,2):
  a,b=c['bands'][j:j+2];lines.append('| '+' | '.join([str(a['m']),str(a['B']),str(a['excited_level_count']),mp.nstr(mp.mpf(a['S_band']),13),str(b['excited_level_count']),mp.nstr(mp.mpf(b['S_band']),8)])+' |')
lines+=['', '## Ladder principal angles (degrees)','', 'Profiles: h,h_second,h_fourth,h_sixth,Dh,Dh_second with D=−x d/dx−1/2, projected from the full theta profiles, H=hat h=4xi. Column-scaled SVD gives ladder rank six in all cells.','', '| m | k | canonical angles, degrees |','|---|---|---|']
for c in cells:
 for k in (3,5,7):
  aa=[a for a in c['angles'] if a['k']==k]
  nums=['0*' if a['angle_index']<a['forced_intersection_dimension'] else mp.nstr(mp.mpf(a['angle_degrees_raw']),8) for a in aa]
  lines.append('| '+str(c['summary']['m'])+' | '+str(k)+' | '+', '.join(nums)+' |')
lines+=['', 'For k=3, two ladder dimensions are unmatched. For k=7, two cluster dimensions are unmatched. At m12,k7, the first zero angle (*) is forced by 6+8>13; its tiny raw numerical value is rounding, not extra evidence of alignment. Full cosines/sines and dimension accounting are in angles.csv.','', '## Independent computation and controls','', 'F is the signed whole-line Xi tail from the source row formula, with cutoffs 128,160,192. The high modes enter only F, never the active matrix. Archimedean sine moments are evaluated by a digamma identity plus an exponentially convergent correction, independently checked against all off-diagonal active entries. The matrix includes all prime powers through m, including 19 and 23 when applicable.','', 'X is evaluated independently as k(h_out,e_j)−k(W,e_j)+sum_l A_jl<W,e_l>, then paired with every eigenvector. Physical archimedean integrals, both even tails, all supported prime powers (including n>m for h_out), the pole, and finite projection correction are retained. No X=T−F reconstruction is used. Equation F+X=−Z lambda a is a posteriori validation only. The exterior JSON records each component and omitted-tail indicators.','', 'Production: mpmath100dps, composite Gauss-Legendre128. Validation: complete m24 cell at140dps/GL160, including independent X and ladder. Additional X convergence checks: m12GL64 and m16GL96. No interval quadrature enclosure is claimed.','', '| m24 validation quantity | maximum relative discrepancy |','|---|---|']
for k,v in checks.items():
 if isinstance(v,str) and k.endswith('_max_relative'):lines.append('| '+k+' | '+mp.nstr(mp.mpf(v),7)+' |')
lines+=['', 'Maximum absolute angle discrepancy (degrees): '+mp.nstr(mp.mpf(checks['principal_angles_max_absolute_degrees']),8)+'.','', 'Explicit F-vector tail bounds beyond192 (also bounding each coordinate) are approximately 1.14e−157,1.93e−140,2.57e−129,2.08e−121 for m12,16,20,24. See tail_bound.py/results and its elementary Gamma/zeta derivation. They bound only the truncation tail, not floating roundoff or quadrature. Exterior tail indicators similarly do not certify numerical quadrature.','', '## Interpretation','', 'These finite cells retain most theta mass in the chosen bottom; the excited inverse-weighted mass is concentrated in the polynomial low cluster. The maximum coordinatewise exterior ratio is measured across all excited levels, not only i1. None of these finite measurements supplies an unbounded subsequence, a uniform strict margin, or eta_m→0. The six-profile ladder has several small principal angles but a large worst angle for the six-level cluster; unmatched dimensions are not suppressed.','', '## Reproduction','', 'Install mpmath and run from this directory:','', '```bash','uv run --with mpmath python3 core.py 100 128 12 16 20 24','uv run --with mpmath python3 core.py 140 160 24','for m in 12 16 20 24; do uv run --with mpmath python3 exterior.py "$m" 100 128; done','uv run --with mpmath python3 exterior.py 24 140 160','uv run --with mpmath python3 finalize.py','```','', 'exterior.py uses the repository full_center_probe.py to form its projection matrix when none is passed; core.py includes the same literal formula in matrix_core.py. No route-status files are changed.']
(P/'RESULT.md').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines[:20]));print(json.dumps(checks,indent=2))
