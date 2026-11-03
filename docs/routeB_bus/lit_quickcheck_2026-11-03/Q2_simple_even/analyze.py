from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=170
allrows=[]
for f in sorted(P.glob('spectra_dps*.csv')):allrows.extend(csv.DictReader(f.open()))
keys=sorted(set((r['world'],int(r['m']),int(r['N'])) for r in allrows));preferred=[];checks=[]
for world,m,N in keys:
 rows=[r for r in allrows if r['world']==world and int(r['m'])==m and int(r['N'])==N];dps=max(int(r['dps']) for r in rows);rows=[r for r in rows if int(r['dps'])==dps];rows.sort(key=lambda r:int(r['order']));lo,hi=rows[0],rows[-1]
 error=max(abs(mp.mpf(lo[k])-mp.mpf(hi[k])) for k in ['lambda_even0','lambda_even1','lambda_odd0']);gap=min(abs(mp.mpf(hi[k])) for k in ['parity_gap','even_simple_gap']);preferred.append(hi|dict(quadrature_absolute_replay_error=mp.nstr(error,35),gap_over_quadrature_replay_error=mp.nstr(gap/error,20) if error else 'inf'))
 checks.append(dict(world=world,m=m,N=N,dps=dps,orders=str([r['order'] for r in rows]),maximum_eigenvalue_change=mp.nstr(error,30),positive_gap_both_orders=all(mp.mpf(r['parity_gap'])>mp.mpf(r['roundoff_heuristic']) and mp.mpf(r['even_simple_gap'])>mp.mpf(r['roundoff_heuristic']) for r in rows)))
with (P/'preferred.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=preferred[0]);w.writeheader();w.writerows(preferred)
with (P/'quadrature_replay.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=checks[0]);w.writeheader();w.writerows(checks)
res=[]
for world in ['zeta','dh','plant']:
 for m in [3,5,7,10,15,20,30,40,47,55]:
  rr=sorted([r for r in preferred if r['world']==world and int(r['m'])==m],key=lambda x:int(x['N']));a,b=rr
  ratio=mp.mpf(a['lambda_even0'])/mp.mpf(b['lambda_even0']);res.append(dict(world=world,m=m,N_low=a['N'],N_high=b['N'],even_lambda_ratio=mp.nstr(ratio,30),same_finite_even_simple=a['finite_even_simple']==b['finite_even_simple'],low_even_simple=a['finite_even_simple'],high_even_simple=b['finite_even_simple'],relative_eigenvalue_convergence_point001=abs(ratio-1)<mp.mpf('.001')))
with (P/'carrier_resolution.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=res[0]);w.writeheader();w.writerows(res)
z=[r for r in preferred if r['world']=='zeta'];viol=[dict(world=r['world'],m=r['m'],N=r['N'],even0=r['lambda_even0'],odd0=r['lambda_odd0'],parity_gap=r['parity_gap']) for r in preferred if mp.mpf(r['parity_gap'])<-mp.mpf(r['roundoff_heuristic'])]
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',verdict_continuum='INCONCLUSIVE_RESOLUTION',verdict_finite_zeta='CONSISTENT' if all(r['finite_even_simple']=='True' for r in z) else 'INCONCLUSIVE_RESOLUTION',zeta_finite_cells=len(z),zeta_all_positive_resolved=all(r['resolved_even_ground_sign']=='positive' for r in z),zeta_relative_converged_windows=sum(r['relative_eigenvalue_convergence_point001'] for r in res if r['world']=='zeta'),violations=viol,P3='SUPPORTED_ONLY_ON_FINITE_CARRIERS;CONTINUUM_INCONCLUSIVE',P4='SUPPORTED_BY_FINITE_DH_VIOLATIONS',external_code_executed=False)
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
# Emit a concise native zeta table used verbatim in the report.
for r in preferred:
 if r['world']=='zeta' and r['m']==r['N']:print(r['m'],*[mp.nstr(mp.mpf(r[k]),6) for k in ['lambda_even0','lambda_even1','lambda_odd0','parity_gap','even_simple_gap']])
