from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=130
read=lambda name:list(csv.DictReader((P/name).open()))
lo=read('metrics_dps80.csv');hi=read('metrics_dps100.csv');extra=read('metrics_dps120.csv')
keys=lambda r:(r['world'],r['m'],r['cutoff']);L={keys(r):r for r in lo};H={keys(r):r for r in hi};checks=[]
num=['sigma_section','full_minimum','full_f_norm','angle_f_J_degrees','projection_quiet_norm','projection_complement_norm','delta_full_AQ','quiet_compression_norm','lambda_r','ratio','quiet_S2_min']
ints=['rank','quiet_dimension','old_negative_index','quiet_S2_negative','quiet_D2_negative','full_A2_negative','section_S0_negative','full_A0_negative','section_S2_negative','section_C2_negative','quiet_S0_negative','quiet_D0_negative']
for key,b in H.items():
 a=L[key];assert all(a[k]==b[k] for k in ints),key
 diffs={k:abs(mp.mpf(a[k])-mp.mpf(b[k])) for k in num if a[k] and b[k]};rel={k:v/max(mp.mpf(1),abs(mp.mpf(b[k]))) for k,v in diffs.items()}
 checks.append(dict(world=key[0],m=key[1],cutoff=key[2],all_rank_and_inertia_match=True,max_absolute_change=mp.nstr(max(diffs.values()),25),max_scaled_change=mp.nstr(max(rel.values()),25)))
validation=[]
for b in extra:
 a=H[keys(b)];assert all(a[k]==b[k] for k in ints);diff=max(abs(mp.mpf(a[k])-mp.mpf(b[k])) for k in num if a[k] and b[k]);validation.append(dict(world=b['world'],m=b['m'],cutoff=b['cutoff'],maximum_absolute_100_120_change=mp.nstr(diff,25)))
preferred={**H,**{keys(r):r for r in extra}}
rows=[]
for key,r in sorted(preferred.items()):
 r=r.copy();r['angle_status']='PROJECTED_DISTANCE_CONVENTION_EMPTY_J' if r['quiet_dimension']=='0' else 'ONE_DIRECTION_PRINCIPAL_ANGLE';r['projector_partition_error']=mp.nstr(abs(mp.mpf(r['full_f_norm'])**2-mp.mpf(r['projection_quiet_norm'])**2-mp.mpf(r['projection_complement_norm'])**2),25);r['full_f_Rayleigh']=mp.nstr(mp.mpf(r['sigma_section'])/mp.mpf(r['full_f_norm'])**2,35);r['N_A2_minus_r']=int(r['full_A2_negative'])-int(r['quiet_dimension']);rows.append(r)
with (P/'preferred.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
with (P/'precision_replay.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=checks[0]);w.writeheader();w.writerows(checks)
summary=dict(status='DIAGNOSTIC_NEVER_A_PROOF',rows=len(rows),all_precision_rank_inertia_match=True,max_precision_scaled_change=max(mp.mpf(r['max_scaled_change']) for r in checks),validation120=validation,empty_J_rows=sum(r['quiet_dimension']=='0' for r in rows),quiet_D_below2_rows=sum(r['quiet_D_below2']=='True' for r in rows),nonempty_quiet_D_below2_rows=sum(r['quiet_D_below2']=='True' and int(r['quiet_dimension'])>0 for r in rows),worlds={})
for world in ['zeta','dh','plant']:
 rs=[r for r in rows if r['world']==world];summary['worlds'][world]=dict(full_A0_negative_counts=sorted(set(int(r['full_A0_negative']) for r in rs)),old_negative_counts=sorted(set(int(r['old_negative_index']) for r in rs)),section_S0_negative_counts=sorted(set(int(r['section_S0_negative']) for r in rs)),stationary_only_rows=sum(r['section_interpretation'].startswith('STATIONARY') for r in rs),minimum_full_A=mp.nstr(min(mp.mpf(r['full_minimum']) for r in rs),25),minimum_section_S0=mp.nstr(min(mp.mpf(r['sigma_section']) for r in rs),25),maximum_full_AQ=mp.nstr(max(mp.mpf(r['delta_full_AQ']) for r in rs),25))
summary['max_precision_scaled_change']=mp.nstr(summary['max_precision_scaled_change'],25)
summary['max_projector_partition_error']=mp.nstr(max(mp.mpf(x['projector_partition_error']) for x in rows),25)
summary['max_constraint_residual']=mp.nstr(max(mp.mpf(x['constraint_residual']) for x in rows),25)
summary['max_Q_orthogonality_error']=mp.nstr(max(mp.mpf(x['orthogonality_error']) for x in rows),25)
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
# Inspect every retained coordinate identity at both thresholds, including eliminated indices.
for r in rows:
 c=json.loads((P/f"cell_{r['world']}_m{r['m']}_{r['cutoff']}_dps{r['dps']}.json").read_text())
 for label in ['quiet_schur0','quiet_schur2']:
  z=c[label];assert z['guard']=='RESOLVED' and z['inertia_identity']
 for label in ['section0','section2']:
  z=c['section'][label];assert z['guard']=='RESOLVED' and z['inertia_identity']
print('PASS: both coordinate inertia identities at thresholds0and2 for every preferredcell')
