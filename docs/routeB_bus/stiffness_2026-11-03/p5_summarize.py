"""Aggregate P5 saved diagnostics without rebuilding sources/frames."""
from pathlib import Path
import json,csv
P=Path(__file__).resolve().parent
summary=[];basis=[];spectra=[];controls=[]
for path in sorted(P.glob('p5_*_m*.json')):
 z=json.loads(path.read_text());mode=z.get('precision',path.name)
 if z['status']!='DIAGNOSTIC_NEVER_A_PROOF':summary.append(dict(m=z['m'],precision=mode,status=z['status']));continue
 vals=z['quiet_basis_diagonal'];ev=z['quiet_curvature_eigenvalues'];mp='mpmath'in mode
 def f(x):return float(x)if x is not None else None
 full=z['full_root'].get('a_star');trial=z['quiet_trial_root'].get('a_star');pred=z['registered_prediction'];corr=z['corrected_threshold_prediction']
 row=dict(m=z['m'],precision=mode,status=z['status'],epsilon=z['epsilon'],source_gate=z['source_gate_max_entry'],gate_tolerance=z['source_gate_tolerance'],quiet_dimension=len(vals),negative_basis_count=sum(f(v)<0 for v in vals),nonnegative_basis_count=sum(f(v)>=0 for v in vals),S4_all_basis_negative=z['quiet_basis_all_negative'],curvature_compression_minimum=ev[0],curvature_compression_maximum=ev[-1],quiet_lambda=z['quiet_minimum'],qmin_curvature=z['qmin_curvature'],registered_prediction=pred,corrected_threshold_prediction=corr,full_crossing=full,quiet_trial_crossing=trial,full_over_registered=z.get('full_over_registered',f(full)/f(pred)if full and pred else None),full_over_corrected=z.get('full_over_corrected',f(full)/f(corr)if full and corr else None),S5_factor2_pass=(.5<=f(full)/f(pred)<=2)if full and pred else None,full_threshold_lower=z['full_root'].get('threshold_eigenvalue_lower'),full_threshold_upper=z['full_root'].get('threshold_eigenvalue_upper'),lowpart_zero_count=z['lowpart_known_positive_zero_count'],balanced_remainder_frobenius=z.get('source_minus_lowpart_frobenius_norm'))
 summary.append(row)
 for j,(h,low,tail)in enumerate(zip(vals,z['lowpart_diagonal'],z['source_minus_lowpart_diagonal'])):basis.append(dict(m=z['m'],precision=mode,basis_index=j,h_source=h,lowpart=low,source_minus_lowpart=tail,negative=f(h)<0))
 for kind,key in [('source_curvature','quiet_curvature_eigenvalues'),('knownzero_lowpart','lowpart_compression_eigenvalues'),('source_minus_lowpart','source_minus_lowpart_eigenvalues')]:
  for j,v in enumerate(z.get(key,[])):spectra.append(dict(m=z['m'],precision=mode,kind=kind,index=j,eigenvalue=v,classification='unresolved_if_at_source_or_float_floor'))
 for c in z.get('controls',[]):controls.append(dict(m=z['m'],epsilon=z['epsilon'],**c))
for name,rows in [('p5_summary.csv',summary),('p5_basis.csv',basis),('p5_spectra.csv',spectra),('p5_controls.csv',controls)]:
 keys=list(dict.fromkeys(k for row in rows for k in row))
 with(P/name).open('w',newline='')as f:
  w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
print('P5 aggregates',len(summary),len(basis),len(spectra),len(controls))
