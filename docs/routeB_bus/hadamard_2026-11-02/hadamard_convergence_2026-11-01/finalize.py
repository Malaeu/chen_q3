import json,csv
from pathlib import Path
import mpmath as mp
mp.mp.dps=150
D=Path(__file__).resolve().parent
A=json.loads((D/'convergence_dps100_gl96.json').read_text());B=json.loads((D/'convergence_dps140_gl128.json').read_text());ref={(r['m'],r['N']):r for r in B}
requested=(8,12,16,20,24,28,32,40)
rows=[];maxerr=mp.mpf(0)
for a in A:
 m,N=a['m'],a['N'];b=ref[m,N];v=mp.mpf(a['lambda0']);w=mp.mpf(b['lambda0']);err=abs(v-w)/abs(w);maxerr=max(maxerr,err)
 r=dict(m=m,N=N,requested=N in requested,lambda0=a['lambda0'],relative_100dps_GL96_vs_140dps_GL128=mp.nstr(err,30),gap=a['gap'],residual=a['residual'])
 if N+4<=44:
  z=mp.mpf(ref[m,N+4]['lambda0']);ratio=w/z
  r.update(ratio_N_to_Nplus4=mp.nstr(ratio,60),relative_change_to_Nplus4=mp.nstr(ratio-1,60),relative_1e_3_converged=bool(abs(ratio-1)<=mp.mpf('.001')))
 else:r.update(ratio_N_to_Nplus4='',relative_change_to_Nplus4='',relative_1e_3_converged='not tested')
 rows.append(r)
(D/'convergence_results.json').write_text(json.dumps(rows,indent=2)+'\n')
with (D/'convergence_results.csv').open('w') as f:
 cw=csv.DictWriter(f,fieldnames=list(rows[0]));cw.writeheader();cw.writerows(rows)
summary=dict(status='NO_RELATIVE_CONVERGENCE_IN_REQUESTED_N_RANGE',dps=100,quadrature_order=96,quadrature_panels=8,validation_dps=140,validation_order=128,validation_max_relative_eigenvalue_discrepancy=mp.nstr(maxerr,40),converged_N={str(m):None for m in(8,12,16)},requested_N=list(requested),auxiliary_N=[36,44],minmax_in_N_violations=sum(mp.mpf(r['ratio_N_to_Nplus4'])<1 for r in rows if r['ratio_N_to_Nplus4']),precision_floor_reached=False,converged_N_scan_status='UNAVAILABLE_NO_VALIDATED_CONVERGED_N',interval_certificate=False)
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
print('\nRequested table:')
for r in rows:
 if r['requested']:print(r['m'],r['N'],mp.nstr(mp.mpf(r['lambda0']),14),mp.nstr(mp.mpf(r['ratio_N_to_Nplus4']),12))
