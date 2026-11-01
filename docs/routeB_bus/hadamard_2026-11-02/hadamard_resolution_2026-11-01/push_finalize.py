import json,csv
from pathlib import Path
import mpmath as mp
mp.mp.dps=160
D=Path(__file__).resolve().parent
A=json.loads((D/'push_dps100_gl128.json').read_text());B=json.loads((D/'push_dps140_gl160.json').read_text());ref={r['N']:r for r in B}
rows=[];maxerr=mp.mpf(0)
for a in A:
 N=a['N'];b=ref[N];v=mp.mpf(a['lambda0']);w=mp.mpf(b['lambda0']);err=abs(v-w)/abs(w);maxerr=max(maxerr,err)
 r=dict(m=8,N=N,requested=N in(48,56,64),lambda0=a['lambda0'],relative_validation_difference=mp.nstr(err,40),residual=a['residual'],gap=a['gap'])
 if N+4 in ref:
  z=mp.mpf(ref[N+4]['lambda0']);ratio=w/z
  r.update(ratio_N_to_Nplus4=mp.nstr(ratio,60),relative_change_N_to_Nplus4=mp.nstr(ratio-1,60),relative_1e_3_pass=bool(abs(ratio-1)<=mp.mpf('.001')))
 else:r.update(ratio_N_to_Nplus4='',relative_change_N_to_Nplus4='',relative_1e_3_pass='not tested')
 rows.append(r)
(D/'push_results.json').write_text(json.dumps(rows,indent=2)+'\n')
with (D/'push_results.csv').open('w') as f:
 cw=csv.DictWriter(f,fieldnames=list(rows[0]));cw.writeheader();cw.writerows(rows)
summary=dict(m=8,dps=100,order=128,panels=8,validation_dps=140,validation_order=160,max_relative_validation_difference=mp.nstr(maxerr,40),converged_requested_N=[r['N'] for r in rows if r['requested'] and r['relative_1e_3_pass'] is True],criterion='abs(lambda_N/lambda_(N+4)-1)<=0.001',interval_certificate=False)
(D/'push_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
for r in rows:print(r['N'],mp.nstr(mp.mpf(r['lambda0']),16),mp.nstr(mp.mpf(r['ratio_N_to_Nplus4']),16) if r['ratio_N_to_Nplus4'] else '')
