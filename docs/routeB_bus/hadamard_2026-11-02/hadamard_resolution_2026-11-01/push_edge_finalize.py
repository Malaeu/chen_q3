from pathlib import Path
import json,csv
import mpmath as mp
mp.mp.dps=160
D=Path(__file__).resolve().parent
A=json.loads((D/'push_edge_dps100_gl128.json').read_text());B=json.loads((D/'push_edge_dps140_gl160.json').read_text());ref={r['N']:r for r in B}
rows=[];err=mp.mpf(0)
for a in A:
 b=ref[a['N']];e=abs(mp.mpf(a['R'])/mp.mpf(b['R'])-1);err=max(err,e)
 a['relative_R_validation_difference']=mp.nstr(e,40);rows.append(a)
with (D/'push_edge.csv').open('w') as f:
 cw=csv.DictWriter(f,fieldnames=list(rows[0]));cw.writeheader();cw.writerows(rows)
(D/'push_edge.json').write_text(json.dumps(rows,indent=2)+'\n')
summary=dict(status='FLOATING_DIAGNOSTIC',definition='R=|f_N(L/2)|^2/lambda0_N; f_N is L2-normalized eigenfunction',dps=100,order=128,validation_dps=140,validation_order=160,max_relative_R_validation_difference=mp.nstr(err,40),R_min=mp.nstr(min(mp.mpf(r['R']) for r in rows),40),R_max=mp.nstr(max(mp.mpf(r['R']) for r in rows),40),all_R_between_26_and_28=all(26<=mp.mpf(r['R'])<=28 for r in rows),interval_certificate=False)
(D/'push_edge_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
for r in rows:print(r['N'],mp.nstr(mp.mpf(r['lambda0']),16),mp.nstr(mp.mpf(r['edge_squared']),16),mp.nstr(mp.mpf(r['R']),16),mp.nstr(mp.mpf(r['R_over_L']),16))
