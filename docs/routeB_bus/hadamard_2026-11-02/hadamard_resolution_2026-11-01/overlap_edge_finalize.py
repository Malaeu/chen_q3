import json,csv
from pathlib import Path
import mpmath as mp
mp.mp.dps=160
p=Path(__file__).resolve().parent
rows=json.loads((p/'overlap_edge_dps100_gl96.json').read_text())
valid=json.loads((p/'overlap_edge_dps140_gl128.json').read_text())
summary={'status':'FINITE_DIAGNOSTIC_NOT_CERTIFICATE','N_ladder':'every integer8..44','baseline_dps':100,'baseline_GL_order':96,'validation_dps':140,'validation_GL_order':128,'rows':len(rows),'anchors':{},'validation':[]}
for m in(8,12,16):
 rr=[r for r in rows if r['m']==m]
 assert len(rr)==37
 summary['anchors'][str(m)]={'literal':[r for r in rr if r['literal']][0],'N40':[r for r in rr if r['N']==40][0],'N44':[r for r in rr if r['N']==44][0],'min_w0':min(rr,key=lambda r:mp.mpf(r['w0'])),'max_w0':max(rr,key=lambda r:mp.mpf(r['w0'])),'min_edge_ratio':min(rr,key=lambda r:mp.mpf(r['ground_edge_squared_over_lambda'])),'max_edge_ratio':max(rr,key=lambda r:mp.mpf(r['ground_edge_squared_over_lambda'])),'lambda_monotone_nonincreasing':all(mp.mpf(rr[j+1]['lambda0'])<=mp.mpf(rr[j]['lambda0']) for j in range(len(rr)-1))}
for v in valid:
 r=[r for r in rows if r['m']==v['m'] and r['N']==v['N']][0]
 summary['validation'].append({'m':r['m'],'N':r['N'],**{key:mp.nstr(abs(mp.mpf(r[key])/mp.mpf(v[key])-1),25) for key in('lambda0','ground_edge_squared_over_lambda','ground_edge_squared_over_Llambda','w0','one_minus_w0','projection_h_norm_squared')}})
(p/'overlap_edge_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('m N lambda edge²/lambda edge²/(Llambda) w0 1-w0')
for m in(8,12,16):
 for N in sorted(set([m,40,44])):
  r=[r for r in rows if r['m']==m and r['N']==N][0]
  print(m,N,*[mp.nstr(mp.mpf(r[key]),14) for key in('lambda0','ground_edge_squared_over_lambda','ground_edge_squared_over_Llambda','w0','one_minus_w0')])
print('max validation relative errors')
for key in('lambda0','ground_edge_squared_over_lambda','w0','one_minus_w0'):
 print(key,mp.nstr(max(mp.mpf(r[key]) for r in summary['validation']),12))
for m,a in summary['anchors'].items():print('m',m,'w0 minmax',a['min_w0']['N'],mp.nstr(mp.mpf(a['min_w0']['w0']),14),a['max_w0']['N'],mp.nstr(mp.mpf(a['max_w0']['w0']),14),'lambda monotone',a['lambda_monotone_nonincreasing'])
