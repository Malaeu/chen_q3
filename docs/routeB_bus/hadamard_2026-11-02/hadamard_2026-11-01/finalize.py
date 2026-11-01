import json,hashlib,csv
from pathlib import Path
import mpmath as mp
mp.mp.dps=80
p=Path(__file__).resolve().parent
raw=[json.loads(x) for x in (p/'results_gl64.jsonl').read_text().splitlines()]
uniq={}
for r in raw:uniq[(r['L'],r['N'],r['tag'],r['side'])]=r
rows=sorted(uniq.values(),key=lambda r:(mp.mpf(r['L']),r['N'],str(r['side'])))
(p/'hadamard_results.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
summary={'status':'DPS80_FLOATING_DIAGNOSTIC_NOT_CERTIFICATE','dps':80,'quadrature':'8-panel Gauss-Legendre order64','fd_step':'1e-7','fd_order':4,'rows':len(rows),'points':len(set(r['L'] for r in rows)),'branches':{},'thresholds':[]}
for N in (8,12):
 rr=[r for r in rows if r['N']==N]
 summary['branches'][str(N)]={
  'positive_derivative_rows':sum(r['derivative_sign']>0 for r in rr),
  'negative_derivative_rows':sum(r['derivative_sign']<0 for r in rr),
  'lambda_min':min(rr,key=lambda r:mp.mpf(r['lambda0'])),
  'lambda_max':max(rr,key=lambda r:mp.mpf(r['lambda0'])),
  'r_min':min(rr,key=lambda r:mp.mpf(r['r_HF'])),
  'r_max':max(rr,key=lambda r:mp.mpf(r['r_HF'])),
  'max_relative_derivative_difference':str(max(mp.mpf(r['relative_derivative_difference']) for r in rr)),
  'positive_derivative_samples':[{'L':r['L'],'side':r['side'],'derivative_HF':r['derivative_HF'],'r_HF':r['r_HF']} for r in rr if r['derivative_sign']>0]}
for k in range(8,17):
 summary['thresholds'].append({'k':k,'rows':[r for r in rows if r['threshold']==k and r['tag']=='threshold']})
summary['literal_diagonal']=[r for r in rows if r['literal_comparison']]
(p/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
with (p/'hadamard_results.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
with (p/'threshold_table.csv').open('w',newline='') as f:
 names=['k','N','lambda0','derivative_left_HF','derivative_right_HF','r_left_HF','r_right_HF','r_left_FD','r_right_FD']
 w=csv.DictWriter(f,fieldnames=names);w.writeheader()
 for k in range(8,17):
  for N in (8,12):
   rr={r['side']:r for r in rows if r['threshold']==k and r['N']==N and r['tag']=='threshold'}
   a,b=rr['left'],rr['right']
   w.writerow(dict(k=k,N=N,lambda0=a['lambda0'],derivative_left_HF=a['derivative_HF'],derivative_right_HF=b['derivative_HF'],r_left_HF=a['r_HF'],r_right_HF=b['r_HF'],r_left_FD=a['r_FD'],r_right_FD=b['r_FD']))
print('ROWS',len(rows),'POINTS',summary['points'])
for N,b in summary['branches'].items():
 print('N',N,'derivative+',b['positive_derivative_rows'],'derivative-',b['negative_derivative_rows'],'maxFDrel',b['max_relative_derivative_difference'])
 for key in ('lambda_min','lambda_max','r_min','r_max'):
  r=b[key];print(key,'L',r['L'],'lambda',r['lambda0'],'r',r['r_HF'])
 print('positive L:',[(r['L'],r['side']) for r in b['positive_derivative_samples']])
