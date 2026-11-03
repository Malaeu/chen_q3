import json,csv
from decimal import Decimal
from pathlib import Path
from collections import Counter
P=Path(__file__).resolve().parent
W=['zeta','dh','plant'];rows=[];missing=[]
for m in range(16,301):
 for w in W:
  path=P/'vectors'/f'{w}_m{m}.json'
  if not path.exists():missing.append(dict(m=m,world=w));continue
  a=json.loads(path.read_text())
  for par,b in zip(['even','odd'],a['blocks']):
   a[f'lambda_{par}1_sign_resolved']=abs(Decimal(b['lambda1']))>1000*Decimal(b['eigenvalue_empirical_error'][1])
  rows.append(a)
fields=['m','world','lambda_even0','lambda_even1','lambda_odd0','lambda_odd1','lambda_even1_sign_resolved','lambda_odd1_sign_resolved','even_gap','odd_gap','parity_gap','global_gap','global_ground_parity','global_simple_even','ground_resolved','status','source_precision_bits','precision_bits','FT_precision_ok','FT_precision_margin_ratio','total_cell_seconds']
tmp=P/'spectra.csv.tmp'
with tmp.open('w',newline='') as f:
 wr=csv.DictWriter(f,fields,extrasaction='ignore');wr.writeheader();wr.writerows(rows)
tmp.replace(P/'spectra.csv')
meta=dict(expected_world_cells=855,completed_world_cells=len(rows),completed_integer_m=len([m for m in range(16,301) if all(any(a['m']==m and a['world']==w for a in rows) for w in W)]),missing=missing,status_counts=dict(Counter(a['status'] for a in rows)),global_parity_counts={w:dict(Counter(a['global_ground_parity'] for a in rows if a['world']==w)) for w in W},unresolved=[dict(m=a['m'],world=a['world']) for a in rows if not a['ground_resolved']],source_hashes={k:sorted({a['hashes'][k] for a in rows}) for k in ['source_50777d4.py','analytic_source.py']},certificate=False)
(P/'completeness.json.tmp').write_text(json.dumps(meta,indent=2)+'\n');(P/'completeness.json.tmp').replace(P/'completeness.json')
print(json.dumps({k:v for k,v in meta.items() if k not in ['missing','source_hashes']},indent=2))
