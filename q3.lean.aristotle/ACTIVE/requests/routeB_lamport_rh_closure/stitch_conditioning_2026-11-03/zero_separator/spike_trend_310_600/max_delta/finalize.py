from pathlib import Path
import json,csv,hashlib,os
P=Path(__file__).resolve().parent
rows=[];missing=[]
for m in range(310,601,10):
 for w in ['plant','dh']:
  p=P/f'{w}_m{m}.json'
  if not p.exists():missing.append((w,m));continue
  a=json.loads(p.read_text());assert a['q']+a['r']==m+1 and a['sigma_1']>=a['sigma_2'];assert a['Q_orthogonality']<1e-10
  rows.append({k:a[k] for k in ['world','m','q','r','bits','method','delta','sigma_1','sigma_2','lambda_r','gap','numeric_guard','Q_orthogonality','seconds']})
if rows:
 with (P/'MAX_DELTA.csv').open('w',newline='') as f:
  x=csv.DictWriter(f,fieldnames=rows[0]);x.writeheader();x.writerows(rows)
a=dict(status='DIAGNOSTIC_NEVER_A_PROOF',expected=60,completed=len(rows),missing=missing,max_Q_orthogonality=max((x['Q_orthogonality']for x in rows),default=None),DH_source_sha256=hashlib.sha256(Path(os.environ.get('DH_BASELINE_TABLE',str(P.parent/'source_inputs/dh_zeros_600_200dps.json'))).read_bytes()).hexdigest(),zeta_source_sha256=hashlib.sha256((P.parent/'zeta_zeros.csv').read_bytes()).hexdigest(),maximality='nested quiet spaces imply delta(kappa)>=delta(kappa_next); maximum over kappa>=1 attained at1',no_fit_performed=True)
(P/'COMPLETION.json').write_text(json.dumps(a,indent=2)+'\n');print(a)
with (P/'SHA256SUMS').open('w') as f:
 for p in sorted(list(P.glob('*.py'))+list(P.glob('*.json'))+list(P.glob('*.csv'))+list(P.glob('*.md'))):f.write(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n')
