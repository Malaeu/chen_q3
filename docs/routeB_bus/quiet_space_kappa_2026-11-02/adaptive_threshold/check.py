"""Saved-data scalar comparison only: no eigenproblems. DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
from decimal import Decimal as D, getcontext
import csv,json,hashlib
getcontext().prec=200
P=Path(__file__).resolve().parent;SRC=P.parent
PIN='77c22cb60e70634d1c75ac75538e06cdf7db5f3b'
BLOBS={16:'4aa869b9a0436bfa88fc9156fbf1776b11c5cc29',24:'2031a2a55f3e22020a33f997fb856ac9e2a207b8',32:'b20b1b426289b9ea21e6b2838b13fc957d66bff6',40:'9716570ef352f70dfe58af671b3284386cc89841'}
f=lambda x,n=9:format(D(str(x)),f'.{n}g')
rows=[];groups=[];provenance={}
for m,blob in BLOBS.items():
 path=SRC/f'cell_m{m}.json';b=path.read_bytes();actual=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert actual==blob
 provenance[path.name]={'git_blob':actual,'sha256':hashlib.sha256(b).hexdigest()}
 cell=json.loads(b);ev=list(map(D,cell['A_eigenvalues']));assert ev==sorted(ev)
 local=[]
 for old in cell['rows']:
  delta=D(old['delta']);r=old['dimension'];mu=delta*D('1.000001');n=sum(x<mu for x in ev);ratio=ev[r]/delta
  assert n>=r and ((n==r)==(ev[r-1]<mu<=ev[r]))
  assert sum(x<delta for x in ev)==n
  row=dict(m=m,kappa=old['kappa'],zero_count=old['positive_zero_count_strict'],r=r,delta=str(delta),adaptive_mu=str(mu),N_A_mu=n,count_minus_r=n-r,lambda_r=str(ev[r]),lambda_r_over_delta=str(ratio),lambda_r_minus_mu=str(ev[r]-mu),nearest_threshold_eigenvalue_distance=str(min(abs(x-mu) for x in ev)),saturates=n==r)
  rows.append(row);local.append(row)
 for q in sorted(set(x['zero_count'] for x in local)):
  rr=[x for x in local if x['zero_count']==q];a=rr[0]
  if not a['saturates']:continue
  cache=cell['cache'][str(q)];omega=D(cell['rows'][0]['Omega']);left=max(D(1),D(cache['last_included_zero'])/omega);right=min(D('1.4'),D(cache['first_excluded_zero'])/omega)
  groups.append(dict(m=m,q=q,r=a['r'],grid_kappas=','.join(f(x['kappa'],3) for x in rr),continuous_left=str(left),left_included=left==1 and D(cache['last_included_zero'])/omega<1,continuous_right=str(right),right_included=True,delta=a['delta'],N_A_mu=a['N_A_mu'],lambda_r=a['lambda_r'],gap_ratio=a['lambda_r_over_delta']))
def save(name,data):
 with (P/name).open('w',newline='') as h:
  w=csv.DictWriter(h,fieldnames=data[0]);w.writeheader();w.writerows(data)
save('scan.csv',rows);save('saturation_windows.csv',groups)
margin=min(D(x['nearest_threshold_eigenvalue_distance'])/D(x['adaptive_mu']) for x in rows)
(P/'provenance.json').write_text(json.dumps(dict(source_commit=PIN,decimal_precision=200,threshold_multiplier='1.000001',new_eigenproblems=0,source_files=provenance,points=len(rows),saturated_points=sum(x['saturates'] for x in rows),minimum_relative_threshold_distance=str(margin),inflation_changes_no_count=True),indent=2)+'\n')
lines=['# Adaptive threshold on saved interpolation quiet spaces','', '**DIAGNOSTIC_NEVER_A_PROOF.** No new eigenproblems, matrix constructions or zero computations. Source: rh_clean @'+PIN+'. Source JSON Git blobs were checked against the pinned repository files before reading. Scalar arithmetic uses200-digit Decimal.', '',
'Use μκ=δκ(1+10⁻⁶), N_A(μ)=#{λ_i<μ}, and zero-based λ_r, the first level after r lower eigenvalues. All84 original points are retained. The count includes the ground and every negative level. Strict counting means saturation is equivalent here to λ_(r−1)<μ≤λ_r; equality λ_r=μ is allowed. No equality boundary is numerically close in these data.', '',
'## Saturating sectors','',
'Unlike the fixed power thresholds, the adaptive threshold **does saturate** on the following early sectors. Within each sector the interpolation subspace and δ are unchanged. The continuous endpoints are inherited zero-entry heights divided by Ω; the listed grid points are the actual saved samples.', '',
'|m|Saved κ values|Continuous κ sector (approximately)|r=N_A(μ)|δ|λ_r|λ_r/δ|', '|---:|:---|:---|---:|---:|---:|---:|']
for g in groups:
 interval=('[' if g['left_included'] else '(')+f(g['continuous_left'],8)+', '+f(g['continuous_right'],8)+']'
 lines.append(f"|{g['m']}|{g['grid_kappas']}|{interval}|{g['r']}|{f(g['delta'])}|{f(g['lambda_r'])}|{f(g['gap_ratio'])}|")
lines+=['', 'These are finite saturation checks at the saved residual scale. They do not establish an unbounded family with a controlled residual. The previous fixed-μ failures remain unchanged: the threshold used here is different.', '',
'## Every saved κ: count excess and L12 gap ratio','',
'Each entry is **N_A(δ⁺)−r ; λ_r/δ**. Zero excess means saturation. Full δ, μ, r, λ_r and threshold margins are in scan.csv.', '',
'|κ|m16|m24|m32|m40|','|---:|:---|:---|:---|:---|']
for j in range(21):
 k=D(1)+D(j)/50;values=[]
 for m in BLOBS:
  x=next(x for x in rows if x['m']==m and D(x['kappa'])==k);values.append(str(x['count_minus_r'])+' ; '+f(x['lambda_r_over_delta'],8))
 lines.append('|'+f(k,3)+'|'+'|'.join(values)+'|')
lines+=['', '## Checks and reproduction','',
'The script checks sorted eigenvalues, N_A(μ)≥r and the exact scalar equivalence between count saturation and λ_(r−1)<μ≤λ_r for all84 rows. The1e−6 inflation changes no count; the nearest threshold-to-eigenvalue distance, relative to μ, is0.04445045. Input bytes and Git blobs are recorded in provenance.json. It imports only standard-library Decimal/JSON/CSV/hash utilities: there is no eigensolver or new linear algebra.', '',
'Run `python3 check.py` from any directory. It reads the four parent cell_m*.json files and writes scan.csv, saturation_windows.csv, provenance.json and this report. Numerical reliability inherits the parent SVD and independent polynomial-kernel validation; this postprocessing is not an interval certificate.']
(P/'RESULT.md').write_text('\n'.join(lines)+'\n')
print('points',len(rows),'saturating',sum(x['saturates'] for x in rows))
for g in groups:print(g['m'],g['grid_kappas'],'r',g['r'],'delta',f(g['delta']),'gap',f(g['gap_ratio']))
