from pathlib import Path
import json,csv
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=220;rows=[]
for m in [16,24,32,40]:
 main=json.loads((P/f'cell_m{m}.json').read_text())
 for r in json.loads((P/f'validation_m{m}.json').read_text()):
  q=r['q'];s=main['cache'][str(q)];Q=mp.matrix(r['Q']);U=mp.matrix(s['Q']);err=mp.norm(Q*Q.T-U*U.T)
  rows.append(dict(m=m,q=q,projector_Frobenius_difference=mp.nstr(err,100),full_norm_relative_difference=mp.nstr(abs(mp.mpf(r['full_AQ_operator_norm'])/mp.mpf(s['delta'])-1),100),compressed_norm_relative_difference=mp.nstr(abs(mp.mpf(r['compressed_operator_norm'])/mp.mpf(s['beta'])-1),100),polynomial_kernel_residual=r['kernel_residual'],polynomial_orthogonality_residual=r['orthogonality_residual'],rank=m+1-q))
with (P/'validation_comparison.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
summary=dict(cells=len(rows),max_projector_difference=mp.nstr(max(mp.mpf(r['projector_Frobenius_difference']) for r in rows),80),max_full_norm_relative_difference=mp.nstr(max(mp.mpf(r['full_norm_relative_difference']) for r in rows),80),max_compressed_norm_relative_difference=mp.nstr(max(mp.mpf(r['compressed_norm_relative_difference']) for r in rows),80),max_kernel_residual=mp.nstr(max(mp.mpf(r['polynomial_kernel_residual']) for r in rows),80),max_orthogonality_residual=mp.nstr(max(mp.mpf(r['polynomial_orthogonality_residual']) for r in rows),80))
(P/'validation_summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
