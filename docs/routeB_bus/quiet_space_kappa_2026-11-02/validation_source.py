"""Cross-precision arithmetic-matrix check on independently constructed m40 kernels."""
from pathlib import Path
import json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=220;S=P.parent/'cluster_count_2026-11-02/level_zero_ladder'
A=mp.matrix(json.loads((S/'cell_m40_dps160_gl128.json').read_text())['A']);B=mp.matrix(json.loads((S/'cell_m40_dps180_gl160.json').read_text())['A']);rows=[]
for r in json.loads((P/'validation_m40.json').read_text()):
 Q=mp.matrix(r['Q']);v=[]
 for M in [A,B]:
  X=M*Q;ev=mp.eigsy(X.T*X,eigvals_only=True);e=mp.eigsy(Q.T*X,eigvals_only=True);v.append((mp.sqrt(ev[ev.rows-1]),max(abs(t) for t in e)))
 rows.append(dict(q=r['q'],full_relative_difference=mp.nstr(abs(v[0][0]/v[1][0]-1),100),compressed_relative_difference=mp.nstr(abs(v[0][1]/v[1][1]-1),100)))
summary=dict(matrix_Frobenius_difference=mp.nstr(mp.norm(A-B),100),max_full_relative_difference=mp.nstr(max(mp.mpf(r['full_relative_difference']) for r in rows),100),max_compressed_relative_difference=mp.nstr(max(mp.mpf(r['compressed_relative_difference']) for r in rows),100),cells=rows)
(P/'validation_source.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary['max_full_relative_difference'],summary['max_compressed_relative_difference'])
