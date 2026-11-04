#!/usr/bin/env python3
"""Fresh float predecessor check; no high-precision ordering claim."""
import json,time
from pathlib import Path
from fractions import Fraction
import numpy as np
from scipy.linalg import eigvalsh
from threadpoolctl import threadpool_limits
from matrix_probe import build,coefficients
P=Path(__file__).resolve().parent
start=time.perf_counter();rows=[]
for g in json.loads((P/'prefix_summary.json').read_text())['groups']:
 for a,m in g['first'].items():
  if m==g['m_admit']:continue
  mm=m-1; A,meta=build(mm);c=coefficients(mm,float(Fraction(a)),g['gamma'])
  Q=4*(np.outer(c.real,c.real)-np.outer(c.imag,c.imag))
  with threadpool_limits(limits=1):v=float(eigvalsh(A+Q,subset_by_index=[0,0],driver='evr',check_finite=False)[0])
  old=next(r['lambda_min'] for r in json.loads((P/f'matrix_cells/m{mm}.json').read_text())['cases'] if r['a']==a and r['gamma']==g['gamma'])
  assert v>=-1e-6
  rows.append(dict(a=a,gamma=g['gamma'],first=m,predecessor=mm,fresh_lambda=v,saved_lambda=old,difference=v-old,builder_sha256=meta['builder_sha256']))
  print(mm,a,g['gamma'],v,flush=True)
out=dict(status='ALL_9_LATER_THRESHOLDS_PREDECESSORS_RECHECKED',rows=rows,precision='float64 eigenvalue; longdouble arithmetic source moments',scope='Fresh independent assembly, no MP predecessor ordering or interval enclosure.',wall_seconds=time.perf_counter()-start)
(P/'predecessor_recheck.json').write_text(json.dumps(out,indent=2)+'\n')
