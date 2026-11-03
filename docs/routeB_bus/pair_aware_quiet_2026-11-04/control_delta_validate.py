"""Independent row/null dual-span checks at unchanged768bits; no source replay."""
from pathlib import Path
import json,csv,time
import numpy as np
import scipy.linalg as la
import control_delta as c

def run(world,m):
 p=c.OUT/f'control_delta_{world}_m{m}.json';old=json.loads(p.read_text());q=old['q'];r=old['r'];saved=np.load(c.LOCAL/f'{world}_m{m}_Q_AQ.npz');Qrow=saved['Q'];A=np.load(c.LOCAL/f'{world}_m{m}_A.npz')['A'];c.g.get_context().precision=768;events=c.scan.events(world);start=time.monotonic();Qnull=c.scan.last_null(events,q,m,768);projector=float(la.norm(Qrow@Qrow.T-Qnull@Qnull.T,2));delta_null=float(la.norm(A@Qnull,2));delta_row=float(old['delta']);norm=float(la.norm(A,2));guard=float(old['original_numeric_guard']);projector_guard=guard/max(1.,norm);diff=abs(delta_null-delta_row);roworth=float(la.norm(Qrow.T@Qrow-np.eye(r),2));nullorth=float(la.norm(Qnull.T@Qnull-np.eye(r),2));bound=norm*(projector+2*(roworth+nullorth))
 out=dict(status='PASS_NUMERIC_DUAL_SPAN_CHECK'if projector<=projector_guard and diff<=guard else'FAIL_NUMERIC_DUAL_SPAN_CHECK',world=world,m=m,q=q,r=r,bits=768,row_recipe='original physical-row ordered native MGS followed by complete float QR',null_recipe='unchanged original midscan.last_null Cauchy polynomial basis followed by native MGS; no precision increase',row_delta=delta_row,null_delta=delta_null,absolute_delta_difference=diff,original_delta_guard=guard,projector_operator_norm=projector,projector_guard=projector_guard,source_operator_norm=norm,delta_difference_bound_from_projector=bound,bound_formula='||A||*(projector_difference+2*(row_orthogonality_defect+null_orthogonality_defect)); conservative finite float diagnostic, not an interval bound',row_Q_orthogonality=roworth,null_Q_orthogonality=nullorth,row_minimum_relative_MGS_pivot=old['minimum_relative_MGS_pivot'],null_minimum_relative_MGS_pivot='not returned by unchanged last_null; original function discards it',source_A_array_sha256=old['source_A_array_sha256'],row_Q_array_sha256=old['Q_array_sha256'],source_regeneration=False,seconds=time.monotonic()-start,scope='fixed numerical point inputs; independent algebraic nullspace representation; not interval certification')
 (c.OUT/f'control_delta_dualspan_{world}_m{m}.json').write_text(json.dumps(out,indent=2)+'\n');print(world,m,out['status'],'projector',projector,'delta_diff',diff,flush=True);return out

if __name__=='__main__':
 # Plant121 was not missing and noA was generated; firstmissingplant122 supplies sixth control.
 tasks=[('dh',121),('dh',200),('dh',300),('plant',122),('plant',200),('plant',300)]
 rows=[run(w,m) for w,m in tasks];manifest=dict(status='ALL_SIX_DUAL_SPAN_CHECKS_PASS'if all(z['status'].startswith('PASS')for z in rows)else'DUAL_SPAN_CHECK_FAILURE',selection_note='DH121/200/300 and plant200/300 are selected requested missingcells; plant121 already had originalκ1δ and no localA, so plant122(firstmissingplant) supplies sixth pilot without source regeneration.',rows=rows)
 (c.OUT/'control_delta_dualspan.json').write_text(json.dumps(manifest,indent=2)+'\n')
 with (c.OUT/'control_delta_dualspan.csv').open('w')as f:
  keys=['world','m','q','r','bits','row_delta','null_delta','absolute_delta_difference','original_delta_guard','projector_operator_norm','projector_guard','delta_difference_bound_from_projector','row_Q_orthogonality','null_Q_orthogonality','row_minimum_relative_MGS_pivot','status'];w=csv.DictWriter(f,fieldnames=keys,extrasaction='ignore');w.writeheader();w.writerows(rows)
