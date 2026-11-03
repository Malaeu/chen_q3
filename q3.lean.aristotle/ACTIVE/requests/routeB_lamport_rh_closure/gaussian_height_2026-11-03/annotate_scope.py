"""Add explicit finite-census scope and conservative observed-prefix sensitivity."""
from pathlib import Path
import json
P=Path(__file__).resolve().parent
for f in(P/'cells').glob('*.json'):
 d=json.loads(f.read_text())
 for r,receipt in zip(d['summary'],d['receipts']):
  if 'roundoff_guard_before_census_sensitivity'in r:continue
  old=r['guard'];pad=old+8*r['tail_checks'][1]['operator_difference'];r.update(matrix_heuristic_budget=old+4*r['tail_checks'][1]['operator_difference'],roundoff_guard_before_census_sensitivity=old,observed_prefix_sensitivity_allowance=pad,guard=old+pad,scope='FINITE_CENSUS_WITH_HEURISTIC_GUARD; NO_BOUND_ON_UNLISTED_ZEROS')
  r['max_gap_lower']-=pad;r['max_gap_upper']+=pad
  for b in receipt['bounded']:b['gap_upper']+=pad
  r['status']='PASS_NUMERIC'if r['best_gap']>r['guard']else('FAIL_NUMERIC'if r['max_gap_upper']<0 else'UNRESOLVED')
 f.write_text(json.dumps(d,indent=2)+'\n')
