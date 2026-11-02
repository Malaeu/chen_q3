"""Correct support labels only; do not rewrite numeric source inputs or solves."""
from pathlib import Path
import json
P=Path(__file__).resolve().parent
ZERO=set(json.loads((P/'DH_EXACT_COEFFICIENTS.json').read_text())['zero_indices'])
def annotate(d):
 if d['world']=='dh' and d['m'] in ZERO and 'b_m' in d:
  if 'numeric_recurrence_birth_raw' not in d:
   d['numeric_recurrence_birth_raw']={k:d[k] for k in ['b_m','birth_source_coefficient','birth_inverse_kernel_derivative_kinks']}
  d['b_m']='0';d['birth_source_coefficient']='0'
  d['birth_inverse_kernel_derivative_kinks']=['0']*len(d['endpoint_cross'])
  d['birth_label_scope']='EXACT_FORMAL_DIRICHLET_LOG_ZERO; source input and numerical solves unchanged'
 return d
if __name__=='__main__':
 for f in (P/'native_cells').glob('*.json'):
  d=annotate(json.loads(f.read_text()));f.write_text(json.dumps(d,indent=2)+'\n')
