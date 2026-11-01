import json,csv
from pathlib import Path
import mpmath as mp
mp.mp.dps=100
p=Path(__file__).resolve().parent
rows=[json.loads(s) for s in (p/'five_terms.jsonl').read_text().splitlines()]
edges=[json.loads(s) for s in (p/'edge_ratios.jsonl').read_text().splitlines()]
val=json.loads((p/'decomposition_validation_dps100_gl80.json').read_text())
summary=json.loads((p/'decomposition_summary.json').read_text())
terms=['pole','arch_interior','arch_boundary','old_atom_interior','atom_boundary']
for r in rows:r['cancellation_digits']=mp.nstr(mp.log10(mp.fsum(abs(mp.mpf(r[t])) for t in terms)/abs(mp.mpf(r['sum_five']))),20)
summary['max_cancellation_row']=max(rows,key=lambda r:mp.mpf(r['cancellation_digits']))
summary['quadrature_dps_checks']=[]
for v in val['edges']:
 r=[x for x in edges if x['m']==v['m']][0]
 summary['quadrature_dps_checks'].append({'m':r['m'],**{key:mp.nstr(abs(mp.mpf(r[key])/mp.mpf(v[key])-1),20) for key in ('lambda_m','ground_edge_squared_over_lambda','projected_h_edge_squared_over_lambda','mode_jump_over_lambda_right')}})
summary['five_term_validation']=[]
for v in val['five_terms']:
 r=[x for x in rows if x['threshold']==int(mp.nint(mp.exp(mp.mpf(v['L'])))) and x['N']==v['N'] and x['side']=='right'][0]
 summary['five_term_validation'].append({'N':v['N'],'threshold':r['threshold'],'max_absolute_component_change':mp.nstr(max(abs(mp.mpf(r[t])-mp.mpf(v[t])) for t in terms),20),'relative_derivative_change':mp.nstr(abs(mp.mpf(r['sum_five'])/mp.mpf(v['sum_five'])-1),20)})
(p/'decomposition_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('EDGE TABLE: m lambda |fedge|²/lambda |P_h_edge|²/lambda Delta/lambda_right')
for r in edges:print(r['m'],*[mp.nstr(mp.mpf(r[k]),11) for k in ('lambda_m','ground_edge_squared_over_lambda','projected_h_edge_squared_over_lambda','mode_jump_over_lambda_right')])
print('Max cancellation digits:',summary['max_cancellation_row']['cancellation_digits'])
print('Max relative five sum error:',summary['max_relative_five_sum_error']['relative_sum_error'])
print('Validation:',json.dumps(summary['quadrature_dps_checks']))
