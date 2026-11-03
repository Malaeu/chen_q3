from pathlib import Path
import json
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=250
p=P/'tall_DH120_half_priority.json'
if not p.exists():raise SystemExit('No tall priority receipt')
a=json.loads(p.read_text())
if a['outcome']!='RESOLVED_FIXED_DECIMAL_MATRIX':raise SystemExit(a['outcome'])
s=a['attempts'][-1];p=P/'cells/dh_m120.json';cell=json.loads(p.read_text())
for r in cell['rows']:
 if r['cut']=='c_half' and r['variant']=='base':
  r.update(sigma_min=s['sigma'],sigma_min_squared=s['sigma_squared'],sigma_dps=s['dps'],sigma_iterations=s['iterations'],sigma_relative_residual=s['relative_residual'],sigma_relative_change=s['relative_change'],sigma_seconds=a['cpu_seconds'],sigma_status='MP200_240_TALL_PRIORITY',sigma_priority_source='tall_DH120_half_priority.json',weak_pair_left=s['weak_pair_left'],weak_pair_right=s['weak_pair_right'],weak_pair_mass=s['weak_pair_mass'])
  lr=r['lambda_r_preferred'];r['twice_sigma_squared_over_lambda_r']=mp.nstr(2*mp.mpf(s['sigma_squared'])/mp.mpf(lr),100) if lr is not None and mp.mpf(lr) else None
q=p.with_suffix('.tall.tmp');q.write_text(json.dumps(cell,indent=2)+'\n');q.replace(p)
