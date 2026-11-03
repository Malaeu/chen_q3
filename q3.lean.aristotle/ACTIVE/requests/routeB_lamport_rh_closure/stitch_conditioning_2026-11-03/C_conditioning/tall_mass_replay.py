"""Fill missing coordinate ledgers only; existing σ/grid results unchanged."""
from core import *
mp.mp.dps=200
paths=[P/'tall_DH120_half_priority.json']+list((P/'tall_sweep').glob('dh_m*.json'))
for path in paths:
 a=json.loads(path.read_text())
 if a.get('outcome')!='RESOLVED_FIXED_DECIMAL_MATRIX' or a.get('coordinate_ledger') or a['attempts'][-1].get('weak_left'):continue
 m=a['m'];E,labels,heights,metric=rows_for('dh',m,cutoff(m,'.5'));s=sigma_min(E,maxiter=35);a['coordinate_ledger']=dict(dps=200,scope='SAME fixed80-digit root inputs; bookkeeping only',relative_sigma_replay=mp.nstr(abs(s['sigma']/mp.mpf(a['attempts'][0]['sigma'])-1),50),relative_residual=mp.nstr(s['relative_residual'],40),weak_left=[dict(label=label,coordinate=mp.nstr(value,120),mass=mp.nstr(abs(value)**2,120))for label,value in zip(labels,s['left'])]);temp=path.with_suffix('.coord.tmp');temp.write_text(json.dumps(a,indent=2)+'\n');temp.replace(path);print('LEDGER',m,flush=True)
