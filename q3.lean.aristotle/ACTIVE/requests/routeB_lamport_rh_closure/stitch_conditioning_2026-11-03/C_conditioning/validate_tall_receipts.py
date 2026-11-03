"""Read-only acceptance gates for the scheduled tall conditioning receipts."""
from core import *
mp.mp.dps=150;records=[]
paths=[P/'tall_DH120_half_priority.json']+sorted((P/'tall_sweep').glob('dh_m*_half.json'))
for path in paths:
 a=json.loads(path.read_text());m=a['m']
 if a.get('outcome')!='RESOLVED_FIXED_DECIMAL_MATRIX':raise ArithmeticError(f'unresolved {path.name}')
 rel=mp.mpf(a['relative_200_240'])
 if not rel<mp.mpf('1e-20'):raise ArithmeticError(f'agreement gate {m}: {rel}')
 if [s['dps'] for s in a['attempts']]!=[200,240]:raise ArithmeticError(f'precisions {m}')
 for s in a['attempts']:
  if not(mp.mpf(s['relative_residual'])<mp.mpf('1e-30') and mp.mpf(s['relative_change'])<mp.mpf('1e-30')):raise ArithmeticError(f'iteration gate {m}')
 coord=a['attempts'][-1].get('weak_left') or a.get('coordinate_ledger',{}).get('weak_left')
 if not coord:raise ArithmeticError(f'missing weak-coordinate ledger {m}')
 total=mp.fsum(mp.mpf(r['mass'])for r in coord);mass={}
 for r in coord:
  g=r['label']['gamma'];mass[g]=mass.get(g,mp.mpf(0))+mp.mpf(r['mass'])
 hs=sorted(mass,key=lambda x:mp.mpf(x));pair=max(range(len(hs)-1),key=lambda i:mass[hs[i]]+mass[hs[i+1]]);best=mass[hs[pair]]+mass[hs[pair+1]];last=a['attempts'][-1]
 if abs(total-1)>=mp.mpf('1e-25') or abs(best-mp.mpf(last['weak_pair_mass']))>=mp.mpf('1e-25'):raise ArithmeticError(f'coordinate/pair mass gate {m}')
 sm=mp.mpf(last['sigma']);records.append(dict(m=m,q=last['q'],dimension=last['dimension'],J0=a['J_dimension']==0,sigma=str(sm),arithmetic_agreement=str(rel),left_mass_total_error=str(abs(total-1)),best_pair_left=hs[pair],best_pair_right=hs[pair+1],best_pair_mass=str(best),localization='localized'if best>=mp.mpf('.5')else'diffuse',rough80digit_scale_margin=str(80+mp.log10(sm)),margin_is_not_uncertainty_bound=True,source=str(path.relative_to(P))))
missing=[m for m in range(80,121)if m not in [r['m']for r in records]]
result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',outcome='PASS'if not missing else'PARTIAL',receipt_count=len(records),expected=41,missing=missing,acceptance_gates='relative200_240<1e-20; both residual/change<1e-30; full weak masses sum1 and pair mass matches1e-25',root_uncertainty_not_propagated=True,records=records)
(P/'tall_acceptance.json').write_text(json.dumps(result,indent=2)+'\n');print('TALL ACCEPTANCE',result['outcome'],len(records),missing)
