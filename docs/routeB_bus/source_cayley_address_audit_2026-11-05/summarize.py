"""Finite gate/prediction summaries, with no changed thresholds or fresh evaluations."""
from pathlib import Path
import json,csv
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=90

def main():
 g=json.loads((P/'GATES.json').read_text());rs=g['gate_records'];out=[]
 for dps in [45,70]:
  row=dict(dps=dps,tolerance='1e-30'if dps==45 else'1e-50')
  for name in ['real_axis_unitarity','DH_functional_equation','identity_7_7']:
   r=[x for x in rs if x['dps']==dps and(name in x['gate']if name=='identity_7_7'else x['gate']==name)];row[name+'_max']=mp.nstr(max(mp.mpf(x['lhs'])for x in r),55);row[name+'_pass']=all(x['pass_gate']for x in r)
  row['all_registered_gates_pass']=all(x['pass_gate']for x in rs if x['dps']==dps);out.append(row)
 with(P/'GATE_SUMMARY.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=list(out[0]));w.writeheader();w.writerows(out)
 a=json.loads((P/'ADDRESS_MATCHES.json').read_text());pred=dict(C1=dict(probability=.95,pass_gate=g['status']=='PASS_DIAG_NOT_INTERVAL'),C2=dict(probability=.90,pass_gate=all(r['max_deviation_less_0_001']for r in g['max_ratio_deviations']if r['epsilon']=='0.0001')),C3=dict(probability=.95,pass_gate=g['all_mathematical_comparisons_pass']),C4=dict(probability=.85,pass_gate=a['C4_addresses_with_hit_at_m2000']>=3,observed=a['C4_addresses_with_hit_at_m2000']))
 (P/'PREDICTION_SCORES.json').write_text(json.dumps(pred,indent=2)+'\n');print(out)
if __name__=='__main__':main()
