import json,csv
from pathlib import Path
import mpmath as mp
mp.mp.dps=160
D=Path(__file__).resolve().parent
b=json.loads((D/'base_dps100_gl96.json').read_text());b2=json.loads((D/'base_dps140_gl128.json').read_text());a=json.loads((D/'fd_dps100_gl96.json').read_text());a2=json.loads((D/'fd_dps140_gl128.json').read_text())
checks={}
for k in ('lambda0','D_reg','L_lambda_prime_HF_left','L_lambda_prime_HF_right','abs_e_Dh','residual_norm2'):
 checks[k]=mp.nstr(abs(mp.mpf(b[k])/mp.mpf(b2[k])-1),40)
for r,s in zip(a,a2):
 for k in ('P_tau','Dreg_plus_Ptau','lambda_tau_FD_fourth_order','frozen_energy_FD','E_tau_measured'):
  checks[r['side']+'_'+k]=mp.nstr(abs(mp.mpf(r[k])/mp.mpf(s[k])-1),40)
rows=[]
for r in a:
 row={**{k:b[k] for k in('N','L','lambda0','D_reg','abs_e_Dh','residual_norm2')},**r};rows.append(row)
with (D/'pohozaev_results.csv').open('w') as f:
 cw=csv.DictWriter(f,fieldnames=list(rows[0]));cw.writeheader();cw.writerows(rows)
(D/'pohozaev_results.json').write_text(json.dumps(dict(base=b,finite_differences=a,validation_relative_errors=checks),indent=2)+'\n')
(D/'validation.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks,indent=2))
for r in rows:
 print(r['side'])
 for k in('P_tau','Dreg_plus_Ptau','L_lambda_prime_HF','lambda_tau_FD_first_order','lambda_tau_FD_fourth_order','relative_FD4_HF_error','frozen_energy_FD','E_tau_measured','E_tau_over_tau'):
  print(k,mp.nstr(mp.mpf(r[k]),18))
