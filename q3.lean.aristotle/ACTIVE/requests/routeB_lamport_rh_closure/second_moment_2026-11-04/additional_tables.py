from pathlib import Path
import csv,json,math
from measure import P,BASE,counts,write
rows=list(csv.DictReader((P/'SUMMARY.csv').open()));sharp={int(x['m']):x for x in csv.DictReader((P/'sigma_sharp.csv').open())};ss=[];cc=[]
for r in rows:
 if r['sigma_convention']!='L_plus_inv_gamma':continue
 w=r['world'];m=int(r['m']);T=float(r['T']);N,line,nd,h=counts(w,T);cc.append({k:r[k]for k in['world','m','cutoff','kappa','T','N_upper_with_multiplicity','N_on_line_simple','N_distinct_complex','N_distinct_heights','census_simple_on_line_fraction','census_distinct_fraction','lambda_eff']})
 if w!='zeta':continue
 sig=float(sharp[m]['sigma_sharp']);v=float(r['Frob2'])/(sig*sig*N);ss.append(dict(world=w,m=m,cutoff=r['cutoff'],sigma_sharp=sig,sigma_original=r['sigma'],v_sharp=v,v_original=r['v'],raw_simple=2-v,raw_distinct=(3-v)/2,sanity_violation=2-v>1+1e-10 or(3-v)/2>1+1e-10,scope='conditional diagnostic gamma_star height cap; no finite rank-trace/tail certificate'))
write('CENSUS_COUNTS.csv',cc);write('SHARP_SIGMA_RESULTS.csv',ss)
G=BASE.parent/'ground_state_zeros_2026-11-03';ground={(r['world'],int(r['m'])):r for r in csv.DictReader((G/'ZERO_SUMMARY.csv').open())if r['parity']=='even'};gates=[]
for r in cc:
 if r['cutoff']!='primary':continue
 old=ground[r['world'],int(r['m'])];ok=int(r['N_upper_with_multiplicity'])==int(old['source_count']);assert ok;gates.append(dict(world=r['world'],m=r['m'],N_computed=r['N_upper_with_multiplicity'],ground_state_source_count=old['source_count'],pass_gate=ok))
assert len(gates)==855;write('PRIMARY_CENSUS_GATE.csv',gates);print('855primary census gates pass;570optional sharp rows')
