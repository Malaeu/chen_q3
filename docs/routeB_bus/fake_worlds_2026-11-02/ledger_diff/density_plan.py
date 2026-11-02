"""Exact-count cutoff planning from saved ordinates; no eigenproblems."""
from pathlib import Path
import csv,json
import mpmath as mp
P=Path(__file__).resolve().parent;B=P.parent.parent
mp.mp.dps=100
zs=[mp.mpf(r['gamma']) for r in csv.DictReader((B/'capacity_matrix_2026-11-02/zeros.csv').open())]
d=json.loads((P.parent/'dh_zeros.json').read_text())
dh=sorted([mp.mpf(x['gamma']) for x in d['critical_line_zeros']]+[mp.mpf(x['gamma']) for x in d['off_line_pairs'] for _ in range(2)])
out=[]
for m in [20,40,55,60,80,120]:
 L=mp.log(m);omega=2*mp.pi*m/L;T=mp.mpf('1.1')*omega;q=sum(g<T for g in zs);lo=dh[q-1];hi=dh[q]
 rr={'m':m,'q_zeta':q,'density_zeta':mp.nstr(mp.mpf(q)/(m+1),90),'T_zeta':mp.nstr(T,90),'exact_DH_threshold_exists':lo<hi,'DH_options':[]}
 qs=[q] if lo<hi else [sum(g<lo for g in dh),sum(g<=lo for g in dh)]
 for qq in qs:
  t=(dh[qq-1]+dh[qq])/2
  rr['DH_options'].append({'q':qq,'density':mp.nstr(mp.mpf(qq)/(m+1),90),'T_midpoint':mp.nstr(t,90),'kappa_DH':mp.nstr(t/omega,90),'last_included_height':mp.nstr(dh[qq-1],90),'first_excluded_height':mp.nstr(dh[qq],90)})
 out.append(rr)
(P/'density_plan.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items() if k in ['m','q_zeta','exact_DH_threshold_exists']} for x in out]))
