from diagnostics import *
mp.mp.dps=40
from functools import lru_cache
targets=lru_cache(None)(targets)
src=json.loads((P.parents[1]/'fake_worlds_2026-11-02/dh_zeros.json').read_text());zz=src['off_line_pairs'][0];center=complex(float(zz['gamma']),float(zz['sigma_right'])-.5)
rows=[]
for m in [20,40,60,80,120,160,200,240]:
 d=json.loads((P/f'profile_dh_m{m}.json').read_text());a=np.array(targets('dh',.25j))
 for j in [0,8]:
  th=2*np.pi*j/16;g=a/W(d,.25j,th)
  for radius in [.1,.03,.01,.001,.0001,.00001]:
   zs=[center+radius*np.exp(2j*np.pi*k/8) for k in range(8)];ts=np.array([targets('dh',z) for z in zs]);ww=W(d,np.array(zs),th)
   for v in range(2):
    er=np.abs(g[v]*ww-ts[:,v])/np.abs(ts[:,v]);rows.append(dict(m=m,theta_index=j,target=['v1','v3'][v],radius=radius,max_relative_error=float(max(er)),mean_relative_error=float(np.mean(er)),radius_times_max=float(radius*max(er)),W_at_center_abs=float(abs(W(d,center,th))),target_at_center_abs=float(abs(targets('dh',center)[v]))))
with (P/'dh_circle.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
(P/'dh_circle_notes.json').write_text(json.dumps({'center':{'real':center.real,'imag':center.imag},'status':'finite float W, 40dps target evaluations at float coordinates; center zero residual limited by coordinate rounding','gauge':'constant anchor i/4; theta0 andpi; not an optimized arbitrary analytic gauge'},indent=2))
