"""Join fixed-head smooth derivatives, replay controls and h-refinement anchors."""
from pathlib import Path
import json,csv,mpmath as mp
mp.mp.dps=100
P=Path(__file__).resolve().parent
rows=[];replay=[];chain=[];refine=[]
for p in sorted(P.glob('smooth_*_bits1024_h1e-30.json')):
 d=json.loads(p.read_text()); k=json.loads((P.parent/'kernels'/f"{d['world']}_m{d['m']}_bits1024.json").read_text()); km={(r['gauge'],r['eta']):r for r in k['rows']}
 anchor=P/p.name.replace('h1e-30','h1e-35.json').replace('.json.json','.json')
 a=json.loads(anchor.read_text()) if anchor.exists() else None
 for j,r in enumerate(d['rows']):
  t=km[r['gauge'],r['eta']]; q=dict(r)
  for key in ['K','endpoint_cross']:
   err=abs(mp.mpf(r[key])-mp.mpf(t[key]))/max(abs(mp.mpf(t[key])),mp.mpf('1e-1000'))
   q[key+'_base_replay_relative']=mp.nstr(err,30);replay.append(err)
  err=abs(mp.mpf(r['radius_chain_rule_fd_error']))/max(abs(mp.mpf(r['smooth_left_dotr_proxy_tau'])),mp.mpf('1e-1000'));chain.append(err);q['radius_chain_rule_relative']=mp.nstr(err,30)
  if a:
   for key in ['smooth_left_dotK_tau','smooth_left_dotr_proxy_tau']:
    val=mp.mpf(a['rows'][j][key]);err=abs(val-mp.mpf(r[key]))/max(abs(val),mp.mpf('1e-1000'));refine.append(dict(world=d['world'],m=d['m'],gauge=r['gauge'],eta=r['eta'],quantity=key,relative_difference=mp.nstr(err,30)))
  rows.append(q)
with (P/'smooth_parts.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
pp={int(r['m']) for r in csv.DictReader((P/'prime_powers.csv').open())}
with (P/'prime_power_smooth_decomposition.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(r for r in rows if r['m'] in pp)
s=dict(status='DIAGNOSTIC_NEVER_A_PROOF',cells=len(rows)//6,rows=len(rows),prime_power_sizes=len(pp),prime_power_rows=sum(r['m'] in pp for r in rows),worlds=['zeta','dh'],max_base_replay_relative=mp.nstr(max(replay),30),max_radius_chain_rule_relative=mp.nstr(max(chain),30),h_refinement_anchors=refine,max_h_refinement_relative=mp.nstr(max([mp.mpf(r['relative_difference']) for r in refine],default=mp.mpf(0)),30),scope='Fixed N=m, same actual active zero nodes, smooth left continuation excludes birth n=m; right derivative equals left plus exact rank-one atom. Numerical finite differences, no interval error enclosure; formal inverse forms only, no Weyl identification.')
(P/'smooth_summary.json').write_text(json.dumps(s,indent=2)+'\n');print(json.dumps({k:v for k,v in s.items() if k!='h_refinement_anchors'},indent=2))
