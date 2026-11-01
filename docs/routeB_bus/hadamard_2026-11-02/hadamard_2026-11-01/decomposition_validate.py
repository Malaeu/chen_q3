import json,sys
import mpmath as mp
import decomposition as d
p=d.p
mp.mp.dps=100
gn,gw=mp.gauss_quadrature(80,'legendre')
p.nodes=[((mp.mpf(panel)+(z+1)/2)/8,w/16) for panel in range(8) for z,w in zip(gn,gw)]
p.trig={n:[(mp.sin(2*mp.pi*n*y),mp.cos(2*mp.pi*n*y)) for y,w in p.nodes] for n in range(21)}
p.atoms=[(k,mp.log(k),p.mang(k)/mp.sqrt(k)) for k in range(2,21) if p.mang(k)]
p.matrices.cache_clear()
out={'dps':100,'quadrature_order':80,'edges':[],'five_terms':[]}
for m in (4,12,20):
 rr=d.edge(m);out['edges'].append(rr);print('EDGE',m,flush=True)
for k in(8,12,16):
 for N in(8,12):
  rr=d.five(mp.log(k),N,'right',k);out['five_terms'].append(rr);print('FIVE',k,N,flush=True)
(d.OUT/'decomposition_validation_dps100_gl80.json').write_text(json.dumps(out,indent=2)+'\n')
