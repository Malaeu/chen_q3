from margins import *
rows=[]
for mesh in [32,64,128,256]:
 saved=json.loads((CORE/f'zeta_mesh{mesh}_dps100.json').read_text());rr=np.array(saved['r_values'],float);g=float_source('zeta')
 for q in [64,128]:
  r,_=block(g,rr,6*mesh,1/mesh,1/mesh,q);rows.append(dict(world='zeta',mesh=mesh,a=6.,delta=1/mesh,q=q,**r));print(mesh,q,r['mu'],flush=True)
write('extended_refinement.csv',rows)
