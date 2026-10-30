"""Finite floating diagnostic only: literal CCM two-resolvent competitors."""
import json
from pathlib import Path
import noescape_resistance_probe as p
mp=p.mp
mp.mp.dps=80
records=[]
for m in [4,8,16]:
 K=p.full_probe.matrix_K(m);E,_=p.parity_bases(m);A=E.T*K*E
 vals,C=mp.eigsy(A);xs=[mp.mpf(i*i) for i in range(m+1)]
 zs=[-mp.mpf(m*m)*q for q in [mp.mpf('.001'),mp.mpf('.01'),mp.mpf('.1'),1,10,100]]
 zs += [mp.mpf(m*m)*(1+q) for q in [mp.mpf('.001'),mp.mpf('.01'),mp.mpf('.1'),1,10,100]]
 zs += [(xs[i]+xs[i+1])/2 for i in range(m)]
 for col in [0,1]:
  c=C[:,col];B=A-vals[col]*mp.eye(m+1)
  ys=[mp.matrix([c[i]/(x-z) for i,x in enumerate(xs)]) for z in zs]
  ys=[y/mp.norm(y) for y in ys];bys=[B*y for y in ys]
  best=None
  for j in range(len(zs)):
   for k in range(j+1,len(zs)):
    aa=mp.fdot(ys[j],bys[j]);bb=mp.fdot(ys[k],bys[k]);ab=mp.fdot(ys[j],bys[k])
    G=mp.matrix([[aa,ab],[ab,bb]]);ev,evec=mp.eigsy(G)
    y=evec[0,0]*ys[j]+evec[1,0]*ys[k]
    q=mp.fdot(y,B*y)/mp.fdot(y,y)
    if best is None or q<best[0]:best=(q,zs[j],zs[k],aa*bb-ab*ab)
  records.append(dict(m=m, eigen_index=col, shift=mp.nstr(best[0],40), shifts=[mp.nstr(x,40) for x in best[1:3]], determinant=mp.nstr(best[3],40), gap=mp.nstr(vals[1]-vals[0],40), residual=mp.nstr(mp.norm(B*c),15)))

result=dict(status="FINITE_FLOATING_DIAGNOSTIC_NOT_PROOF",dps=80,records=records)
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
