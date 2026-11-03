import os,sys,json
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,scipy.linalg as la
P=Path(__file__).resolve().parent;BASE=Path(os.environ.get('STIFFNESS_BASE','/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03'));sys.path.insert(0,str(BASE/'quiet'));import build
rows=[]
for m in [16,24,40,80,120,200,248,300]:
 for world in ['zeta','dh']:
  g=build.g;g.get_context().precision=768;L=g.log(m);ev=[x for x in build.events(world)if x[0]<2*g.const_pi()*m/L];E=np.array(build.rows(m,ev,L),float);z=np.load(BASE/'quiet/frames'/f'{world}_m{m}.npz');Q=z['Q'];U=z['U'];res=float(la.norm(E@Q,2)/la.norm(E,2));rows.append(dict(world=world,m=m,q=len(E),quiet_dimension=Q.shape[1],normalized_constraint_residual=res));assert res<1e-12
(P/'FRAME_REPLAY_CHECK.json').write_text(json.dumps(rows,indent=2)+'\n');print('16regenerated frames independent constraint check; max',max(x['normalized_constraint_residual']for x in rows))
