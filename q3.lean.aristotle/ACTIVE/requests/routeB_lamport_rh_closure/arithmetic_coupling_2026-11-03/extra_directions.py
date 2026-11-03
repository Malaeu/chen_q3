"""Selected-direction and quiet-compression diagnostics at the same ε."""
from pathlib import Path
import json,csv,numpy as np
import solve
P=Path(__file__).resolve().parent;out=[]
for m in [16,24,40,80,120,200,248,300]:
 z,C,B=solve.source(m,'zeta');A=C+B;eps=100*solve.common_floor(m);Q=np.load(P/'quiet/frames'/f'zeta_m{m}.npz')['Q'];Cq=Q.T@C@Q;Bq=Q.T@B@Q
 full=json.loads((P/'cells'/f'zeta_m{m}_f100.json').read_text())['summary'];quiet=solve.anchored(Cq,Bq,eps,1)
 a=dict(m=m,epsilon=eps,quiet_lower_minus1=quiet[0]['offset_from_one'],quiet_upper_minus1=quiet[1]['offset_from_one'],full_lower_minus1=full['u_lower_minus_one'],full_upper_minus1=full['u_upper_minus_one'],lower_quiet_full_difference=quiet[0]['offset_from_one']-full['u_lower_minus_one'],upper_quiet_full_difference=quiet[1]['offset_from_one']-full['u_upper_minus_one'])
 atom=z['atom2'];ends=solve.anchored(A-atom,atom,eps,1)
 for e in ends:
  a['atom2_'+e['side']+'_minus1']=e['offset_from_one'];a['atom2_'+e['side']+'_quiet_mass']=float(np.linalg.norm(Q.T@np.array(e['carrier_vector']))**2)
 a['doubled_atom2_factor2_is_inside']=ends[0]['u']<=2<=ends[1]['u'];out.append(a)
with(P/'EXTRA_DIRECTIONS.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=list(out[0]));w.writeheader();w.writerows(out)
print(out)
