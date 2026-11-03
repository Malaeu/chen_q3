"""Explicit double2 REFERENCE zeta spectral face; no matching fake zeros."""
from pathlib import Path
import json,csv
import numpy as np,scipy.linalg as la
from binary import BASE,P,make_knobs
r=[]
for m in[16,24,40,80,120,200,248,300]:
 z=np.load(BASE/'source'/f'zeta_m{m}.npz');e,V=la.eigh(z['A1']);meta=json.loads((P/'binary_cells'/f'zeta_m{m}.json').read_text());F=V[:,:meta['face_size']];d=np.load(BASE/'source'/f'double2_m{m}.npz');labels,K=make_knobs(m,d['C'],d['B'],'double2');M=[F.T@x@F for x in K];H=F.T@d['A1']@F;scale=max(la.norm(x,2)for x in M);ratio=la.norm(H,2)/scale;r.append(dict(world='double2',m=m,reference='REFERENCE_SPECTRAL_FACE_ZETA',dimension=F.shape[1],compressed_minimum=float(la.eigvalsh(H)[0]),relative_near_null=float(ratio),gate=ratio<=1e-8,P2_P3_status='STOPPED_FACE_GATE'if ratio>1e-8 else'REQUIRES_SEPARATE_PRICE_RUN'))
assert all(not x['gate']for x in r)
with(P/'REFERENCE_FACE_CONTROLS.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=r[0]);w.writeheader();w.writerows(r)
print('Double2 reference spectral face fails near-null gate on8/8')
