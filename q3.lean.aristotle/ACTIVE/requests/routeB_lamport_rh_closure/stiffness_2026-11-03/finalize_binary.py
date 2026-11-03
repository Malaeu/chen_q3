"""Normalize stored candidates and retain complete numeric audit with denseYlocal."""
from pathlib import Path
import numpy as np,scipy.linalg as la,json,csv
from binary import BASE,P,make_knobs
for f in(P/'binary_cells').glob('*.json'):
 d=json.loads(f.read_text())
 if 'P3'in d:
  z=np.load(BASE/'source'/f'{d["world"]}_m{d["m"]}.npz');labels,K=make_knobs(d['m'],z['C'],z['B'],d['world']);E,U=la.eigh(z['A1']);F=U[:,:d['face_size']];M=np.array([F.T@x@F for x in K]);k=len(M);V=la.null_space(np.ones((1,k)));p=d['P3'];t=np.array(p['t']);t=t/max(1,la.norm(t));image=sum(a*x for a,x in zip(t,M));v=float(la.eigvalsh(image)[0]);yy=np.array(p['dual_Y']);e,Z=la.eigh(yy);yp=(Z*np.maximum(e,0))@Z.T
  if np.trace(yp)>0:yp/=np.trace(yp)
  upper=float(la.norm(V.T@np.array([np.sum(yp*a)for a in M])))if np.trace(yp)>0 else None;p.update(primal_value=max(0.,v),primal_minimum=v,primal_zero_feasible_lower_bound=0.,primal_budget_norm=float(la.norm(t)),primal_gauge_residual=float(abs(sum(t))),t=t.tolist(),dual_upper_envelope=upper,dual_projected_minimum=float(la.eigvalsh(yp)[0]),dual_projected_price_vector=[float(np.sum(yp*a))for a in M],solver_scope='FLOAT_CANDIDATES_AND_RESIDUALS_NOT_CERTIFIED_OPTIMUM_OR_STRICTNESS')
  d['P3']=p
  ix=np.triu_indices(d['face_size']);vec=M[:,ix[0],ix[1]].T;vec[ix[0]!=ix[1]]*=np.sqrt(2);_,ss,vh=la.svd(vec,full_matrices=True);tt=max(d['rho'],1e-8*ss[0]);rank=int(sum(ss>tt));d['P2']['face_tolerance_threshold']=tt;d['P2']['face_tolerance_kernel_dimension']=len(M)-rank;d['P2']['face_tolerance_kernel_basis']=vh[rank:].tolist()
 f.write_text(json.dumps(d,indent=2)+'\n')
print('Normalized24cell candidates, finite upper envelopes retained')
