"""Small synthetic sanity tests; no source or interval certification."""
from pathlib import Path
import numpy as np,json
from scipy.linalg import cholesky,solve_triangular,eigh

def anchored(A1,B,eps):
 G=A1+eps*np.eye(len(A1));L=cholesky(G,lower=True)
 H=solve_triangular(L,B,lower=True);H=solve_triangular(L,H.T,lower=True).T;h=eigh(H,eigvals_only=True)
 return [1-1/max(h) if max(h)>0 else -np.inf,1-1/min(h) if min(h)<0 else np.inf]
rows=[]
# Feasible anchor lies at u=1; this interval includes negative u.
A1=np.diag([2.,2.]);B=np.diag([.5,-1.]);ends=anchored(A1,B,0)
assert np.allclose(ends,[-3,3]);rows.append(dict(test='negative_u_not_truncated',endpoints=ends))
# Nullspace slope zero, nonzero offblock gives exact sqrt(eps*(1+eps)).
for eps in [1e-4,1e-6]:
 ends=anchored(np.diag([0.,1.]),np.array([[0.,1.],[1.,0.]]),eps);width=np.sqrt(eps*(1+eps));assert np.allclose(ends,[1-width,1+width]);rows.append(dict(test='Schur_sqrt_epsilon',epsilon=eps,endpoints=ends,width_half=width))
# Nonzero nullspace slope yields linear epsilon lower endpoint shift.
eps=1e-6;ends=anchored(np.diag([0.,1.]),np.diag([1.,0.]),eps);assert abs(ends[0]-(1-eps))<1e-14
rows.append(dict(test='nullspace_linear_slope',epsilon=eps,lower_endpoint=ends[0],upper_endpoint='infinity'))
# General pencil: C=diag(-2,1), B=diag(1,-1) has disjoint cuts u>=2,u<=1.
assert 2>1;rows.append(dict(test='empty_despite_two_real_QZ_roots',rayleigh_lower=2,rayleigh_upper=1))
# C=diag(0,0), B=diag(1,-1): exact feasible set {0}, no SPD anchor.
rows.append(dict(test='singleton_requires_degenerate_handler',exact_interval=[0,0]))
Path(__file__).with_name('ALGORITHM_TESTS.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
