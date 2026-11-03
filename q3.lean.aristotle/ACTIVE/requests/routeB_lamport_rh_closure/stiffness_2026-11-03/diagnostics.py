"""Bounded float candidates; all residuals explicit, no exact SDP certificate."""
import numpy as np,scipy.linalg as la

def tangent(M,tol=1e-8):
 M=np.array(M,float);k,r,_=M.shape;V=la.null_space(np.ones((1,k)));scale=max(la.norm(x,2)for x in M);scale=max(scale,1e-300);N=M/scale
 if r==1:
  p=M[:,0,0];v=V@(V.T@p);val=la.norm(v);t=v/val if val else np.zeros(k)
  return dict(method='EXACT_SCALAR_FLOAT_FORMULA',primal_value=float(val),primal_minimum=float(p@t),t=t.tolist(),dual_Y=[[1.]],dual_anisotropy=1.,dual_price_residual=float(la.norm(V.T@p)),dual_valid=False if val>tol*scale else None,scale=scale,status='SOFT_DIRECTION'if val>tol*scale else'UNRESOLVED')
 import cvxpy as cp
 x=cp.Variable(k-1);v=cp.Variable();t=V@x;S=sum(t[i]*N[i]for i in range(k));pr=cp.Problem(cp.Maximize(v),[S-v*np.eye(r)>>0,cp.norm(x)<=1])
 try:
  pr.solve(solver='SCS',eps=1e-7,max_iters=6000,verbose=False);tv=np.zeros(k)if x.value is None else V@x.value;tv=tv/max(1,la.norm(tv));image=sum(tv[i]*M[i]for i in range(k));actual=float(la.eigvalsh(image)[0]);pstatus=pr.status
 except Exception as e:tv=np.zeros(k);actual=0.;pstatus=type(e).__name__
 Y=cp.Variable((r,r),symmetric=True);eta=cp.Variable();prices=cp.hstack([cp.trace(Y@N[i])for i in range(k)]);du=cp.Problem(cp.Maximize(eta),[Y-eta*np.eye(r)>>0,cp.trace(Y)==1,V.T@prices==0])
 try:
  du.solve(solver='SCS',eps=1e-7,max_iters=6000,verbose=False);yy=np.zeros((r,r))if Y.value is None else(Y.value+Y.value.T)/2;ye=la.eigvalsh(yy);res=la.norm(V.T@np.array([np.sum(yy*a)for a in M]));ratio=float(ye[0]/ye[-1])if ye[-1]>0 else 0.;dstatus=du.status
 except Exception as e:yy=np.zeros((r,r));res=float('inf');ratio=0.;dstatus=type(e).__name__
 # PSD-project dual candidate for a valid finite-matrix upper envelope.
 ye,Z=la.eigh(yy);yp=(Z*np.maximum(ye,0))@Z.T
 if np.trace(yp)>0:yp/=np.trace(yp)
 upper=float(la.norm(V.T@np.array([np.sum(yp*a)for a in M])))if np.trace(yp)>0 else None
 return dict(method='SCS_CANDIDATES_NOT_CERTIFICATES',primal_value=max(0.,actual),primal_zero_feasible_lower_bound=0.,dual_upper_envelope=upper,primal_budget_norm=float(la.norm(tv)),primal_gauge_residual=float(abs(sum(tv))),primal_minimum=actual,t=tv.tolist(),primal_solver_status=pstatus,dual_Y=yy.tolist(),dual_anisotropy=ratio,dual_price_residual=float(res),dual_solver_status=dstatus,scale=scale,status='SOFT_DIRECTION_NUMERIC'if actual>tol*scale else'UNRESOLVED',dual_valid=None)
