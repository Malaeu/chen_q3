"""Affine PSD interval in one scalar; finite numerical diagnostics, all real u."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,scipy.linalg as la,json,time,argparse,hashlib
P=Path(__file__).resolve().parent
def smallest(M):
 e,v=la.eigh((M+M.T)/2,subset_by_index=[0,0]);return float(e[0]),v[:,0]
def source(m,world):
 z=np.load(P/'source'/f'{world}_m{m}.npz');return z,z['C'],z['B']
def common_floor(m):
 norms=[]
 for w in ['zeta','double2','dh']:
  z=np.load(P/'source'/f'{w}_m{m}.npz');norms.append(max(abs(z['C_eigenvalues']))+max(abs(z['B_eigenvalues'])))
 return 1000*np.finfo(float).eps*(m+1)*max(1,*norms)
def feasible_anchor(C,B,eps,rho):
 n=len(C);I=np.eye(n);cuts=[];vectors=[];history=[]
 def cut(v,tag):
  v=v/la.norm(v);a=float(v@C@v)+eps;b=float(v@B@v);cuts.append(dict(a=a,b=b,tag=tag));vectors.append(v)
 def floor(u):return rho*max(1,abs(u))
 lam,v=smallest(C+B+eps*I);history.append(dict(u=1.,minimum=lam))
 if lam>8*floor(1):return dict(status='SPD_ANCHOR',anchor=1.,minimum=lam,history=history)
 cut(v,'u1_minimum')
 e,V=la.eigh(B);cut(V[:,0],'B_minimum');cut(V[:,-1],'B_maximum');bscale=max(1,max(abs(e)));btol=128*np.finfo(float).eps*bscale
 if e[0]>=-btol or e[-1]<=btol:return dict(status='UNRESOLVED_RECESSION',history=history)
 for it in range(80):
  lowers=[(-c['a']/c['b'],i)for i,c in enumerate(cuts)if c['b']>btol];uppers=[(-c['a']/c['b'],i)for i,c in enumerate(cuts)if c['b']<-btol]
  if not lowers or not uppers:return dict(status='UNRESOLVED_RECESSION',history=history)
  lo,il=max(lowers);hi,ih=min(uppers)
  if lo>hi:
   a,b=cuts[il],cuts[ih];wl=-b['b']/(a['b']-b['b']);wh=1-wl;dual=wl*a['a']+wh*b['a'];slope=wl*a['b']+wh*b['b'];guard=16*rho*max(1,abs(lo),abs(hi))
   return dict(status='EMPTY_NUMERIC'if dual < -guard else'UNRESOLVED_EMPTY_MARGIN',outer_lower=lo,outer_upper=hi,dual_constant=dual,dual_slope=slope,dual_guard=guard,weight_lower=wl,weight_upper=wh,lower_vector=vectors[il].tolist(),upper_vector=vectors[ih].tolist(),lower_cut=a,upper_cut=b,history=history)
  u=(lo+hi)/2;lam,v=smallest(C+u*B+eps*I);history.append(dict(u=u,minimum=lam,outer_lower=lo,outer_upper=hi))
  if lam>8*floor(u):return dict(status='SPD_ANCHOR',anchor=u,minimum=lam,history=history)
  if lam>=-8*floor(u):return dict(status='UNRESOLVED_TANGENCY',candidate=u,minimum=lam,outer_lower=lo,outer_upper=hi,history=history)
  cut(v,'minimum_at_trial')
 return dict(status='UNRESOLVED_ITERATION_LIMIT',history=history)
def anchored(C,B,eps,anchor):
 G=C+anchor*B+eps*np.eye(len(C));L=la.cholesky((G+G.T)/2,lower=True)
 H=la.solve_triangular(L,B,lower=True);H=la.solve_triangular(L,H.T,lower=True).T;H=(H+H.T)/2
 e,V=la.eigh(H);out=[]
 for side,k in [('lower',len(e)-1),('upper',0)]:
  h=float(e[k]);finite=h>0 if side=='lower'else h<0
  if not finite:out.append(dict(side=side,status='UNBOUNDED',u=None,offset_from_one=None));continue
  t=-1/h;u=anchor+t;x=la.solve_triangular(L.T,V[:,k],lower=False);x/=la.norm(x)
  if x[np.argmax(abs(x))]<0:x=-x
  slope=float(x@B@x);alpha=float(x@C@x);M=C+u*B+eps*np.eye(len(C));err=float(la.norm(M@x));step=max(abs(t)*.2,128*np.finfo(float).eps*max(1,abs(u)));outside=u-step if side=='lower'else u+step
  out.append(dict(side=side,status='FINITE',u=u,offset_from_one=(anchor-1)+t,generalized_eigenvalue=h,arithmetic_slope=slope,gamma_pole_energy=alpha,baseline_A1_energy=alpha+slope,endpoint_rayleigh=alpha+u*slope,endpoint_shifted_residual=err,du_depsilon=-1/slope,inside_minimum=smallest(C+(anchor+u)/2*B+eps*np.eye(len(C)))[0],outside_rayleigh=float(alpha+outside*slope+eps),outside_step=step,carrier_vector=x.tolist()))
 return out
def run(task):
 m,world,factor=task;start=time.monotonic();z,C,B=source(m,world);rho=common_floor(m);eps=factor*rho;fr=np.load(P/'quiet/frames'/f'{"dh"if world=="dh"else"zeta"}_m{m}.npz');Q=fr['Q'];A=C+B;D=Q.T@A@Q;de,dv=la.eigh((D+D.T)/2);qguard=1000*np.finfo(float).eps*(m+1)*max(1,max(abs(z['eigenvalues'])));near=abs(de)<=qguard
 r=feasible_anchor(C,B,eps,rho);summary=dict(world=world,m=m,epsilon=eps,epsilon_factor=factor,precision_floor=rho,status=r['status'],quiet_dimension=Q.shape[1],quiet_reference='REFERENCE_J_zeta_NOT_MATCHED_ZEROS'if world=='double2'else'OWN_J_kappa1',quiet_lambda_min=float(de[0]),quiet_lambda_min_status='UNRESOLVED_AT_FLOAT_FLOOR'if abs(de[0])<=qguard else'RESOLVED_NUMERIC',quiet_numeric_guard=qguard,quiet_zero_cluster_dimension=int(sum(near)),A1_minimum=float(z['eigenvalues'][0]),anchor=r.get('anchor'),u_lower=None,u_upper=None,u_lower_minus_one=None,u_upper_minus_one=None)
 if r['status']=='SPD_ANCHOR':
  ends=anchored(C,B,eps,r['anchor']);r['endpoints']=ends;summary['status']='NONEMPTY_NUMERIC'
  for e in ends:
   side=e['side'];summary['u_'+side]=e['u'];summary['u_'+side+'_minus_one']=e['offset_from_one']
   if e['status']!='FINITE':continue
   x=np.array(e['carrier_vector']);v=Q.T@x;mass=float(v@v);ov=dv.T@v;k=int(np.argmax(ov*ov));cluster=float(sum(ov[near]**2));e.update(quiet_mass=mass,quiet_membership='APPROX_QUIET'if mass>=.99 else'MIXED',quiet_top_overlap_index=k,quiet_top_overlap_eigenvalue=float(de[k]),quiet_top_overlap_mass=float(ov[k]**2),quiet_top_overlap_status='UNRESOLVED_QUIET_CLUSTER'if near[k]else'RESOLVED_QUIET_MODE',quiet_zero_cluster_mass=cluster,quiet_projected_rayleigh=float(v@D@v/mass)if mass else None)
   for key in ['quiet_mass','quiet_membership','quiet_zero_cluster_mass','arithmetic_slope','endpoint_shifted_residual','inside_minimum','outside_rayleigh']:summary[side+'_'+key]=e[key]
 elif r['status']=='EMPTY_NUMERIC':
  _,v=smallest(A);summary['baseline_negative_witness_quiet_mass']=float(la.norm(Q.T@v)**2);r['baseline_negative_witness']=v.tolist();summary.update(dual_constant=r['dual_constant'],dual_slope=r['dual_slope'],dual_guard=r['dual_guard'],incompatible_u_lower=r['outer_lower'],incompatible_u_upper=r['outer_upper'])
 summary['seconds']=time.monotonic()-start;summary['source_npz_sha256']=hashlib.sha256((P/'source'/f'{world}_m{m}.npz').read_bytes()).hexdigest();summary['pencil_error_rule']='e_C+abs(u)*e_B; rho*max(1,abs(u)) used as conservative heuristic scale, not enclosure'
 out=P/'cells';out.mkdir(exist_ok=True);name=f'{world}_m{m}_f{factor:g}.json';(out/name).write_text(json.dumps(dict(summary=summary,solver=r),indent=2)+'\n');print(world,m,factor,summary['status'],summary['u_lower_minus_one'],summary['u_upper_minus_one'],'seconds',round(summary['seconds'],2),flush=True);return summary
if __name__=='__main__':
 from concurrent.futures import ProcessPoolExecutor
 p=argparse.ArgumentParser();p.add_argument('--m',nargs='+',type=int,default=list(range(16,301)));p.add_argument('--world',nargs='+',default=['zeta','double2','dh']);p.add_argument('--factor',nargs='+',type=float,default=[100]);p.add_argument('--workers',type=int,default=2);p.add_argument('--skip-existing',action='store_true');a=p.parse_args();tasks=[(m,w,f)for m in a.m for w in a.world for f in a.factor if not(a.skip_existing and(P/'cells'/f'{w}_m{m}_f{f:g}.json').exists())]
 with ProcessPoolExecutor(a.workers)as pool:list(pool.map(run,tasks))
