"""Literal-carrier conditioning and guarded threshold Schur diagnostics."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from core import *
import numpy as np
import scipy.linalg as la
import argparse,hashlib
MATRICES=P/'matrices';CELLS=P/'cells';CELLS.mkdir(exist_ok=True)
CUTS=[('c_quarter','0.25'),('c_half','0.5'),('kappa_one','0')]

def fmt(x):return mp.nstr(x,65) if isinstance(x,(mp.mpf,mp.mpc)) else x
def serial(x):
 if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
 if isinstance(x,list):return [serial(v) for v in x]
 if isinstance(x,(mp.mpf,mp.mpc)):return mp.nstr(x,65)
 if isinstance(x,np.generic):return x.item()
 return x

def shifted_cutoff(world,m,name,c):
 T=cutoff(m,c);ev=events(world);near=min(ev,key=lambda e:abs(mp.mpf(e['gamma'])-T));g=mp.mpf(near['gamma']);half=mp.pi/mp.log(g/(2*mp.pi));flag=abs(T-g)<half
 cases=[dict(cut=name,c=c,variant='base',T=T,edge_zero=flag,nearest_gamma=g,edge_distance=T-g,half_mean_spacing=half)]
 if flag:
  for variant,sgn in [('minus_half_mean',-1),('plus_half_mean',1)]:cases.append(dict(cut=name,c=c,variant=variant,T=T+sgn*half,edge_zero=flag,nearest_gamma=g,edge_distance=T-g,half_mean_spacing=half))
 return cases

def classify(values,tol):
 values=np.asarray(values);return int(np.sum(values < -tol)),int(np.sum(abs(values)<=tol))

def conditioning(world,m,T,E):
 """Precision branch fixed by resolvability, never by the desired gap law."""
 original=mp.mp.dps;start=time.monotonic();ef=np.array(E.tolist(),float)
 uf,sf,vf=la.svd(ef,full_matrices=False);radius=1000*np.finfo(float).eps*max(E.rows,E.cols)*max(1,float(sf[0]))
 if sf[-1]>radius*100:
  v=mp.matrix(vf[-1].tolist());v/=mp.norm(v);left=mp.matrix(uf[:,-1].tolist());left/=mp.norm(left);image=E*v;sm=abs(mp.fdot(left,image));residual=max(mp.norm(image-sm*left),mp.norm(E.T*left-sm*v))
  if residual<radius:
   return dict(sigma=sm,squared=sm*sm,left=left,iterations=0,relative_residual=residual/sm,relative_change=mp.mpf(0),seconds=time.monotonic()-start,dps=original,method='FLOAT_SVD_MP_RAYLEIGH',float_sigma_radius=radius)
 errors=[]
 if world=='dh' and m>=80 and E.rows>=E.cols:
  return dict(sigma=None,squared=None,left=None,iterations=0,relative_residual=None,relative_change=None,seconds=time.monotonic()-start,dps=original,method='UNRESOLVED_BUDGET_TALL_DH',retry_reason='Prespecified runtime kill-switch after DHm120 pilot; retain tall-E and J0 flags.')
 try:
  for precision in ([120] if world=='dh' and m>=75 else [original,120]):
   mp.mp.dps=precision
   e=E if precision==original else rows_for(world,m,T)[0]
   try:
    out=sigma_min(e,maxiter=30);out.update(dps=precision,method='MP_INVERSE_ITERATION',seconds=time.monotonic()-start);return out
   except (ArithmeticError,ValueError,ZeroDivisionError) as error:errors.append(str(error))
  # A precision-independent rate issue is handled by full SVD only in small cells.
  if min(E.rows,E.cols)<=32:
   mp.mp.dps=120;e=rows_for(world,m,T)[0];u,s,v=mp.svd(e);sm=s[len(s)-1];left=u[:,len(s)-1];right=v[len(s)-1,:].T
   return dict(sigma=sm,squared=sm*sm,left=left,iterations=0,relative_residual=mp.norm(e*right-sm*left)/sm,relative_change=mp.mpf(0),seconds=time.monotonic()-start,dps=120,method='FULL_SVD_FALLBACK',retry_reason=errors)
  return dict(sigma=None,squared=None,left=None,iterations=0,relative_residual=None,relative_change=None,seconds=time.monotonic()-start,dps=120,method='UNRESOLVED_PRECISION_OR_RATE',retry_reason=errors)
 finally:mp.mp.dps=original

def metrics(A,ae,rad,Q,U,r):
 d=len(A);norm=float(la.norm(A,2));roundoff=1000*np.finfo(float).eps*d*max(1,norm);tol=max(rad,roundoff)
 D=Q.T@A@Q;B=U.T@A@Q;G=U.T@A@U
 delta=float(la.norm(A@Q,2)) if r else 0.;compression=float(la.norm(D,2)) if r else 0.
 allshift=ae-2;count,unresolved=classify(allshift,tol)
 out=dict(delta=delta,delta_numeric_radius=tol,compressed_norm=compression,N_A2=count,N_A2_unresolved=unresolved,count_minus_r=count-r,D_min=float(la.eigvalsh(D)[0]) if r else None,D_max=float(la.eigvalsh(D)[-1]) if r else None,B_norm=float(la.norm(B,2)) if B.size else 0,G_min=float(la.eigvalsh(G)[0]),G_max=float(la.eigvalsh(G)[-1]),numeric_radius=tol,quiet_coupling_retained=True)
 if r:
  Hd=D-2*np.eye(r);de=la.eigvalsh(Hd);nd,ud=classify(de,tol);gap=float(min(abs(de)))
 else:Hd=np.empty((0,0));nd=ud=0;gap=float('inf')
 out.update(eliminated_negative_index=nd,eliminated_unresolved=ud,eliminated_gap=gap if np.isfinite(gap) else None,delta_less_than_2=delta+tol<2)
 if ud:
  out.update(S_negative_index=None,S_unresolved=None,Schur_status='UNRESOLVED_ELIMINATED_BLOCK');return out,None
 S=G-2*np.eye(G.shape[0])-(B@la.solve(Hd,B.T,assume_a='sym') if r else 0);S=(S+S.T)/2
 sr=tol*(1+(out['B_norm']/gap if r else 0))**2+roundoff
 se=la.eigvalsh(S);ns,us=classify(se,sr);pred=nd+ns-r
 out.update(S_min=float(se[0]),S_negative_index=ns,S_unresolved=us,S_numeric_radius=sr,predicted_defect=pred,Schur_status='NUMERIC_IDENTITY_PASS' if not(us or unresolved) and pred==count-r else ('UNRESOLVED_THRESHOLD_SIGN' if us or unresolved else 'MISMATCH'))
 if out['Schur_status']=='MISMATCH':raise ArithmeticError('Schur inertia mismatch')
 return out,(D,B,G,S)

def run(world,m,dps=80):
 start=time.monotonic();mp.mp.dps=dps
 casepath=CELLS/f'{world}_m{m}.json'
 npz=np.load(MATRICES/f'cell_{world}_m{m}.npz');A=npz['A'];ae=npz['eigenvalues'];rad=float(npz['numeric_radius']);d=m+1;L=mp.log(m);Om=2*mp.pi*m/L
 meta=json.loads((MATRICES/f'cell_{world}_m{m}.json').read_text())
 cases=sum([shifted_cutoff(world,m,name,c) for name,c in CUTS],[])
 for c in cases:
  E,labels,heights,metric=rows_for(world,m,c['T']);c.update(E=E,labels=labels,heights=heights,metric=metric,q=E.rows,rank=min(E.rows,d),r=max(0,d-E.rows))
 maxcase=max(cases,key=lambda c:c['q']);Emax=maxcase['E'];qneed=sorted(set(c['q'] for c in cases if c['q']<d));projections={}
 if qneed:
  Ump,basis_stats=row_basis(Emax[:max(qneed),:]);
  mp_orth=mp.norm(Ump*Ump.T-mp.eye(Ump.rows))
  for q in qneed:
   u=Ump[:q,:];uf=np.array(u.tolist(),float);frame,_=la.qr(uf.T,mode='full');r=d-q;U=frame[:,:q];Q=frame[:,q:]
   projections[q]=(Q,U,dict(MP_projector_orthogonality=mp_orth,MP_orthogonality_is_max_prefix_bound=True,projector_float_separation=1.,projector_method='MP row MGS then stable float complete QR',E_kernel_residual=float(la.norm(np.array(Emax[:q,:].tolist(),float)@Q,2)),Q_orthogonality=float(la.norm(Q.T@Q-np.eye(r),2)),U_Q=float(la.norm(U.T@Q,2))))
 else:basis_stats=dict(seconds=0,min_residual_row_norm=0)
 rows=[];sigcache={};blocks_saved=[]
 for c in cases:
  q=c['q'];r=c['r'];E=c['E'];rank=c['rank'];labels=c['labels'];heights=c['heights']
  if r:Q,U,pr=projections[q]
  else:Q=np.empty((d,0));U=np.eye(d);pr=dict(MP_projector_orthogonality=0,projector_float_separation=1,E_kernel_residual=0,Q_orthogonality=0,U_Q=0)
  met,blocks=metrics(A,ae,rad,Q,U,r)
  lr=float(ae[r]);preferred=None;mpvals=meta.get('mp_eigenvalues')
  if mpvals and len(mpvals)==d:preferred=mp.mpf(mpvals[r])
  lrstatus='CACHED_MP_VALUE' if preferred is not None else ('FLOAT_RESOLVED' if abs(lr)>met['numeric_radius'] else 'UNRESOLVED_TINY_FLOAT')
  norms=[(heights[i+1]-heights[i])*L/(2*mp.pi) for i in range(len(heights)-1)];imin=min(range(len(norms)),key=lambda i:norms[i]) if norms else None
  eventall=events(world);above=next((mp.mpf(e['gamma']) for e in eventall if mp.mpf(e['gamma'])>=c['T']),None);look=(above-heights[-1])*L/(2*mp.pi) if above is not None and heights else None
  row={k:v for k,v in c.items() if k not in ['E','labels','heights','metric']};row.update(world=world,m=m,L=L,Omega=Om,kappa=c['T']/Om,dimension=d,zero_count_with_multiplicities=sum(e['multiplicity']*(2 if e['kind']=='quartet' else 1) for e in eventall if mp.mpf(e['gamma'])<c['T']),distinct_zero_heights=len(heights),lambda_r_float=lr,lambda_r_preferred=preferred if preferred is not None else (lr if lrstatus=='FLOAT_RESOLVED' else None),lambda_r_status=lrstatus,min_included_normalized_gap=norms[imin] if imin is not None else None,min_gap_left=heights[imin] if imin is not None else None,min_gap_right=heights[imin+1] if imin is not None else None,last_included_height=heights[-1] if heights else None,lookahead_normalized_gap=look,quiet_status='J_ZERO_FULL_RANK' if not r else 'NONZERO_QUIET_SPACE',row_normalization='RAW physical samples; offreal Re/Im unscaled',**met,**pr)
  if c['variant']=='base':
   if q not in sigcache:sigcache[q]=conditioning(world,m,c['T'],E)
   sig=sigcache[q];sm=sig['sigma'];left=sig['left'];mass=[abs(v)**2 for v in left] if left is not None else [];byheight={}
   for label,value in zip(labels,mass):byheight.setdefault(label['gamma'],mp.mpf(0));byheight[label['gamma']]+=value
   hs=sorted(byheight,key=lambda x:mp.mpf(x));pair=max(range(len(hs)-1),key=lambda i:byheight[hs[i]]+byheight[hs[i+1]]) if len(hs)>1 else None
   row.update(sigma_min=sm,sigma_min_squared=sig['squared'],sigma_dps=sig.get('dps',dps),sigma_iterations=sig['iterations'],sigma_relative_residual=sig['relative_residual'],sigma_relative_change=sig['relative_change'],sigma_seconds=sig['seconds'],sigma_status=sig.get('method','MP_INVERSE_ITERATION'),sigma_float_radius=sig.get('float_sigma_radius'),sigma_retry_reason=sig.get('retry_reason'),weak_pair_left=hs[pair] if pair is not None else None,weak_pair_right=hs[pair+1] if pair is not None else None,weak_pair_mass=byheight[hs[pair]]+byheight[hs[pair+1]] if pair is not None else None,twice_sigma_squared_over_lambda_r=2*sig['squared']/preferred if sig['squared'] is not None and preferred is not None and preferred else (2*sig['squared']/lr if sig['squared'] is not None and lrstatus=='FLOAT_RESOLVED' and lr else None))
  if m in [24,65,77,78,80,120] and c['variant']=='base' and blocks is not None:
   tag=f"{world}_m{m}_{c['cut']}";D,B,G,S=blocks;np.savez_compressed(CELLS/(tag+'_blocks.npz'),D=D,B=B,G=G,S=S,Q=Q,U=U);blocks_saved.append(tag)
  rows.append(serial(row))
 thresholds=[]
 for B in [2,4]:
  mu=m**(-B);count=int(np.sum(ae<mu));tol=max(rad,1000*np.finfo(float).eps*d*max(1,float(la.norm(A,2))));uncertain=int(np.sum(abs(ae-mu)<=tol));target=d-count
  cumulative=0;lo=hi=None
  ev=events(world)
  if target==0:lo=mp.mpf(0);hi=mp.mpf(ev[0]['gamma'])
  for i,e in enumerate(ev[:-1]):
   cumulative+=1 if e['kind']=='line' else 2
   if cumulative==target:lo=mp.mpf(e['gamma']);hi=mp.mpf(ev[i+1]['gamma']);break
  thresholds.append(dict(B=B,mu=mu,signed_count=count,count_unresolved=uncertain,target_rank=target,kappa_sector_left=fmt(lo/Om) if lo is not None else None,kappa_sector_right=fmt(hi/Om) if hi is not None else None,status='UNRESOLVED_THRESHOLD_COUNT' if uncertain else ('EXACT_RANK_SECTOR' if lo is not None else 'NO_HEIGHT_CUTOFF_REALIZES_TARGET_RANK'),left_boundary_strict=True,right_boundary_included=True))
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',world=world,m=m,dps=dps,rows=rows,adaptive_thresholds=thresholds,basis=serial(basis_stats),saved_blocks=blocks_saved,seconds=time.monotonic()-start,source_matrix_sha256=hashlib.sha256((MATRICES/f'cell_{world}_m{m}.npz').read_bytes()).hexdigest(),within_source_asymptotic_regime=False)
 temporary=casepath.with_suffix('.json.tmp');temporary.write_text(json.dumps(result,indent=2)+'\n');temporary.replace(casepath);print('CELL',world,m,'seconds',round(result['seconds'],2),'sigma',[r.get('sigma_min') for r in rows if r['variant']=='base'],flush=True)
 return result

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--world',required=True);a.add_argument('--m',nargs='+',type=int,required=True);a.add_argument('--dps',type=int,default=80);a.add_argument('--skip-existing',action='store_true');args=a.parse_args()
 for m in args.m:
  if args.skip_existing and (CELLS/f'{args.world}_m{m}.json').exists():
   old=json.loads((CELLS/f'{args.world}_m{m}.json').read_text());current=hashlib.sha256((MATRICES/f'cell_{args.world}_m{m}.npz').read_bytes()).hexdigest()
   if old.get('world')==args.world and old.get('m')==m and len([r for r in old.get('rows',[]) if r['variant']=='base'])==3 and old.get('source_matrix_sha256')==current:continue
   raise ArithmeticError(f'checkpoint identity/hash mismatch {args.world} {m}')
  run(args.world,m,args.dps)
