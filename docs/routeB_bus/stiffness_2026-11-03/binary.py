"""Finite calibration reuse: pinned dense arrays and saved quiet frames."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,csv,hashlib,time
import numpy as np,scipy.linalg as la
from knobs import make_knobs
from diagnostics import tangent
P=Path(__file__).resolve().parent;BASE=Path(os.environ.get('STIFFNESS_BASE','/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03'));sys.path.insert(0,str(BASE));import solve
old={(x['world'],int(x['m'])):x for x in csv.DictReader((BASE/'SUMMARY.csv').open())}

def inertia(K,rho,label):
 e=la.eigvalsh(K);n=len(e);g=max(rho,1000*np.finfo(float).eps*n*max(1,la.norm(K,2)));out=dict(positive=int(sum(e>g)),negative=int(sum(e< -g)),unresolved_zero=int(sum(abs(e)<=g)),guard=g,minimum=float(e[0]),maximum=float(e[-1]),structural=None)
 if label=='C_pole':out.update(positive=int(np.any(K)),negative=0,unresolved_zero=n-int(np.any(K)),structural='EXACT_ZERO_OR_PSD_RANK_ONE')
 return out

def one_interval(A,K,eps,rho,label):
 G=A+eps*np.eye(len(A));lo=la.eigvalsh(G,subset_by_index=[0,0])[0]
 if not np.any(K):return dict(status='ALL_REAL'if lo>8*rho else'EMPTY_NUMERIC'if lo< -8*rho else'UNRESOLVED',lower_offset=None,upper_offset=None)
 if label=='C_pole':
  e,V=la.eigh(K);p=V[:,-1]*np.sqrt(max(e[-1],0));v=p/la.norm(p);Z=la.null_space(v[None,:]);H=Z.T@G@Z;he,hv=la.eigh(H)
  if he[0]< -16*rho:return dict(status='EMPTY_NUMERIC',negative_kernel_witness=float(he[0]),lower_offset=None,upper_offset=None,reason='NEGATIVE_RAYLEIGH_ORTHOGONAL_TO_PSD_KNOB')
  if lo>8*rho:
   s=float(p@la.solve(G,p,assume_a='pos'));return dict(status='ONE_SIDED_PSD',lower_offset=-1/s,upper_offset=None,upper_unbounded=True)
  if he[0]>16*rho:
   b=Z.T@G@v;a=float(v@G@v);off=float((b@la.solve(H,b,assume_a='pos')-a)/la.norm(p)**2);return dict(status='ONE_SIDED_PSD',lower_offset=off,upper_offset=None,upper_unbounded=True)
  return dict(status='UNRESOLVED_PSD_KERNEL',lower_offset=None,upper_offset=None)
 C=A-K;f=solve.feasible_anchor(C,K,eps,rho)
 if f['status']=='SPD_ANCHOR':
  ends=solve.anchored(C,K,eps,f['anchor']);d=dict(status='FINITE_OR_ONE_SIDED_NUMERIC',anchor=f['anchor'])
  for x in ends:d[x['side']+'_offset']=x['offset_from_one'];d[x['side']+'_unbounded']=x['status']=='UNBOUNDED'
  return d
 return {k:v for k,v in f.items()if k not in ['history','lower_vector','upper_vector']}

def run(m,w):
 start=time.time();z=np.load(BASE/'source'/f'{w}_m{m}.npz');A=z['A1'];C=z['C'];B=z['B'];eps=float(old[w,m]['epsilon']);rho=float(old[w,m]['precision_floor']);labels,K=make_knobs(m,C,B,w);K=np.array(K);error=float(np.max(abs(K.sum(axis=0)-A)));gate=error<=rho
 E,V=la.eigh(A);n=len(A);floor=rho;ratios=[float(max(E[j],floor)/max(E[j-1],floor))for j in range(1,n//2+1)];r=1+int(np.argmax(ratios));F=V[:,:r];M=np.array([F.T@x@F for x in K]);D=F.T@A@F;scale=max(la.norm(x,2)for x in M);face_relative=float(la.norm(D,2)/max(scale,1e-300));face_gate=face_relative<=1e-8
 quiet=np.load(BASE/'quiet/frames'/f'{"dh"if w=="dh"else"zeta"}_m{m}.npz')['Q'];recon=float(la.norm(M.sum(axis=0)-D,2));out=dict(world=w,m=m,epsilon=eps,rho=rho,source_reconstruction_max_entry=error,P1_gate=bool(gate),face_size=r,face_gap_ratio=ratios[r-1],face_selection_floor=floor,face_all_ratios=ratios,face_PAP_norm=float(la.norm(D,2)),face_component_norm_max=float(scale),face_relative=face_relative,face_gate=bool(face_gate),face_sum_residual=recon,quiet_QAQ_norm=float(la.norm(quiet.T@A@quiet,2)),quiet_reference='REFERENCE_J_ZETA'if w=='double2'else'OWN_J',baseline_minimum=float(E[0]),inertias={label:inertia(k,rho,label)for label,k in zip(labels,K)},exit_overlaps=[],labels=labels)
 cell=BASE/'cells'/f'{w}_m{m}_f100.json'
 if cell.exists():
  orig=json.loads(cell.read_text())
  for ex in orig['solver'].get('endpoints',[]):
   if 'carrier_vector'in ex:out['exit_overlaps'].append(dict(side=ex['side'],mass_in_face=float(la.norm(F.T@np.array(ex['carrier_vector']))**2)))
 if gate and face_gate:
  ix=np.triu_indices(r);vec=M[:,ix[0],ix[1]].T;vec[ix[0]!=ix[1]]*=np.sqrt(2);uu,s,vh=la.svd(vec,full_matrices=True);threshold=max(1000*np.finfo(float).eps*max(vec.shape)*s[0],rho);rank=int(sum(s>threshold));ker=vh[rank:];prices=K.sum(axis=0)
  out['P2']=dict(singular_values=s.tolist(),rank=rank,kernel_dimension=len(labels)-rank,kernel_basis=ker.tolist(),threshold=threshold,ones_image_norm=float(la.norm(M.sum(axis=0),2)),ones_relative=float(la.norm(M.sum(axis=0),2)/(max(1,la.norm(np.ones(len(labels))))*max(s[0],1e-300))))
  out['P3']=tangent(M)
 else:out['P2_status']=out['P3_status']='STOPPED_FAILED_GATE'
 out['P4']=[]
 if gate:
  for label,k in zip(labels,K):
   if label in ['C_Gamma','C_pole']or(label.startswith('B_')and label[2:].isdigit()and int(label[2:])<=13):out['P4'].append(dict(knob=label,**one_interval(A,k,eps,rho,label)))
 out['seconds']=time.time()-start;dest=P/'binary_cells';dest.mkdir(exist_ok=True);(dest/f'{w}_m{m}.json').write_text(json.dumps(out,indent=2)+'\n');print(w,m,'P1',error,'face',r,'ratio',face_relative,'gate',face_gate,'seconds',out['seconds'],flush=True)
 return out
if __name__=='__main__':
 for m in [16,24,40,80,120,200,248,300]:
  for w in ['zeta','dh','double2']:run(m,w)
