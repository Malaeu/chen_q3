"""DH resolution positive control; source float matrix and MP100 witness."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,time,csv
import numpy as np
import scipy.linalg as la
import mpmath as mp
P=Path(__file__).resolve().parent;BUS=P.parents[1]
sys.path.insert(0,str(BUS/'screw_line_2026-11-02/extension_margin/uniform'));from margins import float_source
sys.path.insert(0,str(P));from stitch import zeros
CORE=BUS/'screw_line_2026-11-02/innovation_law/core'

def count(ev,floor):return dict(negative=int(sum(ev<-floor)),positive=int(sum(ev>floor)),unresolved=int(sum(abs(ev)<=floor)),raw_negative=int(sum(ev<0)),minimum=float(ev[0]))
def gram(g,left,right):
 return g(right[:,None]-right[None,:])-g(right[:,None]-left[None,:])-g(left[:,None]-right[None,:])+g(left[:,None]-left[None,:])

def main():
 start=time.monotonic();mp.mp.dps=100;m=40;mesh=256;L=np.log(m);a=np.log(m-1);delta=L-a
 nodes=np.array(sorted(set([k/mesh for k in range(int(np.floor(L*mesh))+1)]+[a+j*delta/4 for j in range(5)])));left=nodes[:-1];right=nodes[1:];lengths=np.diff(nodes);old=int(np.searchsorted(nodes,a));d=len(lengths);g=float_source('dh');A=gram(g,left,right)/np.sqrt(lengths[:,None]*lengths[None,:]);A=(A+A.T)/2
 saved=json.loads((CORE/'dh_mesh256_dps100.json').read_text());rr=np.array(saved['r_values'],float);p=int(np.floor(a*mesh));A[:p,:p]=la.toeplitz(rr[:p])*mesh
 # Replay the already independently checked first-negative source witness.
 check=next(x for x in saved['checks'] if x['kind']=='first_negative_direct_quadratic');ww=np.array(saved['snapshots']['944']['coefficients'],float);mid=(left+right)/2;ii=np.floor(mid*mesh).astype(int);w=np.array([ww[k] if k<944 else 0. for k in ii])*np.sqrt(lengths);w/=np.linalg.norm(w);ray=float(w@A@w);expected=float(mp.mpf(check['normalized_rayleigh'])*mesh)
 assert ray<0 and abs(ray-expected)<1e-8
 floor=1e-7;full=la.eigvalsh(A,check_finite=False);C=A[:old,:old];B=A[:old,old:];F=A[old:,old:];ce=la.eigvalsh(C,check_finite=False);ci=count(ce,floor)
 if ce[0]<=floor:raise ArithmeticError('Old positive history numerically unresolved')
 LL=la.cho_factor(C,lower=True,check_finite=False);sol=la.cho_solve(LL,B,check_finite=False);S=F-B.T@sol;ev,z=la.eigh(S,check_finite=False);f=np.r_[-sol@z[:,0],z[:,0]];section=count(ev,floor);source_energy=float(f@A@f)
 results=[];records=[]
 for name,c in [('kappa1',0),('cquarter',.25),('chalf',.5)]:
  kappa=1+c*(1+np.log(L))/L;T=kappa*2*np.pi*m/L;zs=zeros('dh',mp.mpf(T));E=[]
  for item in zs:
   zz=complex(item['z']);v=2*np.exp(1j*zz*mid)*np.sin(zz*lengths/2)/(zz*np.sqrt(lengths))
   E.extend([v.real/np.linalg.norm(v.real),v.imag/np.linalg.norm(v.imag)])
  E=np.array(E);ue,s,vh=la.svd(E,full_matrices=True,check_finite=False);rank=int(sum(s>1e-10*s[0]));assert rank==E.shape[0] and s[-1]>1e-8
  U=vh[:rank].T;Q=vh[rank:].T;r=Q.shape[1];D=Q.T@A@Q;G=U.T@A@U;QB=Q.T@A@U
  qrec={}
  for threshold in [0,2]:
   De=D-threshold*np.eye(r);de=la.eigvalsh(De,check_finite=False);di=count(de,floor)
   if np.min(abs(de))<=floor:
    qrec[str(threshold)]=dict(guard='UNRESOLVED_ELIMINATED',D=di);continue
   sq=G-threshold*np.eye(rank)-QB.T@la.solve(De,QB,assume_a='sym',check_finite=False);se=la.eigvalsh(sq,check_finite=False);si=count(se,floor);fi=count(full-threshold,floor);identity=fi['raw_negative']==di['raw_negative']+si['raw_negative']
   qrec[str(threshold)]=dict(guard='NUMERICALLY_RESOLVED',D=di,S=si,full=fi,raw_inertia_identity=identity)
  lamr=full[r];proj=np.linalg.norm(U.T@f);ratio=float(ev[0]/(lamr*proj**2)) if lamr>floor and proj>floor else None
  row=dict(world='dh',m=m,ambient='uniform256_plus_exact_section_nodes',dimension=d,old_dimension=old,fresh_dimension=d-old,cutoff=name,kappa=kappa,T=T,rank=rank,quiet_dimension=r,complex_evaluation_points=sum('complex' in x['kind'] for x in zs),rank_smallest_singular=s[-1],old_minimum=ce[0],old_negative=ci['negative'],old_unresolved=ci['unresolved'],full_minimum=full[0],full_negative=count(full,floor)['negative'],full_unresolved=count(full,floor)['unresolved'],section_S0_min=ev[0],section_S0_negative=section['negative'],section_S0_unresolved=section['unresolved'],angle_f_J_degrees=float(np.degrees(np.arccos(np.clip(np.linalg.norm(Q.T@f)/np.linalg.norm(f),0,1)))),delta_full_AQ=float(la.svdvals(A@Q,check_finite=False)[0]),quiet_compression_norm=float(np.max(abs(la.eigvalsh(D,check_finite=False)))),lambda_r=lamr,ratio=ratio,quiet_D0_negative=qrec['0']['D']['negative'],quiet_S0_negative=qrec['0'].get('S',{}).get('negative'),quiet_S0_min=qrec['0'].get('S',{}).get('minimum'),quiet_D2_negative=qrec['2']['D']['negative'],quiet_S2_negative=qrec['2'].get('S',{}).get('negative'),quiet_D_below2=qrec['2']['D']['negative']==r,precision='float64, MP100 old uniform source and witness',numeric_floor=floor,constraint_residual=float(np.linalg.norm(E@Q)),section_energy_replay_error=abs(source_energy-ev[0]))
  results.append(row);records.append(dict(metrics=row,quiet_indices=qrec));print(name,'fullneg',row['full_negative'],'old',row['old_negative'],'Ssection0',ev[0],'D0',row['quiet_D0_negative'],'Squiet0',row['quiet_S0_negative'],flush=True)
  (P/'resolution_control_checkpoint.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',records=records),indent=2)+'\n')
 with (P/'resolution_control.csv').open('w',newline='') as f0:
  wr=csv.DictWriter(f0,fieldnames=results[0]);wr.writeheader();wr.writerows(results)
 (P/'resolution_control.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,source_rayleigh=ray,stored_MP100_expected_rayleigh=expected,witness_absolute_change=abs(ray-expected),records=records,source_matrix='Full arithmetic source; leading uniform Toeplitz block from MP100 r; remaining entries float64',interval_certificate=False),indent=2)+'\n')
if __name__=='__main__':main()
