"""Integer-aligned genuine screw-kernel prefixes; finite passivity judge.
Not a canonical-system impedance. Float scan has independent quadrature and
high-precision source checks; it is not an interval certificate.
"""
from pathlib import Path
import numpy as np
from exact_label_records import ZERO
from scipy.special import roots_legendre
import mpmath as mp
import json,csv,time
from curve import Source,coefficients
P=Path(__file__).resolve().parent;(P/'runtime_cache').mkdir(exist_ok=True)

def run(world):
 start=time.time();mp.mp.dps=85;s=Source(world,300);b=np.array([float(x) for x in s.b]);logs=np.log(np.arange(1,len(b)));ww=b[1:]/np.sqrt(np.arange(1,len(b)));cw=np.cumsum(ww);cl=np.cumsum(ww*logs)
 def psi(t,order):
  t=np.asarray(t);out=np.zeros(t.shape);mask=t>0;v=t[mask]
  zz,w=roots_legendre(order);u=v[:,None]*(zz+1)/2
  jj=u*np.exp(-float(s.alpha)*u)/(-np.expm1(-2*u));arch=(jj@w)*v/2
  aa=np.exp(-v/2);tail=np.arctanh(aa)+(np.arctan(aa) if world=='zeta' else -np.arctan(aa))
  pole=4*(np.expm1(v/2)+np.expm1(-v/2)) if world=='zeta' else 0
  inds=np.searchsorted(logs,v,side='right')-1;arith=np.where(inds>=0,v*cw[np.maximum(inds,0)]-cl[np.maximum(inds,0)],0)
  out[mask]=float(s.c)*v/2+arch+v*tail+pole-arith
  return out
 ns=np.arange(2,241);ts=np.log(ns);tau=np.log(240)*(240.5/240)
 t_all=np.r_[ts,np.abs(ts[:,None]-ts[None,:]).ravel(),tau,np.abs(tau-ts)]
 low=psi(t_all,64);high=psi(t_all,128);maxdiff=float(np.max(np.abs(high-low)))
 vals=high[:len(ts)];offset=len(ts);diff=high[offset:offset+len(ts)**2].reshape(len(ts),len(ts));offset+=len(ts)**2
 vt=high[offset];kt=high[offset+1:];G=vals[:,None]+vals[None,:]-diff;k=vals+vt-kt
 N=len(ts);LL=np.eye(N);D=np.zeros(N);y=np.zeros(N);E=0.;rows=[];neg=0
 for j in range(N):
  dj=G[j,j]-np.dot(LL[j,:j]**2,D[:j]);D[j]=dj
  if dj==0:raise ArithmeticError('zero float Schur pivot')
  neg+=int(dj<0);yj=k[j]-np.dot(LL[j,:j],y[:j]);y[j]=yj;increment=yj*yj/dj;E+=increment
  LL[j+1:,j]=(G[j+1:,j]-(LL[j+1:,:j]*D[:j])@LL[j,:j])/dj
  n=int(ns[j]);bn=0. if world=='dh' and n in ZERO else b[n];rows.append({'m':n,'prefix_dimension':j+1,'L':ts[j],'negative_inertia':neg,'Schur_pivot':dj,'projection_energy':E,'increment':increment,'target_residual':2*vt-E,'b_m':bn,'b_sign':int(np.sign(bn)),'zeta_prime_power':bool(coefficients(240,'zeta')[n]),'atom_born':bool(bn),'section_status':'NEGATIVE_SAMPLED_INNOVATION' if dj<0 else 'POSITIVE_SAMPLED_INNOVATION_NOT_A_PASSIVITY_PROOF'})
 recon=G-(LL*D)@LL.T;err=float(np.linalg.norm(recon,ord=np.inf));spot=[]
 for t in [mp.mpf('.004'),mp.log(2),mp.log(6),mp.log(mp.mpf(53)/17),mp.log(20),mp.log(240),mp.mpf(str(tau))]:
  exact=s.psi(t);approx=float(psi(np.array([float(t)]),128)[0]);spot.append({'t':mp.nstr(t,80),'mp_value':mp.nstr(exact,80),'float_absolute_error':float(abs(exact-mp.mpf(approx)))})
 eig=np.linalg.eigvalsh(G);negative=[r for r in rows if r['Schur_pivot']<0]
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':world,'nodes':'t_n=log(n),n=2..240,old nodes never moved','fixed_target_tau':tau,'float64':True,'source_orders':[64,128],'max_source_quadrature_difference':maxdiff,'high_precision_source_spots':spot,'LDL_reconstruction_inf_norm':err,'final_min_eigenvalue_float':float(eig[0]),'final_negative_eigenvalues_float':int(sum(eig<0)),'first_negative_innovation':negative[0] if negative else None,'first_inertia_loss_without_birth':next((r for r in negative if not r['atom_born']),None),'rows':rows,'seconds':time.time()-start}
 (P/f'aligned_{world}.json').write_text(json.dumps(result,indent=2)+'\n')
 with (P/f'aligned_{world}.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 np.savez_compressed(P/'runtime_cache'/f'aligned_{world}_local.npz',G=G,k=k,LL=LL,D=D)
 print(world,'negative',len(negative),'first',negative[0] if negative else None,'quad',maxdiff,'recon',err,flush=True)
if __name__=='__main__':
 import sys
 run(sys.argv[1])
