"""Pinned literal-even m248 residual-mode dissection; numerical diagnostics."""
from pathlib import Path
import sys,json,csv,hashlib,os
import numpy as np,scipy.linalg as la,gmpy2 as g
P=Path(__file__).resolve().parent;S=Path(os.environ.get('LITERAL_BASE','/workspace/zero_extension'));sys.path.insert(0,str(S))
from native_frame import frame

def prepare(m,bits):
 g.get_context().precision=bits;L=g.log(m);zs=[g.mpfr(r['gamma'])for r in csv.DictReader((S/'zeta_zeros.csv').open())];freq=[(2*g.const_pi()*j/L)**2 for j in range(m+1)];ds=[g.mpfr(1)]+[g.sqrt(2)]*m
 rows=[[ds[j]/(h*h-freq[j])for j in range(m+1)]for h in zs[:132]];uf,piv=frame(rows,bits);W,_=la.qr(uf.T,mode='full');a=np.load(S/f'matrices/zeta_m{m}.npz');return a['A'],a['eigenvalues'],W,np.array(zs,float),float(L),uf
records=[];detail={};vectors=[];profiles=[];zeros=[];replay={}
for m in [247,248,249]:
 A,ae,W,z,L,uf=prepare(m,768);d=m+1;omega=2*np.pi*m/L
 for q in range(125,132):
  Q=W[:,q:];U=W[:,:q];sv=la.svd(A@Q,full_matrices=False);vals=sv[1];V=sv[2].T;y=V[:,0];f=Q@y
  if f[0]<0:f=-f;y=-y
  D=Q.T@A@Q;B=U.T@A@Q;dy=D@y;by=B@y
  nr=float(abs(W[:,q]@f)**2);Tleft=z[q-1];Tright=z[q]
  rec=dict(m=m,q=q,r=d-q,lambda_r=float(ae[d-q]),delta=float(vals[0]),sigma2=float(vals[1]),gap=float(ae[d-q]-vals[0]),top_two_squared_ratio=float(vals[0]**2/(vals[0]**2+vals[1]**2)),top_squared_fraction_frobenius=float(vals[0]**2/sum(vals**2)),D_norm_squared=float(dy@dy),B_norm_squared=float(by@by),residual_squared_decomposition_error=float(vals[0]**2-dy@dy-by@by),D_Rayleigh=float(y@dy),new_row_height=float(z[q]),next_constraint_mode_mass=nr,cutoff_left=Tleft,cutoff_right=Tright,kappa_left=Tleft/omega,kappa_right=Tright/omega,intersects_kappa_ge1=bool(Tright>=omega));records.append(rec)
  if m==248 and q==127:
   de,dv=la.eigh(D);fa,va=la.eigh(A);over=dv.T@y;ov=va.T@f;b=np.array([1]+[np.sqrt(2)]*m)/np.sqrt(L);eQ=Q.T@b
   detail=dict(rec,omega=omega,L=L,f_endpoint=float(b@f),endpoint_carrier_cosine_squared=float((b@f)**2/(b@b)),endpoint_quiet_functional_cosine_squared=float((eQ@y)**2/(eQ@eQ)),top_D_mode_overlaps=[dict(index=int(k),lambda_D=float(de[k]),squared_overlap=float(over[k]**2),residual_D_energy=float(de[k]**2*over[k]**2))for k in np.argsort(over**2)[-12:][::-1]],full_A_resolved_mode_overlaps=[dict(index=int(k),lambda_A=float(fa[k]),squared_overlap=float(ov[k]**2),A_energy=float(fa[k]**2*ov[k]**2))for k in np.argsort(fa**2*ov**2)[-12:][::-1]],D_eigen_residual_check=float(la.norm(D@dv-dv*de)),carrier_top_coefficients=[dict(n=int(k),coefficient=float(f[k]),mass=float(f[k]**2))for k in np.argsort(f**2)[-20:][::-1]],full_A_overlap_unresolved_scope='Float resolved modes only; near-zero eigenvector decomposition is basis-dependent and not interpreted',source_sha256=hashlib.sha256((S/f'matrices/zeta_m{m}.npz').read_bytes()).hexdigest())
   for j in range(d):vectors.append(dict(n=j,top_residual_carrier=f[j],second_residual_carrier=(Q@V[:,1])[j]))
   for x in np.linspace(-L/2,L/2,401):profiles.append(dict(kind='physical',argument=x,value=float(sum(f[j]*(1 if j==0 else np.sqrt(2))*(-1)**j*np.cos(2*np.pi*j*x/L)for j in range(d))/np.sqrt(L))))
   for t in np.linspace(250,315,651):
    om=2*np.pi*np.arange(d)/L;rr=2*np.array([1]+[np.sqrt(2)]*m)*t*np.sin(t*L/2)/(np.sqrt(L)*(t*t-om*om));profiles.append(dict(kind='Fourier',argument=t,value=float(rr@f)))
   for k,h in enumerate(z):
    sp=2*np.pi/np.log(h/(2*np.pi))
    if min(abs(h-Tleft),abs(h-Tright),abs(h-omega))<=sp:
     zeros.append(dict(index_one_based=k+1,gamma=h,included_q127=bool(k<127),cutoff_omega_distance=(h-omega)/sp,left_distance_local=(h-Tleft)/sp,right_distance_local=(h-Tright)/sp,previous_gap_local=(h-z[k-1])*np.log(h/(2*np.pi))/(2*np.pi)if k else None,previous_gap_carrier=(h-z[k-1])*L/(2*np.pi)if k else None))
   replay['768_f']=f;replay['768_Q']=Q;replay['768_delta']=vals[0]
 if m==248:
  A2,_,W2,_,_,_=prepare(m,1024);Q2=W2[:,127:];s2=la.svd(A2@Q2,full_matrices=False);f2=Q2@s2[2][0];replay['check']=dict(delta768=float(replay['768_delta']),delta1024=float(s2[1][0]),projector_difference=float(la.norm(replay['768_Q']@replay['768_Q'].T-Q2@Q2.T,2)),mode_squared_overlap=float((replay['768_f']@f2)**2))
for name,rows in [('neighbors.csv',records),('vectors.csv',vectors),('profiles.csv',profiles),('nearby_zeros.csv',zeros)]:
 with (P/name).open('w')as out:w=csv.DictWriter(out,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
detail['precision_frame_check']=replay['check'];(P/'MODE.json').write_text(json.dumps(detail,indent=2)+'\n');print(json.dumps(detail,indent=2))
