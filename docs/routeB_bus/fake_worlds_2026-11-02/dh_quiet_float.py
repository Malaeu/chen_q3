"""All-m survey; float64 resolution flags retained, never a rank cutoff."""
from pathlib import Path
import json,csv
import numpy as np
from scipy.linalg import svd,svdvals,eigvalsh
P=Path(__file__).resolve().parent

def erow(z,m):
 L=np.log(m);n=np.arange(m+1);ds=np.where(n==0,1,np.sqrt(2));w=2*np.pi*n/L
 return 2*ds*z*np.sin(z*L/2)/(np.sqrt(L)*(z*z-w*w))
def run():
 z=json.loads((P/'dh_zeros.json').read_text());out=[]
 for m in range(20,121):
  A=np.load(P/'matrix_cells'/f'dh_float_m{m}.npz')['A'];d=m+1;Om=2*np.pi*m/np.log(m);cache={}
  for k in [1+j/50 for j in range(21)]:
   E=[];sign=[]
   for a in z['critical_line_zeros']:
    g=float(a['gamma'])
    if g<k*Om:E.append(erow(g,m));sign.append(1)
   for a in z['off_line_pairs']:
    g=float(a['gamma']);dd=float(a['sigma_right'])-.5
    if g<k*Om:
     v=erow(g+1j*dd,m);E.extend([np.sqrt(2)*v.real,np.sqrt(2)*v.imag]);sign.extend([1,-1])
   q=len(E);r=max(0,d-q)
   if q not in cache:
    E=np.array(E);U,s,V=svd(E,full_matrices=True);R=E/np.linalg.norm(E,axis=1)[:,None];Ur,sr,Vr=svd(R,full_matrices=True);Q=Vr[min(q,d):].T
    delta=svdvals(A@Q)[0] if r else 0.;res=svdvals(E@Q)[0] if r else 0.
    cond=sr[0]/sr[-1];rawok=s[-1]>1e-11*s[0];quietok=not r or cond<1e10
    W=2*E.T@np.diag(sign)@E
    cache[q]=dict(q=q,rank_algebraic=min(q,d),dim_J=r,delta_float=delta,sigma_min_squared_float=s[-1]**2,raw_capacity_resolved_float=rawok,kernel_resolved_float=quietok,row_scaled_condition=cond,E_Q_residual_float=res,signed_zero_form_min_float=eigvalsh(W,subset_by_index=[0,0])[0],off_line_pair_count=sign.count(-1))
   out.append(dict(m=m,kappa=k,T=k*Om,**cache[q]))
 with (P/'quiet_float.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=out[0]);w.writeheader();w.writerows(out)
 print('rows',len(out),'rawresolved',sum(x['raw_capacity_resolved_float'] for x in out),'kernelresolved',sum(x['kernel_resolved_float'] for x in out))
if __name__=='__main__':run()
