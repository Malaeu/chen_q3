import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,time,csv
import mpmath as mp,numpy as np,scipy.linalg as la
from run import P,IN,census,mp_events,carrier,matrix
mp.mp.dps=80
rows=[]
for world in ['dh','plant']:
 h,b=next((h,b)for h,b in mp_events(world)if b);z=mp.mpc(h,b)
 for k in [mp.mpf('.1'),1,4,16]:
  y=k/h**2
  # Independent numerical integration of normalized physical heat kernel.
  integral=mp.quad(lambda u:mp.exp(-u*u/4)*mp.cos(z*mp.sqrt(y)*u)/(2*mp.sqrt(mp.pi)),[-mp.inf,0,mp.inf])
  predicted=mp.exp(-y*z*z);err=abs(integral-predicted)
  assert err<mp.mpf('1e-65')
  rows.append(dict(world=world,k=str(k),y=str(y),gamma=str(h),beta=str(b),predicted_real=str(predicted.real),predicted_imag=str(predicted.imag),relative_integral_error=str(err/abs(predicted)),damping=str(mp.exp(-y*(h*h-b*b))),phase=str(-2*y*h*b)))
(P/'GAUSSIAN_INTEGRAL_CHECK.json').write_text(json.dumps(rows,indent=2)+'\n')
# Independent MP carrier-evaluation stress at both grid endpoints.
checks=[]
for m in [310,600]:
 for world in ['zeta','dh','plant']:
  ev=census(world);z,E=carrier(m,ev);L=mp.log(m);freq=[(2*mp.pi*j/L)**2 for j in range(m+1)];ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
  EM=np.array([[complex(2*mp.mpc(h,b)*mp.sin(mp.mpc(h,b)*L/2)*ds[j]/(mp.sqrt(L)*(mp.mpc(h,b)**2-freq[j])))for j in range(m+1)] for h,b in mp_events(world)])
  for c in [8.,16.,32.]:
   y=c/(2*np.pi*m/np.log(m))**2;Af=matrix(z,E,y);Am=matrix(z,EM,y);diff=float(la.norm(Af-Am,2));guard=1000*np.finfo(float).eps*(m+1)*max(1,la.norm(Af,2));print('MPcheck',world,m,c,diff,guard,flush=True);assert diff<guard
   checks.append(dict(world=world,m=m,c=c,operator_difference=diff,guard=guard,ratio=diff/guard))
(P/'CARRIER_PRECISION_CHECK.json').write_text(json.dumps(checks,indent=2)+'\n')
print('Gaussian integral and MP carrier checks passed',flush=True)
rows=[]
for m in [310,450,600]:
 for world in ['dh','plant']:
  z,E=carrier(m,census(world));Om=2*np.pi*m/np.log(m);first=None
  for c in [8,12,16,24,32,48,64,96,128]:
   y=c/Om**2;A=matrix(z,E,y);ev,V=la.eigh(A);f=V[:,0] if first is None else first
   if first is None:first=f
   rows.append(dict(world=world,m=m,c=c,y=y,minimum=float(ev[0]),fixed_c8_vector_value=float(first@A@first),cap850_operator_difference=float(la.norm(A-matrix(z,E,y,850),2))))
with(P/'NEGATIVE_SWEEP.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
print('Negative-level sweep complete',flush=True)
# Descriptive comparison, not an asserted scalar law for a full eigenvalue.
for world in ['dh','plant']:
 h,b=next((h,b)for h,b in census(world)if b)
 for m in [310,450,600]:
  rr=[x for x in rows if x['world']==world and x['m']==m];base=rr[0]
  for x in rr:
   damp=float(np.exp(-(x['y']-base['y'])*(h*h-b*b)));ratio=x['minimum']/base['minimum'];x.update(first_quartet_damping_relative_to_c8=damp,observed_minimum_ratio_to_c8=ratio,relative_mismatch_from_scalar_damping=ratio/damp-1)
with(P/'NEGATIVE_SWEEP.csv').open('w',newline='')as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
