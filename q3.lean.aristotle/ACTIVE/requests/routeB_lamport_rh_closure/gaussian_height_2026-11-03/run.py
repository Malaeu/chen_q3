"""Gaussian zero-side literal even carrier. DIAGNOSTIC_NEVER_A_PROOF."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import json,csv,time,argparse
import numpy as np, scipy.linalg as la,mpmath as mp
from native_frame import frame
P=Path(__file__).resolve().parent;IN=Path(os.environ.get('GAUSSIAN_INPUTS',str(P/'inputs' if (P/'inputs').exists() else P.parent/'input')))
def census(world):
 if world in ['zeta','plant']:ev=[(float(r['gamma']),0.) for r in csv.DictReader((IN/'zeta_zeros.csv').open())]
 else:
  z=json.loads((IN/'dh_zeros_900_200dps.json').read_text());ev=[(float(r['gamma']),0.) for r in z['critical_line_zeros']]+[(float(r['gamma']),float(mp.mpf(r['sigma_right'])-mp.mpf('.5'))) for r in z['off_line_pairs']]
 if world=='plant':ev.append((2*np.pi/np.log(2),.25))
 return sorted(ev)
def mp_events(world):
 if world in ['zeta','plant']:ev=[(mp.mpf(r['gamma']),mp.mpf(0)) for r in csv.DictReader((IN/'zeta_zeros.csv').open())]
 else:
  z=json.loads((IN/'dh_zeros_900_200dps.json').read_text());ev=[(mp.mpf(r['gamma']),mp.mpf(0)) for r in z['critical_line_zeros']]+[(mp.mpf(r['gamma']),mp.mpf(r['sigma_right'])-mp.mpf('.5')) for r in z['off_line_pairs']]
 if world=='plant':ev.append((2*mp.pi/mp.log(2),mp.mpf('.25')))
 return sorted(ev)
def carrier(m,ev):
 L=np.log(m);w=np.arange(m+1)*2*np.pi/L;d=np.r_[1.,np.full(m,np.sqrt(2.))]
 z=np.array([complex(h,b) for h,b in ev]);E=2*z[:,None]*np.sin(z[:,None]*L/2)*d/(np.sqrt(L)*(z[:,None]**2-w[None,:]**2))
 return z,E
def matrix(z,E,y,cap=np.inf):
 a=z.real<=cap;z=z[a];E=E[a];weights=np.where(z.imag==0,2.,4.)*np.exp(-y*z*z)
 A=np.real(E.T@(weights[:,None]*E));return (A+A.T)/2

def scan(m,world,bits=768):
 mp.mp.dps=260;start=time.time();ev=census(world);z,E=carrier(m,ev);Om=2*np.pi*m/np.log(m);d=m+1;events=mp_events(world);rows=[];sectors=[]
 L=mp.log(m);freq=[(2*mp.pi*j/L)**2 for j in range(d)];ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 for i,(h,b) in enumerate(events):
  mult=2 if b else 1
  if len(rows)+mult>=d:break
  zz=mp.mpc(h,b);fac=2*zz*mp.sin(zz*L/2)/mp.sqrt(L) if b else 1
  rr=[fac*ds[j]/(zz*zz-freq[j]) for j in range(d)];rows.append([x.real for x in rr])
  if b:rows.append([x.imag for x in rr])
  hi=float(events[i+1][0])/Om;lo=float(h)/Om
  if hi>=1:sectors.append(dict(q=len(rows),r=d-len(rows),kappa_left=lo,kappa_right=hi))
 assert sectors
 uf,piv=frame(rows,bits);U,_=la.qr(uf.T,mode='full');orth=float(la.norm(uf@uf.T-np.eye(len(rows)),2));results=[];receipts=[]
 for c in [8.,16.,32.]:
  y=c/Om**2;A=matrix(z,E,y);vals,V=la.eigh(A);norm=max(abs(vals));guard=1000*np.finfo(float).eps*d*max(1,norm)
  tail_checks=[dict(cap=cap,operator_difference=float(la.norm(A-matrix(z,E,y,cap),2))) for cap in [750.,850.]]
  AQ=A@U;best=-np.inf;bestrow=None;evals=[];bounded=[]
  for s in sectors:
   lam=vals[s['r']]
   if lam+guard<=max(best-guard,guard):
    bounded.append(dict(**s,lambda_r=float(lam),gap_upper=float(lam+guard)));continue
   delta=float(la.svdvals(AQ[:,s['q']:])[0]);gap=float(lam-delta);row=dict(**s,lambda_r=float(lam),delta=delta,gap=gap);evals.append(row)
   if gap>best:best=gap;bestrow=row
  # Always include the last sector, even when it is unresolved.
  if not evals:
   s=sectors[-1];delta=float(la.svdvals(AQ[:,s['q']:])[0]);bestrow=dict(**s,lambda_r=float(vals[s['r']]),delta=delta,gap=float(vals[s['r']]-delta));best=bestrow['gap'];evals=[bestrow]
  upper=max([r['gap']+guard for r in evals]+[r['gap_upper'] for r in bounded]);lower=best-guard
  out=dict(world=world,m=m,c=c,y=y,Omega=Om,minimum=float(vals[0]),resolved_negative_count=int(sum(vals < -guard)),guard=guard,best_gap=best,max_gap_lower=lower,max_gap_upper=upper,status='PASS_NUMERIC' if best>guard else ('FAIL_NUMERIC' if upper<0 else 'UNRESOLVED'),best=bestrow,sectors=len(sectors),evaluated=len(evals),bounded=len(bounded),frame_orthogonality=orth,tail_checks=tail_checks,max_input_height=float(z.real.max()),input_events=len(z),seconds=time.time()-start)
  if world!='zeta':
   h,b=next((h,b) for h,b in ev if b);zz=complex(h,b);idx=next(i for i,x in enumerate(z) if x==zz);v=E[idx];W=4*np.real(np.outer(v,v));ew,ewv=la.eigh(W);f=ewv[:,0];wy=4*np.real(np.exp(-y*zz*zz)*np.outer(v,v));out['quartet_control']=dict(gamma=h,beta=b,damping=float(np.exp(-y*(h*h-b*b))),phase=-2*y*h*b,unsmoothed_bottom=float(ew[0]),smoothed_bottom=float(la.eigvalsh(wy)[0]),fixed_vector_value=float(f@wy@f),norm_A_minus_quartet=float(la.norm(A-wy,2)))
  results.append(out);receipts.append(dict(c=c,evaluated=evals,bounded=bounded))
 O=P/'cells';O.mkdir(exist_ok=True);(O/f'{world}_{m}_{bits}.json').write_text(json.dumps(dict(summary=results,receipts=receipts),indent=2)+'\n');print(world,m,bits,[(r['c'],r['status'],r['best_gap'],r['minimum']) for r in results],flush=True)
 return results
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--world',nargs='+',default=['zeta','dh','plant']);a.add_argument('--m',type=int,nargs='+',default=list(range(310,601,10)));a.add_argument('--bits',type=int,default=768);args=a.parse_args()
 for m in args.m:
  for w in args.world:
   if not (P/'cells'/f'{w}_{m}_{args.bits}.json').exists():scan(m,w,args.bits)
