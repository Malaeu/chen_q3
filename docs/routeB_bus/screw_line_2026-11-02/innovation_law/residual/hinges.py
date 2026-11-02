"""Fixed-history temporal hinges, distinct from coefficient gradients."""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import numpy as np
from scipy.linalg import solve_toeplitz,toeplitz
from residual import *

def main():
 mp.mp.dps=80;rows=[];checks=[]
 repair='--repair-near-grid' in sys.argv
 if repair:
  previous=list(csv.DictReader((ROOT/'hinges.csv').open()))
  checks=list(csv.DictReader((ROOT/'hinges_mp_validation.csv').open()))
  selected={(x['world'],int(x['mesh']),int(x['n'])) for x in previous if mp.mpf(x['absolute_error'])>mp.mpf('1e-8')}
 for mesh in (32,64):
  h=mp.mpf(1)/mesh
  for world in ('zeta','dh','plant'):
   g,atoms=g_function(world,mp.mpf(6));weights={n:w for s,w,n in atoms}
   gs=[g(i*h) for i in range(6*mesh+1)];rr=r_from(gs)
   for t,_,n in arithmetic('zeta',mp.mpf(6)):
    if mesh==64 and n not in (2,3,5,8,16,27,97,331,397):continue
    if repair and (world,mesh,n) not in selected:continue
    q=int(mp.floor(t/h));a=q*h;cn=weights.get(n,mp.mpf(0))
    r=rr[:q];rf=np.array([float(x) for x in r]);T=toeplitz(rf)
    def cross(z):return [g(z-i*h)-g(z-(i-1)*h)-gs[q-i]+gs[q-i+1] for i in range(1,q+1)]
    b=cross(t);bf=np.array([float(x) for x in b]);beta=solve_toeplitz(rf,bf,check_finite=False)
    residual=float(np.max(np.abs(T@beta-bf)))
    predicted=2*cn*mp.mpf(float(beta[0]));d=-2*g(t-a)
    # Epsilon excludes all additional shifted arithmetic hinges and grid endpoints.
    distances=[abs(t-k*h-s) for s,w,integer in atoms for k in range(q+1) if abs(t-k*h-s)>mp.mpf('1e-50')]
    eps=min(mp.mpf('1e-8'),(t-a)/10000,min(distances)/100) if repair else min(mp.mpf('1e-6'),(t-a)/10,min(distances)/10)
    jumps=[];continuities=[]
    for ee in (eps,eps/2):
     diffs=[]
     for sign in (-1,1):
      z=t+sign*ee;db=[x-y for x,y in zip(cross(z),b)]
      dbf=np.array([float(x) for x in db]);sol=solve_toeplitz(rf,dbf,check_finite=False)
      diff=-2*g(z-a)-d-2*mp.fsum(mp.mpf(float(beta[i]))*db[i] for i in range(q))-mp.fsum(mp.mpf(float(sol[i]))*db[i] for i in range(q))
      diffs.append(diff)
     jumps.append((diffs[0]+diffs[1])/ee);continuities.append(max(abs(x) for x in diffs))
    measured=2*jumps[1]-jumps[0]
    rec=dict(world=world,mesh=mesh,n=n,threshold=st(t),history=q,coefficient=st(cn),beta_first=st(mp.mpf(float(beta[0]))),predicted_jump=st(predicted),measured_jump=st(measured),absolute_error=st(abs(measured-predicted)),epsilon=st(eps),continuity_change_eps=st(continuities[0]),continuity_change_half=st(continuities[1]),toeplitz_solve_residual=residual)
    rows.append(rec)
    if not repair and mesh==32 and n in (2,17,97):
     states=levinson(r,set(range(1,q+1)));betamp=[mp.mpf(0)]*q
     for k,(v,w,oldneg,neg) in states.items():
      dot=mp.fsum(w[i]*b[i] for i in range(k))/v
      for i in range(k):betamp[i]+=dot*w[i]
     checks.append(dict(world=world,mesh=mesh,n=n,max_beta_error=st(max(abs(betamp[i]-mp.mpf(float(beta[i]))) for i in range(q))),MP_predicted_jump=st(2*cn*betamp[0]),float_predicted_jump=st(predicted),jump_difference=st(abs(2*cn*betamp[0]-predicted)),past_negative_index=states[q][3]))
   print('HINGES',world,mesh,flush=True)
 if repair:
  keys={(r['world'],int(r['mesh']),int(r['n'])):r for r in rows}
  common=list(rows[0])
  rows=[keys.get((r['world'],int(r['mesh']),int(r['n'])),{k:r[k] for k in common}) for r in previous]
 write('hinges.csv',rows);write('hinges_mp_validation.csv',checks)
if __name__=='__main__':main()
