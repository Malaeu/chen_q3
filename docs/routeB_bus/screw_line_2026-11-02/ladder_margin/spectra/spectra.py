"""Positive spectral surrogate controls. DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import csv,json,time
import numpy as np
import scipy.linalg as la
from scipy.optimize import brentq
from scipy.fft import irfft
P=Path(__file__).resolve().parent;BUS=P.parents[2]
SCALE=8192;TMAX=6+1/32;TIMES=np.arange(int(TMAX*SCALE)+1)/SCALE
F=lambda x:x/(2*np.pi)*(np.log(x/(2*np.pi))-1)+7/8
MASS=lambda x:(np.log(x/(2*np.pi))+1)/(2*np.pi*x)
def invert(u):
 u=np.asarray(u,float);x=np.full(u.shape,100.)
 for k in range(30):
  y=F(x)-u;d=np.log(x/(2*np.pi))/(2*np.pi);x=np.maximum(2*np.pi+1e-5,x-y/d)
 return x

def tail(cut,power=22,period=16):
 N=2**power;omega=2*np.pi/period;index=np.arange(N//2+1,dtype=float);center=index*omega
 lo=np.maximum(cut,center-omega/2);hi=np.maximum(cut,center+omega/2)
 w=MASS(lo)-MASS(hi);w[0]=0;w[-1]=0
 assert np.min(w)>=0
 cos=N/2*irfft(w,n=N,workers=1)
 stride=N//(period*SCALE);ii=np.arange(len(TIMES))*stride
 g=-2*(MASS(cut)-cos[ii]);g[0]=0
 return g,dict(cut=cut,power=power,period=period,frequency_bin=omega,highest_frequency=center[-2],tail_pointnoise_mass=MASS(center[-2]+omega/2),represented_mass=float(w.sum()),total_mass=float(MASS(cut)))

def spectral(heights):
 value=np.zeros(len(TIMES));heights=np.asarray(heights)
 for i in range(0,len(heights),64):
  h=heights[i:i+64];x=np.multiply.outer(h,TIMES);np.cos(x,out=x);x-=1
  value+=2*(1/h**2)@x
 return value

def getter(values):
 def g(t):
  t=np.abs(np.asarray(t));return values[np.rint(t*SCALE).astype(int)]
 return g

def levinson(rr):
 v=rr[0];a=np.empty(0);vv=[v];status='POSITIVE';minimum=v
 for k in range(1,len(rr)):
  if v<=max(1e-13*rr[0],1e-16):status='UNRESOLVED_PSD_RANK_OR_ROUNDING';break
  alpha=(rr[k]-np.dot(a,rr[k-1:0:-1]))/v
  a=np.r_[a-alpha*a[::-1],alpha];v*=1-alpha**2
  if v<=0:status='UNRESOLVED_PSD_RANK_OR_ROUNDING';break
  vv.append(v);minimum=min(minimum,v)
 return np.asarray(vv),status

def block(g,rr,n,h,q):
 delta=h;d=h/q;D=(n-np.arange(n))*h
 B=g(D[:,None]+np.arange(1,q+1)*d-h)-g(D[:,None]+np.arange(q)*d-h)-g(D[:,None]+np.arange(1,q+1)*d)+g(D[:,None]+np.arange(q)*d)
 vals=g(np.arange(q+1)*d);fr=np.r_[-2*vals[1],2*vals[1:q]-vals[:q-1]-vals[2:q+1]]
 L=la.cholesky(la.toeplitz(rr[:n]),lower=True,check_finite=False);LF=la.cholesky(la.toeplitz(fr),lower=True,check_finite=False)
 Y=la.solve_triangular(L,B,lower=True,check_finite=False);G=Y.T@Y
 H=la.solve_triangular(LF,G,lower=True,check_finite=False);H=la.solve_triangular(LF,H.T,lower=True,check_finite=False).T;H=(H+H.T)/2
 return 1-la.eigvalsh(H,subset_by_index=[q-1,q-1],check_finite=False)[0]

def run_cell(world,rep,cut,values,profiles,multis,summary):
 g=getter(values)
 for mesh in [32,64,128,256]:
  h=1/mesh;gs=g(np.arange(6*mesh+2)*h);rr=np.r_[-2*gs[1],2*gs[1:-1]-gs[:-2]-gs[2:]];vv,status=levinson(rr)
  mu=vv/rr[0];n=np.arange(len(mu));mask=(n/mesh>=1)&(n/mesh<=6)
  summary.append(dict(world=world,rep=rep,cut=cut,mesh=mesh,status=status,resolved_prefixes=len(mu),primary_median=float(np.median(mu[mask])) if np.any(mask) else '',minimum_margin=float(np.min(mu))))
  for k in range(1,min(len(mu),6*mesh+1)):
   profiles.append(dict(world=world,rep=rep,cut=cut,mesh=mesh,a=k*h,mu_endpoint=float(mu[k])))
  for a in [1,3,6]:
   for q in [1,4,8,16,32]:
    try:m=block(g,rr,int(a*mesh),h,q);state='FINITE_SAMPLED'
    except la.LinAlgError:m='';state='UNRESOLVED_PSD_RANK_OR_ROUNDING'
    multis.append(dict(world=world,rep=rep,cut=cut,mesh=mesh,a=a,q=q,mu=m,status=state))


def write(name,rows):
 with (P/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)

def main():
 start=time.monotonic();known=list(csv.DictReader((BUS/'capacity_matrix_2026-11-02/zeros.csv').open()));z=np.array([float(x['gamma']) for x in known]);z=z[z<400];u0=F(z[0]);maxu=F(1600);needed=int(maxu-u0)+200
 tailcache={};metadata=[]
 for cut in [400,800,1600]:tailcache[cut],m=tail(cut);metadata.append(m)
 profiles=[];multis=[];summaries=[];generated=[]
 val=spectral(z)+tailcache[400];run_cell('zeta_surrogate',0,400,val,profiles,multis,summaries)
 # Genuine arithmetic source is a calibration reference, not reconstructed from real zeros.
 core=BUS/'screw_line_2026-11-02/innovation_law/core'
 for mesh in [32,64,128,256]:
  r=list(csv.DictReader((core/f'zeta_mesh{mesh}_dps100.csv').open()));x=[float(q['sigma2_over_local']) for q in r if 1<=float(q['t'])<=6]
  summaries.append(dict(world='zeta_arithmetic_reference',rep=0,cut=0,mesh=mesh,status='SAVED_MP100',resolved_prefixes=len(r),primary_median=float(np.median(x)),minimum_margin=min(x)))
 # Anchored picket and random ensembles share the smooth density map.
 specifications=[('picket',0,np.arange(needed)+u0)]
 for rep in range(20):
  rng=np.random.default_rng(20261103+rep)
  specs=u0+np.r_[0,np.cumsum(rng.exponential(size=needed-1))];specifications.append(('poisson',rep,specs))
  size=4096;diag=rng.normal(size=size);off=np.sqrt(rng.chisquare(2*np.arange(size-1,0,-1)))/np.sqrt(2)
  eig=la.eigh_tridiagonal(diag,off,eigvals_only=True,check_finite=False);x=eig/(2*np.sqrt(size));x=np.clip(x,-1,1)
  u=size*(.5+(np.arcsin(x)+x*np.sqrt(1-x*x))/np.pi)
  first=(size-needed)//2;uu=u[first:first+needed];uu=uu-uu[0]+u0;specifications.append(('gue_bulk',rep,uu))
 for world,rep,u in specifications:
  heights=invert(u);generated.append(dict(world=world,rep=rep,heights=heights.tolist()))
  cuts=[400,800,1600] if world=='picket' or rep<4 else [400]
  for cut in cuts:
   val=spectral(heights[heights<cut])+tailcache[cut];run_cell(world,rep,cut,val,profiles,multis,summaries)
   print('DONE',world,rep,cut,flush=True)
 # Tail-grid convergence: fixed zeta/picket spectra, no tuned new world.
 convergence=[]
 for power in [20,22,24]:
  tg,meta=tail(400,power)
  for world,heights in [('zeta_surrogate',z),('picket',invert(np.arange(needed)+u0))]:
   values=spectral(heights[heights<400])+tg;g=getter(values)
   for mesh in [32,64,128,256]:
    h=1/mesh;gs=g(np.arange(6*mesh+2)*h);rr=np.r_[-2*gs[1],2*gs[1:-1]-gs[:-2]-gs[2:]];vv,status=levinson(rr);mu=vv/rr[0];x=np.arange(len(mu))/mesh
    convergence.append(dict(world=world,power=power,mesh=mesh,status=status,primary_median=float(np.median(mu[(x>=1)&(x<=6)])),mu_a6_q32=block(g,rr,6*mesh,h,32)))
 write('scalar_profiles.csv',profiles);write('future_blocks.csv',multis);write('metrics.csv',summaries);write('tail_convergence.csv',convergence)
 (P/'generated_spectra.json').write_text(json.dumps(generated)+'\n');(P/'tail_metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
 (P/'run.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,zeta_count=len(z),maximum_zeta=float(max(z)),synthetic_replicates=20,source_table=str(BUS/'capacity_matrix_2026-11-02/zeros.csv')),indent=2)+'\n')
if __name__=='__main__':main()
