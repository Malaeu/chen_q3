"""Fixed constant-gauge heldout diagnostics; no freely fitted analytic gauge."""
from pathlib import Path
import json,csv,sys
import numpy as np
import mpmath as mp
from scipy.optimize import brentq
P=Path(__file__).resolve().parent
mp.mp.dps=30

def pieces(d,z):
 z=np.asarray(z,dtype=complex);n=np.arange(d['m']+1);w=2*np.pi*n/d['L'];b=d['a'];ds=np.r_[1.,np.repeat(np.sqrt(2),d['m'])];sg=(-1.)**n
 low=np.sinc((z[...,None]-w)*b/np.pi);high=np.sinc((z[...,None]+w)*b/np.pi)
 C=((low+high)*(ds*sg*b/np.sqrt(d['L'])))@np.array(d['even_coefficients'])
 S=((low[...,1:]-high[...,1:])*(ds[1:]*sg[1:]*b/np.sqrt(d['L'])))@np.array(d['odd_coefficients'])
 return C,S

def W(d,z,theta):
 C,S=pieces(d,z);z=np.asarray(z);return (z-1j)*(C+1j*S)+np.exp(1j*theta)*(z+1j)*(C-1j*S)

def targets(world,z):
 z=mp.mpc(complex(z));s=mp.mpf('.5')-1j*z
 if world=='zeta':
  
  if s==1 or s==0:
   ell=(2+mp.euler-mp.log(4*mp.pi))/2*(1 if s==1 else -1)
   return complex(z*z/ell),complex(1/(1+ell))
  D=mp.zeta(s);Dp=mp.zeta(s,derivative=1);g=1/s+1/(s-1)-mp.log(mp.pi)/2+mp.digamma(s/2)/2
 else:
  c=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);a=[0,1,c,-c,-1]
  if s==1:
   D=-sum(a[k]*mp.digamma(mp.mpf(k)/5) for k in range(1,5))/5
   Dp=-mp.log(5)*D-sum(a[k]*mp.stieltjes(1,mp.mpf(k)/5) for k in range(1,5))/5
  else:D=mp.dirichlet(s,a);Dp=mp.dirichlet(s,a,derivative=1)
  g=mp.log(5/mp.pi)/2+mp.digamma((s+1)/2)/2
 return complex(z*z*D/(Dp+g*D)),complex(D/(D+Dp+g*D))

def run(world,m,xmax=None,suffix=""):
 d=json.loads((P/f'profile_{world}_m{m}.json').read_text());xs=np.linspace(0,.8*d['Omega'] if xmax is None else xmax,41);zs=np.array([x+1j*y for y in [.05,.25,.5] for x in xs]);cal=np.tile(np.arange(41)<21,3);tar=np.array([targets(world,z) for z in zs]);anchor=np.array(targets(world,.25j));rows=[];best=[]
 for j in range(16):
  th=2*np.pi*j/16;ww=W(d,zs,th);wa=W(d,.25j,th)
  for v in range(2):
   gauge=anchor[v]/wa;err=np.abs(gauge*ww-tar[:,v])/np.maximum(np.abs(tar[:,v]),1e-300);r=dict(world=world,m=m,target=['v1','v3'][v],theta_index=j,theta=th,constant_gauge_real=float(gauge.real),constant_gauge_imag=float(gauge.imag),calibration_rms=float(np.sqrt(np.mean(err[cal]**2))),heldout_rms=float(np.sqrt(np.mean(err[~cal]**2))),heldout_max=float(np.max(err[~cal])),origin_W_abs=float(abs(W(d,0,th))));r['negative_grid_max']=float(np.max(np.abs(gauge*W(d,-zs.conjugate(),th)-tar[:,v].conjugate())/np.maximum(np.abs(tar[:,v]),1e-300)));rows.append(r)
 for v in ['v1','v3']:best.append(min([r for r in rows if r['target']==v],key=lambda r:r['calibration_rms']))
 roots=[];upper=.8*d['Omega'] if xmax is None else xmax;xx=np.linspace(0,upper,int(upper/.025)+2);C,S=pieces(d,xx)
 for j in range(16):
  th=np.pi*j/16;yy=(np.cos(th)*(xx*C+S)+np.sin(th)*(xx*S-C)).real
  fun=lambda z:float((np.cos(th)*(z*pieces(d,z)[0]+pieces(d,z)[1])+np.sin(th)*(z*pieces(d,z)[1]-pieces(d,z)[0])).real)
  rr=[0.] if j==0 else []
  for k in range(len(xx)-1):
   if yy[k]*yy[k+1]<0:
    r=brentq(fun,xx[k],xx[k+1],xtol=2e-12)
    if not rr or abs(r-rr[-1])>1e-7:rr.append(r)
  roots.append(dict(theta_index=j,roots=rr,count=len(rr),max_dephased_residual=max([abs(fun(r)) for r in rr],default=0)))
 out=dict(world=world,m=m,grid=f'Im .05,.25,.5; Re 0..{upper} 41 points; first21 calibrate, remaining20 heldout',negative_grid='evaluated at -conj(z), using exact target conjugation; W evaluated independently',gauge='constant anchored at i/4, not arbitrary analytic phi',selected=best,all_theta=rows,real_roots=roots,status='FLOAT_DIAGNOSTIC_ONLY')
 (P/f'diagnostic_{world}_m{m}{suffix}.json').write_text(json.dumps(out,indent=2)+'\n');print(world,m,best,flush=True)
if __name__=='__main__':
 for m in ([int(sys.argv[1])] if len(sys.argv)>1 else [20,40,60,80,120,160,200,240]):
  for world in ['zeta','dh']:run(world,m)
