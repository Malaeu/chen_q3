"""Finite sampled extension margins; DIAGNOSTIC_NEVER_A_PROOF."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,csv,argparse,time
import numpy as np
import scipy.linalg as la
from scipy.special import spence
import mpmath as mp
ROOT=Path(__file__).resolve().parent
CORE=ROOT.parents[1]/'innovation_law'/'core'
sys.path.insert(0,str(CORE));from scan import source,coefficients

def write(name,rows):
 with (ROOT/name).open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)

def float_source(world,end=6.3):
 mp.mp.dps=100;bb=coefficients(int(np.ceil(np.exp(end))),world)
 logs=np.array([np.log(n) for n in range(2,len(bb))]);weights=np.array([float(bb[n]/mp.sqrt(n)) for n in range(2,len(bb))]); cw=np.r_[0,np.cumsum(weights)];clw=np.r_[0,np.cumsum(weights*logs)]
 alpha=1.5 if world=='dh' else .5;c=float(-mp.euler-mp.log(8*mp.pi/(5 if world=='dh' else 1))+(1 if world=='dh' else -1)*mp.pi/2);trig=float(mp.polygamma(1,mp.mpf(str(alpha))/2)/4)
 w=2*np.pi/np.log(2)+.25j
 def g(t):
  t=np.abs(np.asarray(t,dtype=float));x=np.exp(-t/2);tail=spence(1-x)-spence(1+x)+(2 if world!='dh' else -2)*np.imag(spence(1-1j*x));ind=np.searchsorted(logs,t,side='left')
  y=-c*t/2-trig+tail+t*cw[ind]-clw[ind]
  if world!='dh':y-=16*np.sinh(t/4)**2
  if world=='plant':y+=4*np.real((np.cos(w*t)-1)/w**2)
  return np.where(t==0,0.,y)
 return g

def block(g,rr,n,h,delta,q):
 d=delta/q;D=(n-np.arange(n))*h
 # Gram of old increments and fresh increments, both zero-extended step tests.
 B=g(D[:,None]+np.arange(1,q+1)*d-h)-g(D[:,None]+np.arange(q)*d-h)-g(D[:,None]+np.arange(1,q+1)*d)+g(D[:,None]+np.arange(q)*d)
 vals=g(np.arange(q+1)*d);fr=np.r_[-2*vals[1],2*vals[1:q]-vals[:q-1]-vals[2:q+1]];F=la.toeplitz(fr)
 C=la.toeplitz(rr[:n]);L=la.cholesky(C,lower=True,check_finite=False);LF=la.cholesky(F,lower=True,check_finite=False)
 Y=la.solve_triangular(L,B,lower=True,check_finite=False);G=Y.T@Y
 H=la.solve_triangular(LF,G,lower=True,check_finite=False);H=la.solve_triangular(LF,H.T,lower=True,check_finite=False).T;H=(H+H.T)/2
 top=la.eigvalsh(H,subset_by_index=[q-1,q-1],check_finite=False)[0]
 return dict(mu=1-top,lambda_max=top,fresh_min_chol=float(np.min(np.diag(LF))),old_min_chol=float(np.min(np.diag(L))),normalization='finite fresh Gram F, incremental coordinates',precision='float64 source, MP100 old r'),(B,F,C)

def main():
 start=time.monotonic();single=[];multi=[];search=[];checks=[]
 for mesh in [32,64,128,256]:
  h=1/mesh
  for world in ['zeta','dh','plant']:
   saved=json.loads((CORE/f'{world}_mesh{mesh}_dps100.json').read_text());rr=np.array(saved['r_values'],float);old=list(csv.DictReader((CORE/f'{world}_mesh{mesh}_dps100.csv').open()));first=saved['first_negative_prefix'];g=float_source(world)
   mp.mp.dps=80;gm,_=source(world,mp.mpf('6.3'))
   for t in [h/32,h,1.,3.,6.,6.25]:checks.append(dict(world=world,mesh=mesh,t=t,source_error=abs(float(g(t))-float(gm(mp.mpf(t))))))
   for n in range(1,len(old)):
    valid=first is None or n<first
    single.append(dict(world=world,mesh=mesh,old_count=n,a=n*h,delta=h,mu=old[n]['sigma2_over_local'] if valid else '',past_valid=valid,extension_positive=valid and int(old[n]['negative_inertia'])==0,next_prefix=n+1))
   samples=set(k*mesh for k in range(1,7))
   if first:samples.update([first-2,first-1,first])
   for n in sorted(samples):
    for q in [1,4,8,16,32]:
     base=dict(world=world,mesh=mesh,old_count=n,a=n*h,delta=h,q=q)
     if first and n>=first:multi.append(dict(**base,mu='',status='INVALID_PAST',fresh_min_chol='',old_min_chol='',normalization='',precision=''));continue
     try:
      result,_=block(g,rr,n,h,h,q);multi.append(dict(**base,**result,status='FINITE_SAMPLED'))
     except la.LinAlgError:multi.append(dict(**base,mu='',status='FACTORIZATION_UNRESOLVED',fresh_min_chol='',old_min_chol='',normalization='',precision=''))
   if world=='zeta':
    for n in [mesh,3*mesh,6*mesh]:
     for q in sorted(set([1,2,4,8,16,32,64,128,mesh])):
      if q>mesh:continue
      delta=q*h/4
      result,_=block(g,rr,n,h,delta,q)
      search.append(dict(world=world,mesh=mesh,old_count=n,a=n*h,future_step=h/4,delta=delta,q=q,**result,status='NESTED_FINITE_SAMPLED'))
   print('DONE',world,mesh,flush=True)
 write('single_endpoint.csv',single);write('future_refinement.csv',multi);write('nested_step_search.csv',search);write('source_validation.csv',checks)
 (ROOT/'run_summary.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,single_rows=len(single),multi_rows=len(multi),nested_rows=len(search),max_float_source_error=max(x['source_error'] for x in checks)),indent=2)+'\n')
if __name__=='__main__':main()
