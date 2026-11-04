"""Own-source DH raw detector and MP confirmation of weak-core witnesses."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import sys,json,time,hashlib,importlib.util,re
from fractions import Fraction
import numpy as np
from scipy.linalg import eigh
P=Path(__file__).resolve().parent
sys.path[:0]=['/workspace/conditioning_deps',str(P/'builder')]
import gmpy2 as g
from core_components import build
F=g.mpfr

def write(f,d):
 f.parent.mkdir(exist_ok=True);t=f.with_suffix('.tmp');t.write_text(json.dumps(d,indent=2)+'\n');t.replace(f)
def fresh(m):
 spec=importlib.util.spec_from_file_location('fresh_aux_pinned',P/'inputs/analytic_source.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);a,meta=mod.build(m,256);return mod,a,meta

def prime_form(m,v,mod):
 L=g.log(m);pi=g.const_pi();omega=[2*pi*j/L for j in range(m+1)];d=[F(1)]+[g.sqrt(2)]*m
 c=[v[j]*d[j]*((-1)**j)/g.sqrt(L) for j in range(m+1)];ze,_=mod.coefficients(max(300,m),256);total=F(0)
 for n in range(2,m):
  if not ze[n]:continue
  shift=g.log(n);left=-L/2;right=L/2-shift;corr=F(0)
  def integral(k,phase):
   if k==0:return (right-left)*g.cos(phase)
   return (g.sin(k*right+phase)-g.sin(k*left+phase))/k
  for i in range(m+1):
   for j in range(m+1):
    I=(integral(omega[i]-omega[j],-omega[j]*shift)+integral(omega[i]+omega[j],omega[j]*shift))/2
    corr+=c[i]*c[j]*I
  total+=2*ze[n]/g.sqrt(n)*corr
 return total

def weak_confirm():
 d=json.loads((P/'core/core_results.json').read_text());rows=[]
 for key,entry in d['first_weak_detections'].items():
  mat=re.fullmatch(r'a(.+?)_gamma(\d+)_(.+)',key);a=Fraction(mat[1]);gamma=int(mat[2]);convention=mat[3];m=entry['first_m'];f=P/'core'/entry['vector'];raw=f.read_bytes();vectors=np.load(f,allow_pickle=False);mod,A,meta=fresh(m)
  L=g.log(m);pi=g.const_pi();omega=[2*pi*j/L for j in range(m+1)];W=[1+w*w for w in omega];p=[g.sqrt(2/L)*(1 if j==0 else g.sqrt(2))*g.sinh(L/4)/(omega[j]**2+F('.25')) for j in range(m+1)]
  dot=lambda x,y:sum((v*w for v,w in zip(x,y)),F(0))
  if convention=='physical_pole_null':
   z=[F(float(v)) for v in vectors['physical_z']];co=dot(p,z)/dot(p,p);z=[v-co*w for v,w in zip(z,p)];constraint=dot(p,z)
  else:
   y=[F(float(v)) for v in vectors['normalized_y']];co=dot(p,y)/dot(p,p);y=[v-co*w for v,w in zip(y,p)];z=[v/g.sqrt(w) for v,w in zip(y,W)];constraint=dot(p,y)
  source=sum((z[i]*sum((A['zeta'][0][i,j]*z[j] for j in range(m+1)),F(0)) for i in range(m+1)),F(0));B=prime_form(m,z,mod);den=sum((w*v*v for w,v in zip(W,z)),F(0));plant=F(0)
  if gamma:
   q=g.mpc(gamma,F(a.numerator)/a.denominator);ss=g.sin(q*L/2);c=[2*(1 if j==0 else g.sqrt(2))*q*ss/(g.sqrt(L)*(q*q-omega[j]**2)) for j in range(m+1)];qv=sum((v*w for v,w in zip(z,c)),g.mpc(0));plant=4*(qv*qv).real
  value=(source+B/F(10)+plant)/den;assert value<F('-1e-6'),(key,str(value));assert abs(float(value)-entry['value'])<1e-10,(key,str(value),entry['value'])
  out=dict(status='PASS_296_BIT_WEAK_NEGATIVE_WITNESS',key=key,m=m,a=str(a),gamma=gamma,convention=convention,rayleigh=str(value),raw_source_rayleigh=str(source/den),prime_rayleigh=str(B/den),plant_rayleigh=str(plant/den),constraint_residual=str(constraint),W_norm=str(den),vector_sha256=hashlib.sha256(raw).hexdigest(),bits=256,working_bits=296,scope='Physical-overlap prime form independently evaluated; MP projection enforces the chosen constraint. Point arithmetic, not interval/source certification.')
  write(P/'aux_confirmation'/f'weak_{key.replace("/","_")}.json',out);rows.append(out);print(json.dumps(dict(weak=key,value=str(value))),flush=True)
 write(P/'weak_confirmation_summary.json',dict(status='ALL_14_WEAK_WITNESSES_CONFIRMED',cases=len(rows),rows=rows))

def dh_probe():
 cells=[];first=None;vfirst=None
 for m in range(16,3001):
  parts,meta=build(m,'dh');values,v=eigh(parts['A'],subset_by_index=[0,0],driver='evr',check_finite=False);lam=float(values[0]);vec=v[:,0];peak=int(np.argmax(vec*vec));cells.append(dict(m=m,lambda_min=lam,detected=lam<-1e-6,peak_mode=peak,peak_frequency=float(parts['omega'][peak])))
  if lam<-1e-6:first=m;vfirst=vec;break
  if m>=200:break
 assert first is not None,'DH first threshold unresolved within feasible prefix'
 mod,A,meta=fresh(first);vv=[F(float(x)) for x in vfirst];den=sum((x*x for x in vv),F(0));ray=sum((vv[i]*sum((A['dh'][0][i,j]*vv[j] for j in range(first+1)),F(0)) for i in range(first+1)),F(0))/den;assert ray<F('-1e-6')
 result=dict(status='DH_FIRST_RAW_DETECTION_CONFIRMED',first_m=first,cells=cells,high_precision_rayleigh=str(ray),bits=256,working_bits=296,native_pole='absent, p_D=0',source_meta=meta,vector=vfirst.tolist(),scope='Every integer from16 tofirst checked; MP fresh own-source negative witness, not high-precision ordering of predecessors.')
 write(P/'dh_detection.json',result);print(json.dumps(dict(DH_first=first,rayleigh=str(ray))),flush=True)
 # Common post-detection checkpoints retain the raw detector alongside core C*.
 checkpoints=[]
 for m in [80,128,256,512,1000,1500,2000,3000]:
  parts,meta=build(m,'dh');values,v=eigh(parts['A'],subset_by_index=[0,0],driver='evr',check_finite=False);j=int(np.argmax(v[:,0]**2));checkpoints.append(dict(m=m,lambda_min=float(values[0]),peak_mode=j,peak_frequency=float(parts['omega'][j])))
 write(P/'dh_checkpoints.json',dict(cells=checkpoints,native_pole='absent'))

if __name__=='__main__':
 weak_confirm();dh_probe()
