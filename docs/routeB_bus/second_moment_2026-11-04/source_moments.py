"""Pinned-source second moments. Diagnostic, never a proof; dense arrays local only."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,csv,time,hashlib,importlib.util,argparse
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import numpy as np
BASE=Path(os.environ.get('SECOND_BASE','/workspace/stiffness/repo/docs/routeB_bus/arithmetic_coupling_2026-11-03'))
OUT=Path(__file__).resolve().parent
LOCAL=Path(os.environ.get('SECOND_LOCAL','/workspace/second_moment/local'))/'source'
SOURCE=BASE/'source/split.py'
def load():
 s=importlib.util.spec_from_file_location('unchanged_split',SOURCE);v=importlib.util.module_from_spec(s);s.loader.exec_module(v);return v
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def arrhash(a):return hashlib.sha256(np.ascontiguousarray(a).tobytes()).hexdigest()
def inner(a,b):return float(np.einsum('ij,ij->',a,b))
def pole_and_innovation(m,s):
 g=s.g;L=g.log(m);ds=[g.mpfr(1)]+[g.sqrt(2)]*m
 p=np.array([4*g.sqrt(2)*ds[n]*L**g.mpfr('1.5')*g.sinh(L/4)/(L*L+16*s.pi*s.pi*n*n)for n in range(m+1)],float)
 z=g.mpc(2*s.pi/g.log(2),g.mpfr('.25'));e=[2*ds[n]*z*g.sin(z*L/2)/(g.sqrt(L)*(z*z-(2*s.pi*n/L)**2))for n in range(m+1)]
 W=np.array([[4*(a*b).real for b in e]for a in e],float)
 return np.outer(p,p),W

def atoms(m,co):
 L=np.log(m);j=np.arange(m+1);ds=np.ones(m+1);ds[1:]=np.sqrt(2);ii=j[:,None];jj=j[None,:];den=ii*ii-jj*jj;den=np.where(den==0,1,den);fac=ds[:,None]*ds[None,:]/np.pi/den
 primepowers=set()
 for p in range(2,m+1):
  if all(p%k for k in range(2,int(p**.5)+1)):
   n=p
   while n<=m:primepowers.add(n);n*=p
 total=np.zeros((m+1,m+1));diag=0.;npdiag=0.;count=0;neg=0;extra=0
 for n in range(2,m+1):
  b=float(co[n]);
  if b==0:continue
  count+=1;neg+=b<0;extra+=n not in primepowers
  if n==m:continue # exact endpoint atom is zero
  r=np.log(n)/L;w=b/np.sqrt(n);si=np.sin(2*np.pi*j*r);cs=np.cos(2*np.pi*j*r)
  a=w*fac*(j[:,None]*si[:,None]-j[None,:]*si[None,:]);d=-w*(2*(1-r)*cs-np.divide(si,np.pi*j,out=np.zeros_like(si),where=j!=0));np.fill_diagonal(a,d)
  v=inner(a,a);diag+=v;npdiag+=v*(n not in primepowers);total+=a
 return total,dict(arithmetic_diagonal=diag,nonprime_diagonal=npdiag,atom_count=count,negative_b_count=neg,nonprime_atom_count=extra,endpoint_n_m_coefficient=float(co[m]),endpoint_atom_exact_zero=True)

def run(task):
 m,q=task;start=time.monotonic();dest=LOCAL/f'm{m}_q{q}.json'
 if dest.exists():return json.loads(dest.read_text())
 s=load();raw=s.build(m,q);P,W=pole_and_innovation(m,s);coeff=s.coefficient(m);rows=[];decomp=[];arrays={}
 for w,k in [('zeta',0),('dh',1),('plant',0)]:
  C=np.array(raw['zeta'if w=='plant'else w]['C'],float);B=np.array(raw['zeta'if w=='plant'else w]['B'],float);A=np.array(raw['zeta'if w=='plant'else w]['A1'],float);pole=P if w!='dh'else np.zeros_like(P);G=C-pole;innovation=W if w=='plant'else np.zeros_like(W);A=A+innovation
  if w!='plant':atomB,meta=atoms(m,coeff[k]);atomcache=(atomB,meta)if w=='zeta'else atomcache
  else:atomB,meta=atomcache
  terms=dict(G2=inner(G,G),P2=inner(pole,pole),GP=2*inner(G,pole),GB=2*inner(G,B),PB=2*inner(pole,B),B_diagonal=meta['arithmetic_diagonal'],B_offdiagonal=inner(B,B)-meta['arithmetic_diagonal'],W2=inner(innovation,innovation),GW=2*inner(G,innovation),PW=2*inner(pole,innovation),BW=2*inner(B,innovation))
  frob=inner(A,A);abssum=sum(abs(v)for v in terms.values());rec=max(abs((A-G-pole-B-innovation)).flat)
  row=dict(world=w,m=m,dimension=m+1,source_bits=400,GL_order=q,panels=8,trace=float(np.trace(A)),Frob2=frob,decomposition_sum=sum(terms.values()),conservation_error=sum(terms.values())-frob,C_B_reconstruction_maxerr=float(rec),arithmetic_atom_reconstruction_maxerr=float(np.max(np.abs(atomB-B))),arithmetic_scope='ALL signed n including non-prime-powers'if w=='dh'else'prime powers only',source_sha256=sha(SOURCE),A_array_sha256=arrhash(A),C_array_sha256=arrhash(C),B_array_sha256=arrhash(B),**meta)
  rows.append(row)
  for name,value in terms.items():decomp.append(dict(world=w,m=m,GL_order=q,component=name,value=value,signed_share=value/frob,share_of_sum_abs_terms=abs(value)/abssum,absolute_contribution_over_Frob2=abs(value)/frob))
  for name,a in [('A',A),('C',C),('B',B),('G',G),('P',pole),('W',innovation)]:arrays[f'{w}_{name}']=a
 LOCAL.mkdir(parents=True,exist_ok=True);p=LOCAL/f'm{m}_q{q}.npz';np.savez_compressed(p,**arrays)
 for row in rows:row.update(local_array_path=str(p),local_array_file_sha256=sha(p))
 result=dict(m=m,GL_order=q,seconds=time.monotonic()-start,rows=rows,decomposition=decomp);dest.write_text(json.dumps(result,indent=2)+'\n');print('DONE',m,q,round(result['seconds'],2),rows[0]['Frob2'],rows[1]['Frob2'],flush=True);return result

def csvwrite(name,rows):
 with(OUT/name).open('w')as f:
  wr=csv.DictWriter(f,fieldnames=list(rows[0]));wr.writeheader();wr.writerows(rows)
def aggregate():
 data=[json.loads(p.read_text())for p in sorted(LOCAL.glob('m*_q192.json'),key=lambda p:int(p.stem.split('_')[0][1:]))];rows=[r for d in data for r in d['rows']];decomp=[r for d in data for r in d['decomposition']]
 if rows:csvwrite('SOURCE_MOMENTS.csv',rows);csvwrite('DECOMPOSITION.csv',decomp)
 (OUT/'SOURCE_MOMENTS.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',expected_m=285,completed_m=len(data),rows=rows),indent=2)+'\n')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--ms',default='16:300');ap.add_argument('--q',type=int,default=192);ap.add_argument('--workers',type=int,default=2);ap.add_argument('--aggregate-only',action='store_true');a=ap.parse_args();LOCAL.mkdir(parents=True,exist_ok=True)
 if not a.aggregate_only:
  ms=list(range(int(a.ms.split(':')[0]),int(a.ms.split(':')[1])+1))if':'in a.ms else list(map(int,a.ms.split(',')))
  with ProcessPoolExecutor(max_workers=a.workers)as ex:list(ex.map(run,[(m,a.q)for m in ms]))
 aggregate()

def arithmetic_pair_mass(m=300):
 """Both net and pairwise-absolute off-diagonal arithmetic mass, local atoms only."""
 s=load();coeff=s.coefficient(m);L=np.log(m);j=np.arange(m+1);ds=np.ones(m+1);ds[1:]=np.sqrt(2);ii=j[:,None];jj=j[None,:];den=ii*ii-jj*jj;den=np.where(den==0,1,den);fac=ds[:,None]*ds[None,:]/np.pi/den;result=[]
 primary=json.loads((LOCAL/f'm{m}_q192.json').read_text());dec=primary['decomposition'];mass={}
 for w,k in [('zeta',0),('dh',1)]:
  vals=[];ns=[]
  for n in range(2,m):
   b=float(coeff[k][n])
   if b==0:continue
   r=np.log(n)/L;wt=b/np.sqrt(n);si=np.sin(2*np.pi*j*r);cs=np.cos(2*np.pi*j*r);a=wt*fac*(j[:,None]*si[:,None]-j[None,:]*si[None,:]);np.fill_diagonal(a,-wt*(2*(1-r)*cs-np.divide(si,np.pi*j,out=np.zeros_like(si),where=j!=0)));vals.append(a.ravel());ns.append(n)
  V=np.array(vals);gram=V@V.T;np.fill_diagonal(gram,0);pos=float(np.sum(gram[gram>0]));neg=float(np.sum(gram[gram<0]));net=float(np.sum(gram));absolute=float(np.sum(np.abs(gram)));mass[w]=dict(atom_count_excluding_zero_endpoint=len(ns),positive_cross_sum=pos,negative_cross_sum=neg,net_offdiagonal=net,absolute_pair_mass=absolute,abs_net_offdiag=abs(net),ordered_pair_convention='sum over n != k; equivalently twice unordered pairs',Gram_array_sha256=arrhash(gram),atom_matrix_array_sha256=arrhash(V));del V,gram,vals
 for w in ['zeta','dh','plant']:
  r=next(r for r in primary['rows']if r['world']==w);v=dict(mass['zeta'if w=='plant'else w]);off=next(t['value']for t in dec if t['world']==w and t['component']=='B_offdiagonal');v.update(world=w,m=m,Frob2=r['Frob2'],existing_decomposition_offdiagonal=off,net_offdiagonal_minus_existing= v['net_offdiagonal']-off,abs_net_offdiag_over_Frob2=v['abs_net_offdiag']/r['Frob2'],absolute_pair_mass_over_Frob2=v['absolute_pair_mass']/r['Frob2'],positive_cross_sum_over_Frob2=v['positive_cross_sum']/r['Frob2'],negative_cross_sum_over_Frob2=v['negative_cross_sum']/r['Frob2'],source_bits=400,atom_and_Gram_arithmetic='binary64; unchanged analytic atoms; no source rebuild',status='DIAGNOSTIC_NEVER_A_PROOF');result.append(v)
 (OUT/f'ARITHMETIC_PAIR_MASS_m{m}.json').write_text(json.dumps(result,indent=2)+'\n');csvwrite(f'ARITHMETIC_PAIR_MASS_m{m}.csv',result);return result
