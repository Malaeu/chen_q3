"""Rebuild pinned source A and evaluation QR, never a source eigensystem."""
from pathlib import Path
import json,sys,time,csv,os
import mpmath as mp
from functools import lru_cache
from fixed_source import weights,panels
from rellich_helpers import Erow_and_dot
INPUT_ROOT=Path(os.environ.get('EDGE_CAPACITY_INPUT_ROOT',str(Path(__file__).resolve().parent.parent/'inputs')))
P=Path(os.environ.get('EDGE_DENSE',str(INPUT_ROOT/'dense')));P.mkdir(exist_ok=True)
@lru_cache(None)
def build_A(m,world,order):
 L=mp.log(m);d=m+1;b=weights(world,m);alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5')
 sm=[mp.mpf(0)]*d;di=sm.copy();ps=sm.copy();pd=sm.copy()
 for y,w in panels(order):
  x=L*y;wt=L*w*mp.exp(-alpha*x)/(-mp.expm1(-2*x));co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   sm[n]+=wt*sn;di[n]+=wt*(2*y+2*(1-y)*(1-cn)+(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 for k in range(2,m):
  if not b[k]:continue
  y=mp.log(k)/L;wt=b[k]/mp.sqrt(k);co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(d):
   ps[n]+=wt*sn;pd[n]+=wt*(2*(1-y)*cn-(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;beta=[sm[i]+ps[i] for i in range(d)]
 c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2 if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
 aa=mp.exp(-L/2);tail=mp.atanh(aa)+(mp.atan(aa) if world=='zeta' else -mp.atan(aa));A=mp.zeros(d)
 pole=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(d)])
 for i in range(d):
  A[i,i]=c+di[i]+2*tail-pd[i]
  for j in range(i+1,d):A[i,j]=A[j,i]=ds[i]*ds[j]/mp.pi*(i*beta[i]-j*beta[j])/(i*i-j*j)
 if world=='zeta':A+=pole*pole.T
 return A

def build_case(path,zeros_path,dhzeros_path,dps=180,order=192):
 mp.mp.dps=dps;start=time.monotonic();raw=json.loads(Path(path).read_text());m=raw['m'];world=raw['world'];L=mp.log(m);T=mp.mpf(raw['T']);q=raw['q'];rows=[];labels=[]
 if world=='zeta':
  zz=list(csv.DictReader(Path(zeros_path).open()));zz=[mp.mpf(a['gamma']) for a in zz]
  for z in zz:
   if z<T:rows.append(Erow_and_dot(z,m,L)[0]);labels.append(dict(gamma=mp.nstr(z,dps),kind='line'))
 else:
  zd=json.loads(Path(dhzeros_path).read_text())
  for a in zd['critical_line_zeros']:
   z=mp.mpf(a['gamma'])
   if z<T:rows.append(Erow_and_dot(z,m,L)[0]);labels.append(dict(gamma=a['gamma'],kind='line'))
  for a in zd['off_line_pairs']:
   g=mp.mpf(a['gamma']);delta=mp.mpf(a['sigma_right'])-mp.mpf('.5')
   if g<T:
    vv=Erow_and_dot(g+mp.j*delta,m,L)[0]
    for kind in ['real','imag']:
     rows.append([mp.sqrt(2)*(mp.re(v) if kind=='real' else mp.im(v)) for v in vv]);labels.append(dict(gamma=a['gamma'],kind=kind,delta=mp.nstr(delta,dps)))
 if len(rows)!=q:raise RuntimeError(('active row mismatch',path,len(rows),q))
 E=mp.matrix(rows);rn=[mp.norm(E[i,:]) for i in range(q)];En=mp.matrix([[E[i,j]/rn[i] for j in range(m+1)] for i in range(q)])
 # Modified Gram-Schmidt isometry QR; no cutoff or source eigensystem.
 Z,R=mp.qr(En.T);U=Z[:,:q];Q=Z[:,q:];print('QR',world,m,q,time.monotonic()-start,flush=True)
 A=build_A(m,world,order);f=raw.get('complement_f',raw.get('physical_modal_coefficients'));f=mp.matrix(list(map(mp.mpf,f)));f/=mp.norm(f)
 fmt=lambda x:mp.nstr(x,dps-10)
 ser=lambda X:[[fmt(X[i,j]) for j in range(X.cols)] for i in range(X.rows)]
 out=dict(world=world,m=m,q=q,T=raw['T'],dps=dps,order=order,A=ser(A),E=ser(E),U=ser(U),Q=ser(Q),row_labels=labels,
 complement_f=[fmt(x) for x in f],complement_minimum=raw['complement_minimum'],complement_eigenvalues=[raw['complement_minimum']],
 source_path=str(path),source_replay_rayleigh=fmt((f.T*A*f)[0]),U_orthogonality_residual=fmt(mp.norm(U.T*U-mp.eye(q))),E_Q_residual=fmt(mp.norm(E*Q)),
 Pi_c_error=fmt(mp.norm(U*U.T*f-f)),seconds=time.monotonic()-start)
 dest=P/f'{world}_m{m}_q{q}_rebuild.json';dest.write_text(json.dumps(out)+'\n');print('BUILT',dest,out['source_replay_rayleigh'],out['seconds'],flush=True);return dest
if __name__=='__main__':build_case(*sys.argv[1:4],*map(int,sys.argv[4:]))
