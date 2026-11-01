"""80-digit floating Hadamard diagnostic. No interval certificate."""
import json,time,sys
from functools import lru_cache
from pathlib import Path
import mpmath as mp
mp.mp.dps=80
OUT=Path(__file__).resolve().parent
ORDER=int(sys.argv[1]) if len(sys.argv)>1 else 64
gn,gw=mp.gauss_quadrature(ORDER,'legendre')
nodes=[]
for p in range(8):
 for z,w in zip(gn,gw):nodes.append(((mp.mpf(p)+(z+1)/2)/8,w/16))
trig={n:[(mp.sin(2*mp.pi*n*y),mp.cos(2*mp.pi*n*y)) for y,w in nodes] for n in range(17)}
def mang(k):
 for p in range(2,k+1):
  if any(p%d==0 for d in range(2,int(p**.5)+1)):continue
  a=p
  while a<k:a*=p
  if a==k:return mp.log(p)
 return mp.mpf(0)
atoms=[(k,mp.log(k),mang(k)/mp.sqrt(k)) for k in range(2,17) if mang(k)]
@lru_cache(maxsize=40)
def matrices(L,N,side=None,threshold=None,der=True):
 mom=[mp.mpf(0)]*(N+1);dm=mom.copy();di=mom.copy();dd=mom.copy()
 for ni,(y,w) in enumerate(nodes):
  x=L*y;sh=mp.sinh(x);ex=mp.exp(x/2);base=L*ex/(2*sh)
  db=base*(1/L+y/2-y*mp.coth(x))
  fac=L/sh;df=fac*(1/L-y*mp.coth(x))
  for n in range(N+1):
   sn,cs=trig[n][ni]
   if n:mom[n]+=w*base*sn;dm[n]+=w*db*sn
   v=ex*(1-y)*cs-1
   di[n]+=w*fac*v;dd[n]+=w*(df*v+fac*ex*y/2*(1-y)*cs)
 def mm(n):return mom[abs(n)]*(1 if n>=0 else -1)
 def md(n):return dm[abs(n)]*(1 if n>=0 else -1)
 const=mp.euler+mp.log(4*mp.pi*mp.tanh(L/2));dc=1/mp.sinh(L)
 K=mp.matrix(2*N+1);D=mp.matrix(2*N+1)
 selected=[]
 for k,x,c in atoms:
  include=x<L
  if threshold==k:include=side=='right'
  if include:selected.append((x,c,{n:(2*mp.pi*n*x/L,mp.sin(2*mp.pi*n*x/L),mp.cos(2*mp.pi*n*x/L)) for n in range(-N,N+1)}))
 A=32*L*mp.sinh(L/4)**2
 Ap=32*mp.sinh(L/4)**2+16*L*mp.sinh(L/4)*mp.cosh(L/4)
 for ii,n in enumerate(range(-N,N+1)):
  for jj in range(ii,2*N+1):
   v=jj-N;B=L*L-16*mp.pi**2*v*n;C=L*L+16*mp.pi**2*v*v;E=L*L+16*mp.pi**2*n*n
   pole=A*B/(C*E);dp=(Ap*B+2*L*A)/(C*E)-pole*(2*L/C+2*L/E)
   arch=const+di[abs(n)] if n==v else (mm(v)-mm(n))/(mp.pi*(n-v))
   da=dc+dd[abs(n)] if n==v else (md(v)-md(n))/(mp.pi*(n-v))
   prime=mp.mpf(0);pd=mp.mpf(0)
   for x,c,ts in selected:
    an,sn,cn=ts[n];av,sv,cv=ts[v]
    if n==v:
     q=2*(1-x/L)*cn
     qd=2*x/L**2*cn+2*(1-x/L)*sn*an/L
    else:
     q=(sv-sn)/(mp.pi*(n-v))
     qd=(-av*cv+an*cn)/(L*mp.pi*(n-v))
    prime+=c*q;pd+=c*qd
   K[ii,jj]=K[jj,ii]=pole-arch-prime
   D[ii,jj]=D[jj,ii]=dp-da-pd
 return K,D
def even(K,N,fullN):
 inds=list(range(-N,N+1));E=mp.zeros(2*fullN+1,N+1);E[fullN,0]=1
 for n in range(1,N+1):E[fullN+n,n]=E[fullN-n,n]=1/mp.sqrt(2)
 return E.T*K*E
def eig(K,N,fullN,vec=False):
 B=even(K,N,fullN)
 if vec:
  ev,V=mp.eigsy(B);return ev[0],V[:,0],ev[1]-ev[0]
 return mp.eigsy(B,eigvals_only=True)[0]
def fmt(x):return mp.nstr(x,45)
def row(L,N,K,D,NN,tag,step=mp.mpf('1e-7'),side=None,threshold=None):
 lam,v,gap=eig(K,N,NN,True);hf=(v.T*even(D,N,NN)*v)[0]
 vals=[]
 offsets=[-2,-1,1,2] if side is None else ([0,1,2,3,4] if side=='right' else [0,-1,-2,-3,-4])
 for j in offsets:
  kk,_=matrices(L+j*step,NN,side,threshold)
  vals.append(eig(kk,N,NN))
 if side is None:fd=(vals[0]-8*vals[1]+8*vals[2]-vals[3])/(12*step)
 else:fd=(-25*vals[0]+48*vals[1]-36*vals[2]+16*vals[3]-3*vals[4])/(12*step)*(1 if side=='right' else -1)
 return dict(L=fmt(L),N=N,tag=tag,side=side,threshold=threshold,lambda0=fmt(lam),gap=fmt(gap),derivative_HF=fmt(hf),derivative_FD=fmt(fd),derivative_sign=int(mp.sign(hf)),r_HF=fmt(-hf/lam),r_FD=fmt(-fd/lam),relative_derivative_difference=fmt(abs(fd-hf)/max(abs(hf),mp.mpf('1e-70'))))
def main():
 lo=mp.log(8);hi=mp.log(16);points={fmt(lo):[lo,'grid',8],fmt(hi):[hi,'endpoint',16]}
 j=1
 while lo+j*mp.mpf('.01')<hi:
  L=lo+j*mp.mpf('.01');points[fmt(L)]=[L,'grid',None];j+=1
 for k in range(8,17):
  L=mp.log(k);points[fmt(L)]=[L,'threshold',k]
  for sg in (-1,1):
   t=L+sg*mp.mpf('.0001')
   if lo<=t<=hi:points[fmt(t)]=[t,'threshold_offset',None]
 start=time.monotonic()
 previous=[]
 resultpath=OUT/f'results_gl{ORDER}.jsonl'
 if resultpath.exists():previous=[json.loads(s) for s in resultpath.read_text().splitlines()]
 counts={}
 for rr in previous:counts[rr['L']]=counts.get(rr['L'],0)+1
 with resultpath.open('a') as out:
  for L,tag,k in sorted(points.values()):
   literal=k if k else int(mp.floor(mp.exp(L)))
   expected=2*len(set([8,12,literal,literal-1])) if k else len(set([8,12,literal]))
   if counts.get(fmt(L),0)==expected:continue
   NN=max(12,literal);K,D=matrices(L,NN)
   for N in sorted(set([8,12,literal])) if not k else []:
    rr=row(L,N,K,D,NN,tag,threshold=k)
    rr['literal_comparison']=N==literal;out.write(json.dumps(rr)+'\n');out.flush()
   if k:
    for side in ('left','right'):
     K,D=matrices(L,NN,side,k)
     for N in sorted(set([8,12,literal,literal-1])):
      rr=row(L,N,K,D,NN,tag,side=side,threshold=k)
      rr['literal_comparison']=N==(literal if side=='right' else literal-1);out.write(json.dumps(rr)+'\n');out.flush()
   print('POINT',fmt(L),tag,'elapsed',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
