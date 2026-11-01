"""Literal even CCM lowcluster core; DIAGNOSTIC_NEVER_A_PROOF.
Matrix formula copied from pinned full_center_probe via the validated Hadamard builder.
No high tail mode is added to the active N=m carrier.
"""
import sys,json,time
from pathlib import Path
import mpmath as mp
OUT=Path(__file__).resolve().parent

def mangoldt(n):
 for p in range(2,n+1):
  if any(p%d==0 for d in range(2,int(p**.5)+1)):continue
  q=p
  while q<n:q*=p
  if q==n:return mp.log(p)
 return mp.mpf(0)

def setup(dps,order):
 mp.mp.dps=dps
 # Existing literal builder, copied into deliverable as matrix_core.py.
 sys.argv=['lowcluster',str(order),str(dps)]
 import matrix_core as src
 src.atoms=[(n,mp.log(n),mangoldt(n)/mp.sqrt(n)) for n in range(2,25) if mangoldt(n)]
 return src

def theta(x):
 x=abs(x);u=mp.exp(2*x);s=mp.mpf(0);n=1
 aa=16*mp.pi**2*mp.exp(mp.mpf('4.5')*x);bb=24*mp.pi*mp.exp(mp.mpf('2.5')*x)
 while mp.pi*n*n*u<mp.mpf('2.5')*mp.mp.prec:
  s+=(aa*n**4-bb*n*n)*mp.exp(-mp.pi*n*n*u);n+=1
 return s

def xiH(t):
 s=mp.mpf('.5')+mp.j*t
 return mp.re(2*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s))

def beta(n,L,atoms):
 if n==0:return mp.mpf(0)
 om=2*mp.pi*n/L
 # Exact positive-series identity, infinite part summed by digamma.
 val=mp.im(mp.digamma(mp.mpf('.25')+mp.j*om/2))/2
 r=0
 while True:
  c=mp.mpf('.5')+2*r;term=om*mp.exp(-c*L)/(c*c+om*om);val-=term;r+=1
  if abs(term)<mp.eps**mp.mpf('1.1'):break
 return val+mp.fsum(w*mp.sin(om*a) for k,a,w in atoms)

def compute(m,dps=100,order=128,cutoffs=(128,160,192)):
 start=time.monotonic();src=setup(dps,order);L=mp.log(m);N=m
 K,_=src.matrices(L,N);A=src.even(K,N,N);ev,V=mp.eigsy(A)
 hd=[theta(L*(y-mp.mpf('.5'))) for y,w in src.nodes]
 h=mp.matrix([mp.sqrt(L)*(1 if n==0 else mp.sqrt(2))*mp.fsum(w*hd[i]*src.trig[n][i][1] for i,(y,w) in enumerate(src.nodes)) for n in range(m+1)])
 Z=mp.norm(h);u=h/Z
 for i in range(m+1):
  # Deterministic sign: largest basis coordinate positive; bottom positive theta overlap.
  pivot=max(range(m+1),key=lambda j:abs(V[j,i]))
  if (i==0 and (V[:,i].T*h)[0]<0) or (i>0 and V[pivot,i]<0):
   for j in range(m+1):V[j,i]=-V[j,i]
 aa=V.T*u
 atoms=[(n,mp.log(n),mangoldt(n)/mp.sqrt(n)) for n in range(2,m+1) if mangoldt(n)]
 M=max(cutoffs);betas=[beta(n,L,atoms) for n in range(M+1)]
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*M
 pole=[4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(M+1)]
 def row(n,j):return pole[n]*pole[j]+ds[n]*ds[j]/mp.pi*(n*betas[n]-j*betas[j])/(n*n-j*j)
 ctrl=max(abs(row(n,j)-A[n,j]) for n in range(m+1) for j in range(n))
 Fbasis=mp.zeros(m+1,1);partials=[]
 for n in range(m+1,M+1):
  c=mp.sqrt(2/L)*(-1)**n*xiH(2*mp.pi*n/L)
  for j in range(m+1):Fbasis[j]+=c*row(n,j)
  if n in cutoffs:partials.append([mp.nstr(x,dps) for x in V.T*Fbasis]);print('F',m,dps,n,flush=True)
 data=dict(m=m,dps=dps,order=order,L=str(L),Z=str(Z),entry_ctrl=str(ctrl),lambda_=[str(x) for x in ev],a=[str(x) for x in aa],F=[str(x) for x in V.T*Fbasis],Fbasis=[str(x) for x in Fbasis],F_cutoffs=list(cutoffs),F_partials=partials,h=[str(x) for x in h],A=[[str(A[i,j]) for j in range(m+1)] for i in range(m+1)],V=[[str(V[i,j]) for j in range(m+1)] for i in range(m+1)],eigen_residual=str(mp.norm(A*V-V*mp.diag(ev))),elapsed=time.monotonic()-start)
 try:
  from ladder import compute_ladder
  data['ladder']=compute_ladder(m,V,src.nodes,dps)
 except ImportError:pass
 (OUT/f'core_m{m}_dps{dps}_gl{order}.json').write_text(json.dumps(data,indent=2)+'\n')
 print('DONE CORE',m,dps,ctrl,flush=True)
 return data

if __name__=='__main__':
 dps=int(sys.argv[1]);order=int(sys.argv[2]);ms=[int(x) for x in sys.argv[3:]]
 for m in ms:compute(m,dps,order)
