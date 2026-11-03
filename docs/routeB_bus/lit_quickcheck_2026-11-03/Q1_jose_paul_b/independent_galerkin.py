"""DIAGNOSTIC_NEVER_A_PROOF. Physical-source Fourier Galerkin, both poles.
Independent of foreign Legendre/envelope code; adapted literal matrix_K formulas.
Finite-sector minima are upper approximations, not whole-window lower bounds.
"""
import mpmath as mp, json, time, sys
from pathlib import Path
mp.mp.dps=80
OUT=Path(__file__).resolve().parent

def matrix(L,N,order,P=None):
 gn,gw=mp.gauss_quadrature(order,'legendre')
 moments=[mp.mpf(0)]*(N+1);diags=[mp.mpf(0)]*(N+1)
 for panel in range(8):
  for z,w in zip(gn,gw):
   x=L*(panel+(z+1)/2)/8; wt=L*w/16; kernel=mp.exp(x/2)/(2*mp.sinh(x))
   for n in range(N+1):
    t=2*mp.pi*n*x/L
    moments[n]+=wt*kernel*mp.sin(t)
    diags[n]+=wt*(kernel*2*(1-x/L)*mp.cos(t)-1/mp.sinh(x))
 pp=[]
 for p in range(2,int(mp.floor(mp.exp(L)))+1):
  if any(p%d==0 for d in range(2,int(p**.5)+1)):continue
  if P is not None and p>P:continue
  k=p
  while mp.log(k)<L:
   pp.append((mp.log(k),mp.log(p)/mp.sqrt(k)));k*=p
 def sm(n):return mp.sign(n)*moments[abs(n)]
 const=mp.euler+mp.log(4*mp.pi*mp.tanh(L/2))
 def entry(n,k):
  pole=32*L*mp.sinh(L/4)**2*(L**2-16*mp.pi**2*n*k)/((L**2+16*mp.pi**2*n*n)*(L**2+16*mp.pi**2*k*k))
  arch=const+diags[abs(n)] if n==k else (sm(k)-sm(n))/(mp.pi*(n-k))
  def q(x):return 2*(1-x/L)*mp.cos(2*mp.pi*n*x/L) if n==k else (mp.sin(2*mp.pi*k*x/L)-mp.sin(2*mp.pi*n*x/L))/(mp.pi*(n-k))
  return pole-arch-mp.fsum(w*q(x) for x,w in pp)
 even=mp.matrix(N+1);odd=mp.matrix(N)
 even[0,0]=entry(0,0)
 for i in range(1,N+1):
  even[0,i]=even[i,0]=mp.sqrt(2)*entry(0,i)
  for j in range(1,i+1):
   e,o=entry(i,j),entry(i,-j)
   even[i,j]=even[j,i]=e+o;odd[i-1,j-1]=odd[j-1,i-1]=e-o
 return [mp.eigsy(A,eigvals_only=True)[0] for A in (even,odd)]

if __name__=='__main__':
 N=int(sys.argv[1]) if len(sys.argv)>1 else 24;order=int(sys.argv[2]) if len(sys.argv)>2 else 48
 rows=[]
 for label,L,P in [('m3',mp.log(3),None),('mexp1.6',mp.mpf('1.6'),None),('m5',mp.log(5),None),('m7',mp.log(7),None),('P2lower',mp.mpf('1.1140'),2),('P2upper',mp.mpf('1.1147'),2)]:
  t=time.monotonic();ev=matrix(L,N,order,P)
  row=dict(label=label,L=mp.nstr(L,75),N=N,order=order,dps=80,semilocal_P=P,even_min=mp.nstr(ev[0],60),odd_min=mp.nstr(ev[1],60),seconds=time.monotonic()-t)
  rows.append(row);print(json.dumps(row),flush=True)
  (OUT/f'independent_N{N}_gl{order}.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',rows=rows),indent=2)+'\n')
