"""Full-parity finite Suzuki deficiency prototypes, not continuum certification."""
from pathlib import Path
import json,time,sys
import numpy as np
from scipy.special import roots_legendre
from scipy.linalg import eigh,cho_factor,cho_solve
P=Path(__file__).resolve().parent
MAX=240
cDH=(np.sqrt(10-2*np.sqrt(5))-2)/(np.sqrt(5)-1)
a=np.array([0.,1.,cDH,-cDH,-1.])
def coefficients(world,M):
 b=np.zeros(M+1)
 if world=='dh':
  for n in range(2,M+1):b[n]=a[n%5]*np.log(n)-sum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
 else:
  for n in range(2,M+1):
   for p in range(2,n+1):
    if n%p:continue
    k=n
    while k%p==0:k//=p
    if k==1:b[n]=np.log(p)
    break
 return b
B={w:coefficients(w,MAX) for w in ['zeta','dh']}
gn,gw=roots_legendre(96);ys=np.concatenate([(p+(gn+1)/2)/8 for p in range(8)]);ws=np.tile(gw/16,8);ns=np.arange(MAX+1);COS=np.cos(2*np.pi*ys[:,None]*ns);SIN=np.sin(2*np.pi*ys[:,None]*ns)
def build(world,m):
 L=np.log(m);n=np.arange(m+1);ds=np.r_[1.,np.repeat(np.sqrt(2),m)];x=L*ys;alpha=.5 if world=='zeta' else 1.5;wt=L*ws*np.exp(-alpha*x)/(-np.expm1(-2*x));sm=wt@SIN[:,:m+1]
 sint= SIN[:,:m+1]/(np.pi*np.where(n==0,1,n));sint[:,0]=0
 di=wt@(2*ys[:,None]+2*(1-ys[:,None])*(1-COS[:,:m+1])+sint)
 atoms=np.flatnonzero(B[world][2:m])+2;s=np.log(atoms);weights=B[world][atoms]/np.sqrt(atoms);ph=2*np.pi*s[:,None]*n/L;sn=np.sin(ph);co=np.cos(ph);ps=weights@sn;pd=weights@(2*(1-s[:,None]/L)*co-sn/(np.pi*np.where(n==0,1,n)))
 c=-np.euler_gamma-np.log(8*np.pi)-np.pi/2 if world=='zeta' else -np.euler_gamma-np.log(8*np.pi/5)+np.pi/2
 z=np.exp(-L/2);tail=np.arctanh(z)+(np.arctan(z) if world=='zeta' else -np.arctan(z));beta=sm+ps;Ae=np.diag(c+di+2*tail-pd);Ao=np.diag(c+di[1:]+2*tail-pd[1:]-2*beta[1:]/(np.pi*n[1:]))
 for i in range(m+1):
  for k in range(i+1,m+1):Ae[i,k]=Ae[k,i]=ds[i]*ds[k]/np.pi*(i*beta[i]-k*beta[k])/(i*i-k*k)
 for i in range(1,m+1):
  for k in range(i+1,m+1):Ao[i-1,k-1]=Ao[k-1,i-1]=2/np.pi*(k*beta[i]-i*beta[k])/(i*i-k*k)
 if world=='zeta':
  pole=4*np.sqrt(2)*ds*L**1.5*np.sinh(L/4)/(L*L+16*np.pi**2*n*n);Ae+=np.outer(pole,pole)
  odd=32*np.pi*n[1:]*np.sqrt(L)*np.sinh(L/4)/(L*L+16*np.pi**2*n[1:]**2);Ao-=np.outer(odd,odd)
 bound=c-2*np.sum(np.abs(B[world][2:m+1])/np.sqrt(np.arange(2,m+1)))-(2*np.sinh(L/2)-L if world=='zeta' else 0)
 return Ae,Ao,bound

def cell(world,m):
 start=time.monotonic();Ae,Ao,bound=build(world,m);mine=float(eigh(Ae,subset_by_index=[0,0],eigvals_only=True)[0]);mino=float(eigh(Ao,subset_by_index=[0,0],eigvals_only=True)[0]);lam=-1. if world=='zeta' else min(mine,mino)-1;L=np.log(m);omega=2*np.pi*np.arange(m+1)/L;ds=np.r_[1.,np.repeat(np.sqrt(2),m)]
 be=2*ds*np.sinh(L/2)/(np.sqrt(L)*(1+omega**2));bo=-2*np.sqrt(2)*omega[1:]*np.sinh(L/2)/(np.sqrt(L)*(1+omega[1:]**2))
 ce=cho_solve(cho_factor(Ae-lam*np.eye(m+1),lower=True),be);co=cho_solve(cho_factor(Ao-lam*np.eye(m),lower=True),bo);norm=np.sqrt(be@ce+bo@co)
 result=dict(status='FINITE_GALERKIN_PROTOTYPE_NOT_SUZUKI_THEOREM',world=world,m=m,L=L,a=L/2,Omega=2*np.pi*m/L,lambda_shift=lam,full_finite_minimum=min(mine,mino),even_minimum=mine,odd_minimum=mino,finite_T_gap=min(mine,mino)-lam,source_lower_bound=bound,source_admissible_shift=bound-1,main_shift_continuum_admissibility='NOT_VERIFIED_BY_FINITE_POSITIVITY',raw_T_norm=norm,even_coefficients=(ce/norm).tolist(),odd_coefficients=(co/norm).tolist(),linear_even_residual=float(np.linalg.norm((Ae-lam*np.eye(m+1))@ce-be)),linear_odd_residual=float(np.linalg.norm((Ao-lam*np.eye(m))@co-bo)),normalized_T_norm_squared=float(((ce@(Ae-lam*np.eye(m+1))@ce)+(co@(Ao-lam*np.eye(m))@co))/norm**2),vminus_rule='same even coefficients; negate odd coefficients',source_b_coefficients=B[world][:m+1].tolist(),seconds=time.monotonic()-start)
 return result
if __name__=='__main__':
 ms=list(map(int,sys.argv[1:])) if len(sys.argv)>1 else range(20,241);allrows=[]
 for m in ms:
  for world in ['zeta','dh']:
   r=cell(world,m);allrows.append(r)
   if m in [20,40,60,80,120,160,200,240]:(P/f'profile_{world}_m{m}.json').write_text(json.dumps(r,indent=2)+'\n')
  (P/'all_cells.json').write_text(json.dumps(allrows,indent=2)+'\n')
  print(m,[(r['world'],r['full_finite_minimum'],r['finite_T_gap']) for r in allrows[-2:]],flush=True)
