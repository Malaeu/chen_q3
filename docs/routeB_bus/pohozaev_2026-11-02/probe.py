"""Finite N44 Pohozaev regular/atomic diagnostic; not infinite-window certification."""
import sys,json,csv,time
from pathlib import Path
import mpmath as mp
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(OUT.parent/'hadamard_2026-11-02/hadamard_convergence_2026-11-01'))
import convergence as c
DPS=mp.mp.dps;ORDER=c.ORDER;N=44;L=mp.log(8)
def fmt(x):return mp.nstr(x,DPS)
def theta_dh(x):
 xx=abs(x);u=mp.exp(2*xx);h=mp.mpf(0);hp=mp.mpf(0);n=1
 while mp.pi*n*n*u<=mp.mpf('2.4')*mp.mp.prec:
  a=mp.pi*n*n;z=a*u;ee=mp.exp(-z);t1=16*a*a*u**(mp.mpf(9)/4);t2=-24*a*u**(mp.mpf(5)/4)
  h+=(t1+t2)*ee;hp+=((mp.mpf(9)/2-2*z)*t1+(mp.mpf(5)/2-2*z)*t2)*ee;n+=1
 return h,xx*hp+h/2
K,Dright=c.matrices(L,N,'right',8);_,Dleft=c.matrices(L,N,'left',8)
E=c.even(K,N,N);ev,V=mp.eigsy(E);v=V[:,0];lam=ev[0]
a={0:v[0]}
for n in range(1,N+1):a[n]=a[-n]=v[n]/mp.sqrt(2)
bs=[mp.mpf(0)]+[4*a[n]/mp.pi*mp.fsum(a[i]/(i-n) for i in range(-N,N+1) if i!=n) for n in range(1,N+1)]
def Q(u):
 if u>=1:return mp.mpf(0)
 u=abs(u)
 co=mp.fsum(v[n]**2*mp.cos(2*mp.pi*n*u) for n in range(N+1))
 return 2*(1-u)*co+mp.fsum(bs[n]*mp.sin(2*mp.pi*n*u) for n in range(1,N+1))
def dQ(u):
 co=mp.fsum(v[n]**2*mp.cos(2*mp.pi*n*u) for n in range(N+1))
 return -2*co+mp.fsum((-4*mp.pi*n*(1-u)*v[n]**2*mp.sin(2*mp.pi*n*u)+2*mp.pi*n*bs[n]*mp.cos(2*mp.pi*n*u)) for n in range(1,N+1))
def j(s):return mp.exp(-s/2)/(-mp.expm1(-2*s))
def mj(s):return j(s)*(1-s/2-2*s/mp.expm1(2*s))
integ=L*mp.fsum(w*mj(L*y)*Q(y) for y,w in c.nodes)
u=mp.matrix([4*mp.sqrt(2)*(1 if n==0 else mp.sqrt(2))*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(N+1)])
du=mp.matrix([u[n]*(mp.mpf('1.5')/L+mp.coth(L/4)/4-2*L/(L*L+16*mp.pi**2*n*n)) for n in range(N+1)])
A=(v.T*u)[0];B=2*L*(v.T*du)[0]-A;pole=A*A+A*B;arch=-1-integ;Dreg=arch+pole
hfleft=L*(v.T*c.even(Dleft,N,N)*v)[0];hfright=L*(v.T*c.even(Dright,N,N)*v)[0]
P0left=mp.fsum(om*aa/L*dQ(aa/L) for n,aa,om in c.atoms if n<8)
P0right=P0left+c.mang(8)/mp.sqrt(8)*dQ(1)
edge2=(v[0]+mp.sqrt(2)*mp.fsum(v[n] for n in range(1,N+1)))**2/L
# L2 theta projection and dilation residual pairing.
hd=[theta_dh(L*(y-mp.mpf('.5'))) for y,w in c.nodes]
hcoef=mp.matrix([mp.sqrt(L)*(1 if n==0 else mp.sqrt(2))*mp.fsum(w*hd[i][0]*c.trig[n][i][1] for i,(y,w) in enumerate(c.nodes)) for n in range(N+1)])
dcoef=mp.matrix([mp.sqrt(L)*(1 if n==0 else mp.sqrt(2))*mp.fsum(w*hd[i][1]*c.trig[n][i][1] for i,(y,w) in enumerate(c.nodes)) for n in range(N+1)])
alpha=(v.T*hcoef)[0]/(hcoef.T*hcoef)[0];eres=v-alpha*hcoef;pair=(eres.T*dcoef)[0]
base=dict(dps=DPS,order=ORDER,N=N,L=fmt(L),lambda0=fmt(lam),gap=fmt(ev[1]-ev[0]),Q0=fmt(Q(0)),Q1=fmt(Q(1)),edge_squared=fmt(edge2),A=fmt(A),B=fmt(B),minus_one='-1',integral_mj_Q=fmt(integ),arch_regular=fmt(arch),pole_regular=fmt(pole),D_reg=fmt(Dreg),P0_left=fmt(P0left),P0_right=fmt(P0right),Dreg_plus_P0_left=fmt(Dreg+P0left),Dreg_plus_P0_right=fmt(Dreg+P0right),L_lambda_prime_HF_left=fmt(hfleft),L_lambda_prime_HF_right=fmt(hfright),identity_residual_left=fmt(Dreg+P0left-hfleft),identity_residual_right=fmt(Dreg+P0right-hfright),projection_h_norm2=fmt((hcoef.T*hcoef)[0]),residual_norm2=fmt((eres.T*eres)[0]),abs_e_Dh=fmt(abs(pair)),signed_e_Dh=fmt(pair),orthogonality_e_Ph=fmt((eres.T*hcoef)[0]))
(OUT/f'base_dps{DPS}_gl{ORDER}.json').write_text(json.dumps(base,indent=2)+'\n');print(json.dumps(base),flush=True)
rows=[]
for sign in(-1,1):
 tau=sign*mp.mpf('1e-6');side='left' if sign<0 else 'right'
 Pt=-mp.fsum(om*(Q(aa*mp.exp(-tau)/L)-Q(aa/L))/tau for n,aa,om in c.atoms)
 vals=[];frozen=[]
 for k in range(1,5):
  LL=L*mp.exp(k*tau);KK,_=c.matrices(LL,N);EE=c.even(KK,N,N)
  vals.append(mp.eigsy(EE,eigvals_only=True)[0]);frozen.append((v.T*EE*v)[0])
 fd=(vals[0]-lam)/tau
 fd4=(-25*lam+48*vals[0]-36*vals[1]+16*vals[2]-3*vals[3])/(12*tau)
 fr=(frozen[0]-lam)/tau;hf=hfleft if sign<0 else hfright
 r=dict(side=side,tau=fmt(tau),P_tau=fmt(Pt),Dreg_plus_Ptau=fmt(Dreg+Pt),L_lambda_prime_HF=fmt(hf),lambda_tau_FD_first_order=fmt(fd),lambda_tau_FD_fourth_order=fmt(fd4),relative_FD4_HF_error=fmt(abs(fd4-hf)/abs(hf)),frozen_energy_FD=fmt(fr),E_tau_measured=fmt(fr-Dreg-Pt),E_tau_over_tau=fmt((fr-Dreg-Pt)/tau),frozen_FD_minus_HF=fmt(fr-hf),Dreg_Ptau_minus_HF=fmt(Dreg+Pt-hf))
 rows.append(r);print(json.dumps(r),flush=True)
 (OUT/f'fd_dps{DPS}_gl{ORDER}.json').write_text(json.dumps(rows,indent=2)+'\n')
