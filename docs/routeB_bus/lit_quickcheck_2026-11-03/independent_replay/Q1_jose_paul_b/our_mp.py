"""Independent physical cosine/sine Galerkin source, numerical not interval."""
from pathlib import Path
import json,time,argparse,csv
import mpmath as mp
P=Path(__file__).resolve().parent

def build_window(L,N,order,panels,dps,Pmax=None):
 mp.mp.dps=dps;L=mp.mpf(L);m=int(mp.ceil(mp.exp(L)));pi=mp.pi;ds=[mp.mpf(1)]+[mp.sqrt(2)]*N
 g,w=mp.gauss_quadrature(order,'legendre');nodes=[(L*(p+(z+1)/2)/panels,L*v/(2*panels)) for p in range(panels) for z,v in zip(g,w)]
 tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);period=[0,1,tau,-tau,-1];out={}
 for world in ['zeta']:
  b=[mp.mpf(0)]*(m+1)
  for n in range(2,m+1):
   if world=='dh':b[n]=period[n%5]*mp.log(n)-mp.fsum(b[d]*period[(n//d)%5] for d in range(2,n) if n%d==0)
   else:
    for p in range(2,n+1):
     if n%p:continue
     q=n
     while q%p==0:q//=p
     if q==1 and (Pmax is None or p<=Pmax):b[n]=mp.log(p)
     break
  alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5');mom=[mp.mpf(0)]*(N+1);di=[mp.mpf(0)]*(N+1)
  for s,wt in nodes:
   r=s/L;j=mp.exp(-alpha*s)/(-mp.expm1(-2*s));ang=2*pi*r;co=mp.cos(ang);si=mp.sin(ang);cn=mp.mpf(1);sn=mp.mpf(0)
   for n in range(N+1):
    mom[n]+=wt*j*sn;di[n]+=wt*j*(2*r+2*(1-r)*(1-cn)+(sn/(pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
  ps=[mp.mpf(0)]*(N+1);pd=[mp.mpf(0)]*(N+1)
  for k in range(2,m):
   if mp.log(k)>=L:continue
   r=mp.log(k)/L;v=b[k]/mp.sqrt(k)
   for n in range(N+1):
    sn=mp.sin(2*pi*n*r);ps[n]+=v*sn;pd[n]+=v*(2*(1-r)*mp.cos(2*pi*n*r)-(sn/(pi*n) if n else 0))
  c=-mp.euler-mp.log(8*pi)-pi/2 if world=='zeta' else -mp.euler-mp.log(8*pi/5)+pi/2;z=mp.exp(-L/2);tail=mp.atanh(z)+(mp.atan(z) if world=='zeta' else -mp.atan(z));beta=[x+y for x,y in zip(mom,ps)];Ae=mp.zeros(N+1);Ao=mp.zeros(N)
  for n in range(N+1):Ae[n,n]=c+di[n]+2*tail-pd[n]
  for n in range(1,N+1):Ao[n-1,n-1]=Ae[n,n]-2*beta[n]/(pi*n)
  for i in range(N+1):
   for k in range(i+1,N+1):Ae[i,k]=Ae[k,i]=ds[i]*ds[k]/pi*(i*beta[i]-k*beta[k])/(i*i-k*k)
  for i in range(1,N+1):
   for k in range(i+1,N+1):Ao[i-1,k-1]=Ao[k-1,i-1]=2/pi*(k*beta[i]-i*beta[k])/(i*i-k*k)
  if world=='zeta':
   pe=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(N+1)]);po=mp.matrix([-32*pi*n*mp.sqrt(L)*mp.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(1,N+1)]);Ae+=pe*pe.T;Ao-=po*po.T
  out[world]=(Ae,Ao)
 return out['zeta']

if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('--N',type=int,default=32);a.add_argument('--dps',type=int,default=100);a.add_argument('--order',type=int,default=96);q=a.parse_args();mp.mp.dps=q.dps
 cases=[('m3',mp.log(3),None),('exp1.6',mp.mpf('1.6'),None),('m5',mp.log(5),None),('m7',mp.log(7),None),('P2_low',mp.mpf('1.1140'),2),('P2_up',mp.mpf('1.1147'),2)]
 rows=[]
 for label,L,pm in cases:
  Ae,Ao=build_window(L,q.N,q.order,8,q.dps,pm);ev=mp.eigsy(Ae,eigvals_only=True);od=mp.eigsy(Ao,eigvals_only=True)
  row=dict(label=label,L=mp.nstr(L,80),P=pm,N=q.N,dps=q.dps,order=q.order,panels=8,even=mp.nstr(ev[0],80),odd=mp.nstr(od[0],80),ratio=mp.nstr(od[0]/ev[0],80));rows.append(row);print(json.dumps(row),flush=True)
 (Path(__file__).parent/f'our_N{q.N}_dps{q.dps}.json').write_text(json.dumps(rows,indent=2)+'\n')
