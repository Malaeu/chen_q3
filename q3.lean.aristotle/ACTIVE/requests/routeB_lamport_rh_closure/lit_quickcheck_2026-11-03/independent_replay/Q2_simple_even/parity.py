"""Independent physical cosine/sine Galerkin source, numerical not interval."""
from pathlib import Path
import json,time,argparse,csv
import mpmath as mp
P=Path(__file__).resolve().parent

def build(m,N,order,panels,dps):
 mp.mp.dps=dps;L=mp.log(m);pi=mp.pi;ds=[mp.mpf(1)]+[mp.sqrt(2)]*N
 g,w=mp.gauss_quadrature(order,'legendre');nodes=[(L*(p+(z+1)/2)/panels,L*v/(2*panels)) for p in range(panels) for z,v in zip(g,w)]
 tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);period=[0,1,tau,-tau,-1];out={}
 for world in ['zeta','dh']:
  b=[mp.mpf(0)]*(m+1)
  for n in range(2,m+1):
   if world=='dh':b[n]=period[n%5]*mp.log(n)-mp.fsum(b[d]*period[(n//d)%5] for d in range(2,n) if n%d==0)
   else:
    for p in range(2,n+1):
     if n%p:continue
     q=n
     while q%p==0:q//=p
     if q==1:b[n]=mp.log(p)
     break
  alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5');mom=[mp.mpf(0)]*(N+1);di=[mp.mpf(0)]*(N+1)
  for s,wt in nodes:
   r=s/L;j=mp.exp(-alpha*s)/(-mp.expm1(-2*s));ang=2*pi*r;co=mp.cos(ang);si=mp.sin(ang);cn=mp.mpf(1);sn=mp.mpf(0)
   for n in range(N+1):
    mom[n]+=wt*j*sn;di[n]+=wt*j*(2*r+2*(1-r)*(1-cn)+(sn/(pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
  ps=[mp.mpf(0)]*(N+1);pd=[mp.mpf(0)]*(N+1)
  for k in range(2,m):
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
 w=2*pi/mp.log(2)+mp.j/4
 ce=mp.matrix([2*ds[n]*w*mp.sin(w*L/2)/(mp.sqrt(L)*(w*w-(2*pi*n/L)**2)) for n in range(N+1)])
 so=mp.matrix([2*mp.sqrt(2)*(2*pi*n/L)*mp.sin(w*L/2)/(mp.sqrt(L)*(w*w-(2*pi*n/L)**2)) for n in range(1,N+1)])
 out['plant']=(out['zeta'][0]+(4*ce*ce.T).apply(mp.re),out['zeta'][1]+(4*so*so.T).apply(mp.re))
 return out

def run(m,factor,dps,order,panels):
 start=time.monotonic();N=m*factor;mat=build(m,N,order,panels,dps);rows=[]
 for world,(Ae,Ao) in mat.items():
  ev=mp.eigsy(Ae,eigvals_only=True);od=mp.eigsy(Ao,eigvals_only=True);fmt=lambda x:mp.nstr(x,60)
  r=dict(m=m,halfwidth=fmt(mp.log(m)/2),N=N,dps=dps,GL_order=order,panels=panels,world=world,even0=fmt(ev[0]),even1=fmt(ev[1]),odd0=fmt(od[0]),odd_even_gap=fmt(od[0]-ev[0]),even_gap=fmt(ev[1]-ev[0]),global_even=bool(ev[0]<od[0]),finite_simple=bool(ev[1]>ev[0] and od[0]>ev[0]));rows.append(r);print(m,N,world,fmt(ev[0]),fmt(od[0]),flush=True)
 rec=dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,rows=rows);(P/f'm{m}_N{N}_q{order}_p{panels}_dps{dps}.json').write_text(json.dumps(rec,indent=2)+'\n')
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--m',type=int,nargs='+',default=[3,5,7,10,15,20,30,40,47,55]);a.add_argument('--factor',type=int,default=1);a.add_argument('--dps',type=int,default=70);a.add_argument('--order',type=int,default=48);a.add_argument('--panels',type=int,default=8);q=a.parse_args()
 for m in q.m:run(m,q.factor,q.dps,q.order,q.panels)
