"""Independent mpmath m20 full-parity source/resolvent check; no new eigensolve."""
from pathlib import Path
import json,hashlib
import mpmath as mp
P=Path(__file__).resolve().parent;mp.mp.dps=80;m=20;L=mp.log(m);pi=mp.pi;ds=[mp.mpf(1)]+[mp.sqrt(2)]*m;om=[2*pi*n/L for n in range(m+1)]
g,w=mp.gauss_quadrature(128,'legendre');nodes=[(L*(p+(z+1)/2)/8,L*v/16) for p in range(8) for z,v in zip(g,w)]
t=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);period=[0,1,t,-t,-1]
def arithmetic(world):
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
 return b
rows=[]
for world in ('zeta','dh'):
 b=arithmetic(world);alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5');mom=[mp.mpf(0)]*(m+1);di=[mp.mpf(0)]*(m+1)
 for s,wt in nodes:
  r=s/L;j=mp.exp(-alpha*s)/(-mp.expm1(-2*s))
  for n in range(m+1):
   sn=mp.sin(2*pi*n*r);mom[n]+=wt*j*sn;di[n]+=wt*j*(2*r+4*(1-r)*mp.sin(pi*n*r)**2+(sn/(pi*n) if n else 0))
 ps=[mp.mpf(0)]*(m+1);pd=[mp.mpf(0)]*(m+1)
 for k in range(2,m):
  r=mp.log(k)/L;v=b[k]/mp.sqrt(k)
  for n in range(m+1):
   sn=mp.sin(2*pi*n*r);ps[n]+=v*sn;pd[n]+=v*(2*(1-r)*mp.cos(2*pi*n*r)-(sn/(pi*n) if n else 0))
 c=-mp.euler-mp.log(8*pi)-pi/2 if world=='zeta' else -mp.euler-mp.log(8*pi/5)+pi/2;z=mp.exp(-L/2);tail=mp.atanh(z)+(mp.atan(z) if world=='zeta' else -mp.atan(z));beta=[x+y for x,y in zip(mom,ps)];Ae=mp.zeros(m+1);Ao=mp.zeros(m)
 for n in range(m+1):Ae[n,n]=c+di[n]+2*tail-pd[n]
 for n in range(1,m+1):Ao[n-1,n-1]=Ae[n,n]-2*beta[n]/(pi*n)
 for i in range(m+1):
  for k in range(i+1,m+1):Ae[i,k]=Ae[k,i]=ds[i]*ds[k]/pi*(i*beta[i]-k*beta[k])/(i*i-k*k)
 for i in range(1,m+1):
  for k in range(i+1,m+1):Ao[i-1,k-1]=Ao[k-1,i-1]=2/pi*(k*beta[i]-i*beta[k])/(i*i-k*k)
 if world=='zeta':
  pe=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(m+1)]);po=mp.matrix([-32*pi*n*mp.sqrt(L)*mp.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(1,m+1)]);Ae+=pe*pe.T;Ao-=po*po.T
 p=P/f'profile_{world}_m20.json';d=json.loads(p.read_text());lam=mp.mpf(str(d['lambda_shift']));Te=Ae-lam*mp.eye(m+1);To=Ao-lam*mp.eye(m);be=mp.matrix([2*ds[n]*mp.sinh(L/2)/(mp.sqrt(L)*(1+om[n]**2)) for n in range(m+1)]);bo=mp.matrix([-2*mp.sqrt(2)*om[n]*mp.sinh(L/2)/(mp.sqrt(L)*(1+om[n]**2)) for n in range(1,m+1)]);ce=mp.lu_solve(Te,be);co=mp.lu_solve(To,bo);N=mp.sqrt(mp.fdot(be,ce)+mp.fdot(bo,co));ce/=N;co/=N;fe=mp.matrix(d['even_coefficients']);fo=mp.matrix(d['odd_coefficients']);delta=mp.sqrt(mp.norm(ce-fe)**2+mp.norm(co-fo)**2);rel=delta/mp.sqrt(mp.norm(ce)**2+mp.norm(co)**2);energy=mp.fdot(fe,Te*fe)+mp.fdot(fo,To*fo)
 fmt=lambda x:mp.nstr(x,65)
 rows.append(dict(world=world,m=20,dps=80,GL_order=128,panels=8,lambda_shift=fmt(lam),coefficient_maxabs=fmt(max(max(abs(x) for x in ce-fe),max(abs(x) for x in co-fo))),coefficient_relative_L2=fmt(rel),float_profile_Tnorm_squared_in_mp_source=fmt(energy),Tnorm_squared_error=fmt(abs(energy-1)),mp_linear_residual=fmt(max(mp.norm(Te*ce-be/N),mp.norm(To*co-bo/N))),profile_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 print(rows[-1],flush=True)
(P/'validation_audit_m20.json').write_text(json.dumps(dict(status='MP_NUMERICAL_CONSISTENCY_NOT_INTERVAL_CERTIFICATE',rows=rows,code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+'\n')
