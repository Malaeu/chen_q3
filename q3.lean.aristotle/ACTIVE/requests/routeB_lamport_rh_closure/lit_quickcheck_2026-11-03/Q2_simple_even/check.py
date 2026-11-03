"""Independent MP even/odd source matrices, finite diagnostics only."""
from pathlib import Path
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import sys,json,csv,time,argparse
from functools import lru_cache
import mpmath as mp
P=Path(__file__).resolve().parent

def coeffs(M,world):
 b=[mp.mpf(0)]*(M+1)
 if world=='dh':
  tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1);a=[0,1,tau,-tau,-1]
  for n in range(2,M+1):b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
 else:
  for n in range(2,M+1):
   for p in range(2,n+1):
    if n%p:continue
    k=n
    while k%p==0:k//=p
    if k==1:b[n]=mp.log(p)
    break
 return b

@lru_cache(None)
def nodes(order):
 gn,gw=mp.gauss_quadrature(order,'legendre');return [((mp.mpf(p)+(x+1)/2)/8,w/16) for p in range(8) for x,w in zip(gn,gw)]

def build(m,N,world,order):
 L=mp.log(m);bb=coeffs(m,world);alpha=mp.mpf('1.5') if world=='dh' else mp.mpf('.5')
 sm=[mp.mpf(0)]*(N+1);di=sm.copy();ps=sm.copy();pd=sm.copy()
 for y,w in nodes(order):
  x=L*y;wt=L*w*mp.exp(-alpha*x)/(-mp.expm1(-2*x));co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(N+1):
   sm[n]+=wt*sn;di[n]+=wt*(2*y+2*(1-y)*(1-cn)+(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 for k in range(2,m):
  if not bb[k]:continue
  y=mp.log(k)/L;wt=bb[k]/mp.sqrt(k);co=mp.cos(2*mp.pi*y);si=mp.sin(2*mp.pi*y);cn=mp.mpf(1);sn=mp.mpf(0)
  for n in range(N+1):ps[n]+=wt*sn;pd[n]+=wt*(2*(1-y)*cn-(sn/(mp.pi*n) if n else 0));cn,sn=cn*co-sn*si,sn*co+cn*si
 c=-mp.euler-mp.log(8*mp.pi/(5 if world=='dh' else 1))+(1 if world=='dh' else -1)*mp.pi/2
 z=mp.exp(-L/2);tail=mp.atanh(z)+(mp.atan(z) if world!='dh' else -mp.atan(z));beta=[sm[n]+ps[n] for n in range(N+1)];ds=[mp.mpf(1)]+[mp.sqrt(2)]*N
 E=mp.zeros(N+1);O=mp.zeros(N)
 for i in range(N+1):
  E[i,i]=c+di[i]+2*tail-pd[i]
  if i:O[i-1,i-1]=c+di[i]+2*tail-pd[i]-2*beta[i]/(mp.pi*i)
  for k in range(i+1,N+1):
   E[i,k]=E[k,i]=ds[i]*ds[k]/mp.pi*(i*beta[i]-k*beta[k])/(i*i-k*k)
   if i:O[i-1,k-1]=O[k-1,i-1]=2/mp.pi*(k*beta[i]-i*beta[k])/(i*i-k*k)
 if world!='dh':
  pole=mp.matrix([4*mp.sqrt(2)*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(N+1)])
  odd=mp.matrix([32*mp.pi*n*mp.sqrt(L)*mp.sinh(L/4)/(L*L+16*mp.pi**2*n*n) for n in range(1,N+1)]);E+=pole*pole.T;O-=odd*odd.T
 return E,O

def plant(E,O,L):
 N=E.rows-1;w=2*mp.pi/mp.log(2)+mp.j/4
 even=[2*mp.sin(w*L/2)/(mp.sqrt(L)*w)]+[mp.sqrt(2/L)*2*w*mp.sin(w*L/2)/(w*w-(2*mp.pi*n/L)**2) for n in range(1,N+1)]
 odd=[mp.sqrt(2/L)*2*(2*mp.pi*n/L)*mp.sin(w*L/2)/(w*w-(2*mp.pi*n/L)**2) for n in range(1,N+1)]
 return E+mp.matrix([[4*mp.re(x*y) for y in even] for x in even]),O+mp.matrix([[4*mp.re(x*y) for y in odd] for x in odd])

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--dps',type=int,default=120);ap.add_argument('--orders',nargs='+',type=int,default=[128,160]);ap.add_argument('--ms',nargs='+',type=int,default=[3,5,7,10,15,20,30,40,47,55]);a=ap.parse_args();mp.mp.dps=a.dps;start=time.monotonic();rows=[]
 for order in a.orders:
  for m in a.ms:
   Ns=[m,2*m if m<=20 else m+8];N=Ns[-1]
   Ze,Zo=build(m,N,'zeta',order);De,Do=build(m,N,'dh',order);Pe,Po=plant(Ze,Zo,mp.log(m))
   for world,E,O in [('zeta',Ze,Zo),('dh',De,Do),('plant',Pe,Po)]:
    for n in Ns:
     ev=mp.eigsy(E[:n+1,:n+1],eigvals_only=True);ov=mp.eigsy(O[:n,:n],eigvals_only=True);egap=ev[1]-ev[0];pgap=ov[0]-ev[0];floor=mp.mpf(10)**(-a.dps+15)*max(1,mp.norm(E),mp.norm(O))
     row=dict(world=world,m=m,N=n,L_length=mp.nstr(mp.log(m),35),Botha_halfwidth=mp.nstr(mp.log(m)/2,35),inside_Botha_claim=m<=mp.exp(4),dps=a.dps,order=order,lambda_even0=mp.nstr(ev[0],a.dps),lambda_even1=mp.nstr(ev[1],a.dps),lambda_odd0=mp.nstr(ov[0],a.dps),parity_gap=mp.nstr(pgap,a.dps),even_simple_gap=mp.nstr(egap,a.dps),roundoff_heuristic=mp.nstr(floor,15),finite_even_simple=pgap>floor and egap>floor,resolved_even_ground_sign='positive' if ev[0]>floor else ('negative' if ev[0]<-floor else 'UNRESOLVED'))
     rows.append(row);print(world,m,n,order,row['lambda_even0'][:25],row['lambda_odd0'][:25],row['finite_even_simple'],flush=True)
   (P/f'partial_dps{a.dps}.json').write_text(json.dumps(rows,indent=2)+'\n')
 with (P/f'spectra_dps{a.dps}.csv').open('w',newline='') as f:
  wr=csv.DictWriter(f,fieldnames=rows[0]);wr.writeheader();wr.writerows(rows)
 (P/f'run_dps{a.dps}.json').write_text(json.dumps(dict(status='DIAGNOSTIC_NEVER_A_PROOF',seconds=time.monotonic()-start,orders=a.orders,ms=a.ms,dps=a.dps,rows=len(rows)),indent=2)+'\n')
if __name__=='__main__':main()
