"""Independent arithmetic checkpoint and convex-cell-minimum scan; NOT intervals."""
from pathlib import Path
import numpy as np
import mpmath as mp
import json,csv,time,argparse,math
P=Path(__file__).resolve().parent

def main(N=10_000_000):
 start=time.monotonic();mp.mp.dps=85;D=np.longdouble
 alpha=(mp.log(8*mp.pi)+mp.euler+mp.pi/2)/2;C0=mp.pi**2/4+2*mp.catalan-8
 aa=D(str(alpha));cc=D(str(C0))
 sieve=np.ones(N+1,dtype=bool);sieve[:2]=False
 for p in range(2,math.isqrt(N)+1):
  if sieve[p]:sieve[p*p::p]=False
 primes=np.flatnonzero(sieve);nn=[primes];lam=[np.log(primes.astype(D))]
 extra=[];base=[]
 for p in primes[primes<=math.isqrt(N)]:
  k=int(p)*int(p)
  while k<=N:extra.append(k);base.append(int(p));k*=int(p)
 nn.append(np.array(extra,dtype=np.int64));lam.append(np.log(np.array(base,dtype=D)))
 q=np.concatenate(nn);ll=np.concatenate(lam);order=np.argsort(q);q=q[order];ll=ll[order]
 x=q.astype(D);t=np.log(x);weights=ll/np.sqrt(x);W=np.cumsum(weights,dtype=D);M=np.cumsum(weights*t,dtype=D)
 def rem(x,derivative=False):
  x=np.asarray(x,dtype=D);power=x**D('-2.5');total=np.zeros_like(x)
  for k in range(1,56):
   total+=(2 if derivative else 4)*power/((4*k+1) if derivative else (4*k+1)**2);power/=x*x
  return total
 def smooth(x):return 4*np.sqrt(x)-aa*np.log(x)+cc-rem(x)
 event=smooth(x)-W*t+M
 hi=np.r_[x[1:],D(N)];der_right=2*np.sqrt(x)-aa+rem(x,True)-W;der_hi=2*np.sqrt(hi)-aa+rem(hi,True)-W
 active=(der_right<0)&(der_hi>0)&(hi>x);idx=np.flatnonzero(active);y=(W[idx]+aa)/2
 for _ in range(4):
  xx=y*y;yy=2*y-aa+rem(xx,True)-W[idx];dy=2-2*y**(-6)/(1-y**(-4));y-=yy/dy
 xr=y*y;tr=np.log(xr);interior=smooth(xr)-W[idx]*tr+M[idx]
 assert np.all(xr>x[idx]) and np.all(xr<hi[idx])
 endpoint=smooth(D(N))-W[-1]*np.log(D(N))+M[-1]
 selected_indices=set(map(int,np.argsort(event)[:20]))|set(map(int,idx[np.argsort(interior)[:20]]))
 exact_prefix={};ww=mp.mpf(0);mm=mp.mpf(0)
 for i,(nn,lnp) in enumerate(zip(q,ll)):
  n=int(nn);pr=round(float(np.exp(lnp)));w=mp.log(pr)/mp.sqrt(n);ww+=w;mm+=w*mp.log(n)
  if i in selected_indices:exact_prefix[i]=(ww,mm)
  if i>=max(selected_indices):break
 rows=[]
 for kind,values,coords,indices in [('event',event,t,np.arange(len(t))),('interior',interior,tr,idx)]:
  selected=np.argsort(values)[:20]
  for j in selected:
   i=int(indices[j]);tt=mp.mpf(str(coords[j]))
   # Independent high-precision sum over every active prime power.
   exact=4*mp.exp(tt/2)-alpha*tt+C0
   exact-=4*mp.fsum(mp.exp(-(4*k+1)*tt/2)/(4*k+1)**2 for k in range(1,90))
   we,me=exact_prefix[i];exact-=we*tt-me
   delta=abs(exact-mp.mpf(str(values[j])));assert delta<mp.mpf('1e-7')
   rows.append(dict(kind=kind,cell_left_prime_power=int(q[i]),t=str(tt),x=mp.nstr(mp.exp(tt),30),psi_longdouble=str(values[j]),psi_mp80=mp.nstr(exact,70),absolute_difference=mp.nstr(delta,20)))
 with (P/'minimum_candidates.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 np.savez_compressed(P/'all_checkpoints.npz',prime_power=q,t=t,psi_event=event,interior_cell_indices=idx,t_interior=tr,psi_interior=interior)
 result=dict(status='DIAGNOSTIC_NEVER_A_PROOF',N=N,t_max=str(np.log(D(N))),events=len(q),interior_stationary_minima=len(idx),minimum_event=str(event.min()),minimum_interior=str(interior.min()),endpoint=str(endpoint),all_sampled_candidates_positive=bool(min(event.min(),interior.min(),endpoint)>0),alpha=mp.nstr(alpha,80),C0=mp.nstr(C0,80),seconds=time.monotonic()-start,warning='Long-double scan and MP replay, not outward intervals. Continuous infimum including origin is zero; between-event candidate completeness uses source convexity for x>=2.')
 (P/'scan_summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--N',type=int,default=10_000_000);a=p.parse_args();main(a.N)
