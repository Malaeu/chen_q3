"""Independent Suzuki checkpoints: 40 dps, all prime powers, no source sums read."""
import os,time,json,hashlib,array,bisect,math
from pathlib import Path
import mpmath as mp
mp.mp.dps=40
ROOT=Path('/workspace/corner_thermometer');OUT=ROOT/'output';PF=ROOT/'primes.bin'
MS=sorted(set([16,80,300]+[10**k for k in range(1,9)]))
class Kahan:
 def __init__(self):self.s=mp.mpf(0);self.c=mp.mpf(0)
 def add(self,x):
  y=x-self.c;t=self.s+y;self.c=(t-self.s)-y;self.s=t

def main():
 if not PF.exists():raise SystemExit('WAIT: primes.bin unavailable; no computation begun')
 start=time.monotonic();pr=array.array('I');pr.frombytes(PF.read_bytes())
 if pr.itemsize!=4:raise RuntimeError('uint32 array required')
 assert pr[0]==2 and pr[-1]<=MS[-1] and all(pr[k]<pr[k+1]for k in range(len(pr)-1))
 sums1=[Kahan()for _ in MS];sums2=[Kahan()for _ in MS];sums3=[Kahan()for _ in MS];counts=[0]*len(MS)
 for idx,p in enumerate(pr):
  lp=mp.log(p);invroot=1/mp.sqrt(p);weight=invroot;n=p;k=1
  while n<=MS[-1]:
   j=bisect.bisect_left(MS,n);v=lp*weight
   sums1[j].add(v);ln=k*lp;sums2[j].add(v*ln);sums3[j].add(v*ln*ln);counts[j]+=1
   if n>MS[-1]//p:break
   n*=p;k+=1;weight*=invroot
  if(idx+1)%250000==0:
   dt=time.monotonic()-start
   print(json.dumps(dict(primes_done=idx+1,prime=p,seconds=dt,estimated_total_seconds=dt*len(pr)/(idx+1))),flush=True)
 s1=Kahan();s2=Kahan();s3=Kahan();count=0;rows=[]
 C=mp.pi**2+8*mp.catalan;gamma_slope=(mp.digamma(mp.mpf(1)/4)-mp.log(mp.pi))/2
 for j,m in enumerate(MS):
  s1.add(sums1[j].s);s2.add(sums2[j].s);s3.add(sums3[j].s);count+=counts[j];L=mp.log(m)
  pole=4*(mp.exp(L/2)+mp.exp(-L/2)-2)
  arithmetic=-(L*s1.s-s2.s)
  gamma=L*gamma_slope
  lerch=(C-mp.exp(-L/2)*mp.lerchphi(mp.exp(-2*L),2,mp.mpf(1)/4))/4
  psi=pole+arithmetic+gamma+lerch
  rows.append(dict(m=m,L=mp.nstr(L,42),S1=mp.nstr(s1.s,42),S2=mp.nstr(s2.s,42),S3=mp.nstr(s3.s,42),primepower_count=count,pole=mp.nstr(pole,42),arithmetic=mp.nstr(arithmetic,42),gamma=mp.nstr(gamma,42),lerch=mp.nstr(lerch,42),Psi=mp.nstr(psi,42),A00=mp.nstr(2*psi/L,42)))
 result=dict(status='INDEPENDENT_MPMATH_40DPS_POINT_CHECKPOINTS_NOT_INTERVAL',preregistration='bd8ebad42d718a9fd2c5149470a646377f8e638f',dps=40,prime_file=str(PF),prime_file_sha256=hashlib.sha256(PF.read_bytes()).hexdigest(),prime_count=len(pr),last_prime=int(pr[-1]),sum_method='Kahan compensation per disjoint checkpoint bucket then Kahan cumulative; each p log/sqrt once, powers via recurrence; no root sums read',formula='Suzuki(1.1), original Catalan and lerchphi',all_primepowers=True,seconds=time.monotonic()-start,rows=rows)
 (OUT/'CHECKPOINTS_MP.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
