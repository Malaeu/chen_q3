"""Bounded independent MP candidate refinement; frozen checkpoint states only."""
import array,bisect,json,time,hashlib
from pathlib import Path
import mpmath as mp
mp.mp.dps=40
ROOT=Path('/workspace/corner_thermometer');OUT=ROOT/'output'
cp=json.loads((OUT/'CHECKPOINTS_MP.json').read_text());states={r['m']:r for r in cp['rows']}
class Kahan:
 def __init__(self,x=0):self.s=mp.mpf(x);self.c=mp.mpf(0)
 def add(self,x):
  y=x-self.c;t=self.s+y;self.c=(t-self.s)-y;self.s=t
C=mp.pi**2+8*mp.catalan;gs=(mp.digamma(mp.mpf(1)/4)-mp.log(mp.pi))/2

def psi(m,S):
 L=mp.log(m);return 4*(mp.exp(L/2)+mp.exp(-L/2)-2)-L*S[0]+S[1]+L*gs+(C-mp.exp(-L/2)*mp.lerchphi(mp.exp(-2*L),2,mp.mpf(1)/4))/4

def primitive(L,S):
 # Exact integral_0^L Psi(t)dt, including original Lerch order3.
 return 16*mp.sinh(L/2)-8*L-(L*L*S[0]-2*L*S[1]+S[2])/2+gs*L*L/2+C*L/4-(mp.zeta(3,mp.mpf(1)/4)-mp.exp(-L/2)*mp.lerchphi(mp.exp(-2*L),3,mp.mpf(1)/4))/8

def refine(pr,base,ms):
 states0=[states[base][k]for k in ['S1','S2','S3']];buckets=[[Kahan()for k in range(3)]for m in ms];count=0;t0=time.monotonic();mx=ms[-1]
 for p in pr:
  if p>mx:break
  n=p;k=1
  while n<=base and n<=mx//p:n*=p;k+=1
  if n<=base or n>mx:continue
  lp=mp.log(p);invroot=1/mp.sqrt(p);weight=invroot**k
  while n<=mx:
   j=bisect.bisect_left(ms,n);v=lp*weight;ln=k*lp
   for b,z in zip(buckets[j],[v,v*ln,v*ln*ln]):b.add(z)
   count+=1
   if n>mx//p:break
   n*=p;k+=1;weight*=invroot
 sums=[Kahan(v)for v in states0];rows=[]
 for m,bb in zip(ms,buckets):
  for ss,b in zip(sums,bb):ss.add(b.s)
  S=[v.s for v in sums];rows.append(dict(m=m,Psi=mp.nstr(psi(m,S),42),S1=mp.nstr(S[0],42),S2=mp.nstr(S[1],42),S3=mp.nstr(S[2],42)))
 return rows,dict(baseline_m=base,additional_primepowers=count,seconds=time.monotonic()-t0)

def main():
 start=time.monotonic();pr=array.array('I');pr.frombytes((ROOT/'primes.bin').read_bytes());plan=json.loads((OUT/'REFINEMENT_PLAN.json').read_text())
 mins,meta=refine(pr,10**7,list(range(plan['m_first'],plan['m_last']+1)))
 print('MIN_DONE',meta,flush=True)
 maxs,maxmeta=refine(pr,100000,list(range(plan['native_maximum_m']-2,plan['native_maximum_m']+3)))
 ranked=sorted(mins,key=lambda r:mp.mpf(r['Psi']));mranked=sorted(maxs,key=lambda r:mp.mpf(r['Psi']),reverse=True)
 for k,r in enumerate(ranked,1):r['rank']=k
 for k,r in enumerate(mranked,1):r['rank']=k
 end=mp.log(10**8);S=[mp.mpf(states[10**8][k])for k in ['S1','S2','S3']];ant=primitive(end,S)
 lo=mp.log(2);a2=mp.log(2)/mp.sqrt(2);Slo=[a2,a2*lo,a2*lo*lo];antlo=primitive(lo,Slo)
 result=dict(status='BOUNDED_MPMATH40DPS_REFINEMENT_NOT_GLOBAL_INTERVAL_CERTIFICATE',dps=40,checkpoint_sha256=hashlib.sha256((OUT/'CHECKPOINTS_MP.json').read_bytes()).hexdigest(),primefile_sha256=hashlib.sha256((ROOT/'primes.bin').read_bytes()).hexdigest(),minimum_candidate_scope='all40 native guardband candidates; no independent global exhaustive MP scan',candidate_minimum=ranked[0],minimum_ranked_rows=ranked,minimum_top20=ranked[:20],maximum_neighborhood_ranked_rows=mranked,maximum_neighborhood_winner=mranked[0],minimum_refinement=meta,maximum_refinement=maxmeta,mean=dict(formula='original Suzuki antiderivative using order3 Lerch and frozen independently computed S1,S2,S3',integral_from_zero=mp.nstr(ant,42),uniform_t_mean_from_zero=mp.nstr(ant/end,42),integral_to_log2=mp.nstr(antlo,42),uniform_t_mean_from_log2=mp.nstr((ant-antlo)/(end-lo),42)),seconds=time.monotonic()-start,no_root_sums_read=True)
 (OUT/'REFINED_EXTREMA.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
