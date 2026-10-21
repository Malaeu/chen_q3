"""Source kernel diagnostic only: no primes, CCM full spectra, or interval certificate."""
import mpmath as mp
from pathlib import Path
import json,hashlib,sys
mp.mp.dps=65
rows=[]
for power in (384,512,640):
 L=power*mp.log(2);M=2**(power//64);w=2*mp.pi/L;a=mp.mpf('0.5');h=mp.mpf(3)/8;s=L-h
 ks=list(range(-2,3));ds=[-mp.mpf(1)/8-2*w*w,mp.mpf(1)/2+2*w*w,-mp.mpf(3)/4,mp.mpf(1)/2+2*w*w,-mp.mpf(1)/8-2*w*w]
 dps=[4*w*w/L,-4*w*w/L,mp.mpf(0),-4*w*w/L,4*w*w/L]
 norm=mp.sqrt(sum(x*x for x in ds)); normprime=sum(x*y for x,y in zip(ds,dps))/norm
 c=[x/norm for x in ds];cp=[y/norm-x*normprime/norm**2 for x,y in zip(ds,dps)]
 js=list(range(-M,M+1));r=[a/(mp.sqrt(L)*(a*a+(j*w)**2)) for j in js]
 rmean=sum(r)/len(r);v=[x-rmean for x in r];vnorm=sum(x*x for x in v)
 rcprime=sum(r[k+M]*x for k,x in zip(ks,cp));alpha=rcprime/vnorm
 def Q(j,k):
  return 2*h/L*mp.cos(j*w*h) if j==k else (mp.sin(j*w*h)-mp.sin(k*w*h))/(mp.pi*(j-k))
 def Qdot(j,k):
  if j==k:return 2*s/L**2*mp.cos(j*w*h)-2*h/L*(j*w)*s/L*mp.sin(j*w*h)
  return 2*s/L**2*(j*mp.cos(j*w*h)-k*mp.cos(k*w*h))/(j-k)
 raw=sum(x*y*Qdot(j,k) for j,x in zip(ks,c) for k,y in zip(ks,c))
 Qc=[sum(x*Q(j,k) for k,x in zip(ks,c)) for j in js]
 motion=2*alpha*sum(x*y for x,y in zip(v,Qc))
 cov=raw+motion
 Jp=12*h**4-h**6/5+h**8/2240
 leading=(2*mp.pi)**8/(mp.mpf(35)/32)*Jp/L**9
 assert abs(sum(c))<mp.mpf('1e-55')
 assert abs(sum(x/(a*a+(k*w)**2) for k,x in zip(ks,c)))<mp.mpf('1e-55')
 assert cov>0
 rows.append({'m':'2^'+str(power),'epsilon':'1/64','M':M,'h':'3/8','L':str(L),
              'covariant_drift':str(cov),'frozen_P_term':str(raw),'P_motion_cross':str(motion),
              'leading_asymptotic':str(leading),'ratio_to_leading':str(cov/leading),
              'even_constraint_Gram_norm_squared':str(vnorm)})
 print(power,'ratio',mp.nstr(cov/leading,12),'P-motion/leading',mp.nstr(motion/leading,12),flush=True)
out={'status':'PASS_DIAGNOSTIC_NOT_INTERVAL','cases':len(rows),'decimal_digits':65,'rows':rows,
 'all_prime_sums_evaluated':False,'actual_full_CCM_spectrum_evaluated':False,
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
