#!/usr/bin/env python3
"""Mandatory controls only, after Gate0. No CCM scan or source arrays used."""
from pathlib import Path
import json,random,time,datetime
import mpmath as mp
P=Path(__file__).resolve().parents[1]
mp.mp.dps=80

def frob(M):return mp.sqrt(mp.fsum(x*x for x in M))
def main():
 assert json.loads((P/'GATE0.json').read_text())['status']=='PASS','Gate0 must pass first'
 started=datetime.datetime.now(datetime.timezone.utc).isoformat();start=time.monotonic();m=16;d=m+1;L=mp.log(m);b=L/2;rho=mp.mpf(1);c=rho/b
 ds=[mp.mpf(1)]+[mp.sqrt(2)]*m
 def F(j,z):
  if j==0:return mp.sin(z)/z if z else mp.mpf(1)
  return ds[j]*z*mp.sin(z)/(z*z-(mp.pi*j)**2)
 def J(n):
  n=abs(n)
  return mp.mpf(2)/3 if not n else 4*(-1)**n/(mp.pi*n)**2
 def T(n):return mp.mpf(4)/3 if not n else -J(n)
 K=mp.matrix(d);D=mp.matrix(d)
 for i in range(d):
  for j in range(i+1):
   K[i,j]=K[j,i]=2/mp.pi*mp.quad(lambda z:F(i,z)*F(j,z),[0,rho/2,rho])
   D[i,j]=D[j,i]=-ds[i]*ds[j]*(-1)**(i+j)/4*(mp.pi**2*i*j*(T(i-j)-T(i+j))+rho**2*(J(i-j)+J(i+j)))
 comm=D*K-K*D;fixed_r=frob(comm)/(frob(D)*frob(K));identity=mp.eye(d)/mp.sqrt(d)
 rng=random.Random(20261104);X=mp.matrix(d)
 for i in range(d):
  for j in range(i+1):X[i,j]=X[j,i]=mp.mpf(rng.randrange(-1000,1001))/1000
 scalar_comm=frob(identity*X-X*identity)/frob(X)
 # Independent direct-integral entries of D, not the closed-form J/T construction.
 spot=[]
 for i,j in [(0,0),(0,1),(1,1),(1,2),(3,5)]:
  def fi(k,y):return ds[k]*(-1)**k*mp.cos(mp.pi*k*y)/mp.sqrt(2)
  def dpi(k,y):return -ds[k]*(-1)**k*mp.pi*k*mp.sin(mp.pi*k*y)/mp.sqrt(2)
  direct=mp.quad(lambda y:-(1-y*y)*dpi(i,y)*dpi(j,y)-rho*rho*y*y*fi(i,y)*fi(j,y),[-1,0,1])
  spot.append(dict(i=i,j=j,closed=mp.nstr(D[i,j],82),direct_integral=mp.nstr(direct,82),difference=mp.nstr(direct-D[i,j],82)))
 assert all(abs(mp.mpf(s['difference']))<mp.mpf('1e-70')for s in spot)
 def txt(x):return mp.nstr(x,82)
 positive=dict(m=m,dimension=d,mpmath_dps=80,L=txt(L),rho='1',c=txt(c),a_polynomial='(L/2)^2 - x^2',b_polynomial='-c^2*x^2',D_Frobenius=txt(frob(D)),K_Frobenius=txt(frob(K)),commutator_Frobenius=txt(frob(comm)),fixed_Slepian_normalized_residual=txt(fixed_r),requested_threshold='1e-25',passes_requested_control=bool(fixed_r<=mp.mpf('1e-25')),commutator_entry_01=txt(comm[0,1]),D_entry_spot_checks=spot,literal_optimized_metric='0 EXACT by scalar identity; not a valid Slepian check')
 negative=dict(m=m,dimension=d,seed=20261104,matrix_distribution='symmetric integer entries uniform[-1000,1000]/1000',matrix_Frobenius=txt(frob(X)),chosen_D='I/sqrt(m+1)',D_norm=txt(frob(identity)),commutator_residual=txt(scalar_comm),literal_minimum='0 EXACT for every random matrix',requested_order_one_nonzero_discrimination_pass=False)
 result=dict(status='SCAN_VOID_POSITIVE_CONTROL_FAILURE'if not positive['passes_requested_control']else'CLASS_DEGENERATE_NEGATIVE_CONTROL_FAILURE',gate0_status='PASS',started_UTC=started,mpmath_dps=80,seconds=time.monotonic()-start,positive=positive,negative=negative,CCM_scan_run=False,non_scalar_commutant_scan_run=False,explanation='Continuous Slepian commutation loses cross-projection terms under finite cosine compression; scalar identity remains in the literal class. No repaired metric is substituted.')
 (P/'CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
