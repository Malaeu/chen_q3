"""Source-correct screw geometry on genuinely nested nodes. No RH premise.
DIAGNOSTIC_NEVER_A_PROOF; negative pivot signs are numerical diagnostics.
"""
from pathlib import Path
import mpmath as mp
import json,csv,time,sys
P=Path(__file__).resolve().parent;mp.mp.dps=85

def coefficients(M,world):
 if world=='zeta':
  out=[mp.mpf(0)]*(M+1)
  for p in range(2,M+1):
   if all(p%d for d in range(2,int(p**.5)+1)):
    k=p
    while k<=M:out[k]=mp.log(p);k*=p
  return out
 tau=(mp.sqrt(10-2*mp.sqrt(5))-2)/(mp.sqrt(5)-1)
 a=[mp.mpf(0),mp.mpf(1),tau,-tau,mp.mpf(-1)];b=[mp.mpf(0)]*(M+1)
 for n in range(2,M+1):b[n]=a[n%5]*mp.log(n)-mp.fsum(b[d]*a[(n//d)%5] for d in range(2,n) if n%d==0)
 return b

class Source:
 def __init__(self,world,maxn=300):
  self.world=world;self.b=coefficients(maxn,world)
  self.c=-mp.euler-mp.log(8*mp.pi)-mp.pi/2 if world=='zeta' else -mp.euler-mp.log(8*mp.pi/5)+mp.pi/2
  self.alpha=mp.mpf('.5') if world=='zeta' else mp.mpf('1.5')
  self.logs=[mp.log(n) if n else mp.mpf(0) for n in range(maxn+1)]
 def psi(self,t):
  if t==0:return mp.mpf(0)
  alpha=self.alpha
  def fj(s):return mp.mpf('.5') if s==0 else s*mp.exp(-alpha*s)/(-mp.expm1(-2*s))
  a=mp.exp(-t/2);tail=mp.atanh(a)+(mp.atan(a) if self.world=='zeta' else -mp.atan(a))
  arch=mp.quad(fj,[0,t/2,t])+t*tail
  pole=4*(mp.expm1(t/2)+mp.expm1(-t/2)) if self.world=='zeta' else 0
  arith=mp.fsum(self.b[n]/mp.sqrt(n)*(t-self.logs[n]) for n in range(2,len(self.b)) if self.logs[n]<=t)
  return self.c*t/2+arch+pole-arith
 def explicit_zeta(self,t):
  # Suzuki 2206 (1.1), independently evaluated special-function expression.
  C=mp.pi**2+8*mp.catalan
  arith=mp.fsum(self.b[n]/mp.sqrt(n)*(t-self.logs[n]) for n in range(2,len(self.b)) if self.logs[n]<=t)
  return 4*(mp.expm1(t/2)+mp.expm1(-t/2))-arith+t/2*(mp.digamma(mp.mpf('.25'))-mp.log(mp.pi))+(C-mp.exp(-t/2)*mp.lerchphi(mp.exp(-2*t),2,mp.mpf('.25')))/4

def run(world):
 start=time.time();M=480;h=mp.log(240)/M;tau=(M+1)*h;s=Source(world,300)
 # Integer and half-integer distances suffice for every point and the fixed target.
 vals=[s.psi(j*h/2) for j in range(2*M+3)]
 print(world,'psi values done',round(time.time()-start,2),flush=True)
 G=mp.matrix(M);k=mp.matrix(M,1)
 for i in range(M):
  ti=i+1;k[i]=vals[2*ti]+vals[2*M+2]-vals[2*M+2-2*ti]
  for j in range(M):G[i,j]=vals[2*ti]+vals[2*(j+1)]-vals[2*abs(ti-j-1)]
 LL=mp.eye(M);D=[];y=[];E=mp.mpf(0);rows=[];neg=0;orth_error=mp.mpf(0)
 for j in range(M):
  dj=G[j,j]-mp.fsum(LL[j,a]**2*D[a] for a in range(j));D.append(dj);neg+=int(dj<0)
  if not dj:raise ArithmeticError('exact zero pivot')
  yj=k[j]-mp.fsum(LL[j,a]*y[a] for a in range(j));y.append(yj);increment=yj*yj/dj;E+=increment
  for i in range(j+1,M):LL[i,j]=(G[i,j]-mp.fsum(LL[i,a]*LL[j,a]*D[a] for a in range(j)))/dj
  rows.append({'n':j+1,'L':mp.nstr((j+1)*h,75),'effective_m':mp.nstr(mp.exp((j+1)*h),50),'negative_inertia':neg,'Schur_pivot':mp.nstr(dj,75),'projection_energy':mp.nstr(E,75),'increment':mp.nstr(increment,75),'target_residual':mp.nstr(2*vals[2*M+2]-E,75),'pivot_over_max_diagonal':mp.nstr(abs(dj)/max(abs(G[a,a]) for a in range(j+1)),50)})
  if (j+1)%40==0:print(world,'LDL',j+1,'negative',neg,'E',mp.nstr(E,10),flush=True)
 # Reconstruction and solves are checked directly at the last prefix.
 x=mp.matrix([y[i]/D[i] for i in range(M)])
 for i in range(M-1,-1,-1):x[i]-=mp.fsum(LL[a,i]*x[a] for a in range(i+1,M))
 residual=mp.norm(G*x-k);energy_direct=mp.fdot(k,x)
 # Selected source normalization checks, not a zero-side tail assumption.
 primary=[]
 if world=='zeta':
  for t in [mp.mpf('.1'),mp.log(2),mp.log(20),mp.log(240)]:primary.append(mp.nstr(abs(s.psi(t)-s.explicit_zeta(t)),70))
 cells=[]
 for m in range(20,241):
  n=int(mp.floor(mp.log(m)/h));n=min(n,M)
  cells.append({'m':m,'node_prefix':n,**{key:rows[n-1][key] for key in ['negative_inertia','projection_energy','target_residual','Schur_pivot','increment']}})
 result={'status':'DIAGNOSTIC_NEVER_A_PROOF','world':world,'dps':mp.mp.dps,'nodes':M,'h':mp.nstr(h,80),'fixed_target_tau':mp.nstr(tau,80),'g_equals_minus_psi':True,'first_negative_node':next((r for r in rows if r['negative_inertia']),None),'first_decreasing_energy_node':next((r for r in rows if mp.mpf(r['increment'])<0),None),'final_linear_solve_residual':mp.nstr(residual,75),'final_energy_direct_error':mp.nstr(abs(E-energy_direct),75),'source_Suzuki_formula_errors':primary,'prefixes':rows,'m_cells':cells,'seconds':time.time()-start}
 (P/f'curve_refined_{world}.json').write_text(json.dumps(result,indent=2)+'\n')
 with (P/f'curve_refined_{world}.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
 print(world,'DONE',result['seconds'],'first_negative',result['first_negative_node'],flush=True)

if __name__=='__main__':run(sys.argv[1])
