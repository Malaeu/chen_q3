"""Replay the source's four-anchor coarse budget, at80digits; no proof."""
from pathlib import Path
import sys,json
import mpmath as mp
from check_margin import source
OUT=Path(__file__).resolve().parent
mp.mp.dps=80
a=mp.log(16);delta=mp.log(mp.mpf(17)/16);old=[a*(i+1)/4 for i in range(4)]
g,atoms=source('zeta',a+delta)
cc=mp.euler+mp.log(8*mp.pi)+mp.pi/2
def gp(u):
    r=mp.exp(-u/2)
    atanhr=(mp.log1p(r)-mp.log(-mp.expm1(-u/2)))/2
    return -4*mp.sinh(u/2)+cc/2-atanhr-mp.atan(r)+mp.fsum(weight for s,weight,n in atoms if s<=u)
def eta(i,x):return gp((a-old[i])+x)-gp(a+x)
def K(s,t):return g(s-t)-g(s)-g(t)
C=mp.matrix([[K(s,t) for t in old] for s in old])
R=mp.matrix(4)
for i in range(4):
    for j in range(i+1):
        R[i,j]=R[j,i]=mp.quad(lambda x:eta(i,x)*eta(j,x),[0,delta/4,delta])
Linv=mp.cholesky(C)**-1
rho=mp.eigsy(Linv*R*Linv.T,eigvals_only=True)[3]
r=mp.exp(-delta/2)
beta=2*(mp.atanh(r)+mp.atan(r))-cc-(2*mp.sinh(delta/2)-delta)
record={'status':'DIAGNOSTIC_NEVER_A_PROOF','dps':80,'a':mp.nstr(a,60),'delta':mp.nstr(delta,60),'beta':mp.nstr(beta,70),'rho':mp.nstr(rho,70),'beta_minus_rho':mp.nstr(beta-rho,70),'coarse_mu_lower':mp.nstr(1-rho/beta,70),'rho_source40_difference':mp.nstr(rho-mp.mpf('.95532489784161851'),30)}
(OUT/'coarse_source.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
