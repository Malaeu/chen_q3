"""Arb outward rounding for the explicit preflight tail budget, not zero isolation."""
from pathlib import Path
import json,math
from flint import arb,ctx
P=Path(__file__).resolve().parent
def main():
 ctx.prec=600;pi=arb.pi();a=pi/5
 M=2*(-a).exp()/(1-(-a).exp())**2*(1/a+3/a**2+6/a**3+6/a**4)
 C=(5/pi)**arb('1.5')*pi.sqrt()/2*(2-pi*pi/6)
 A=arb(1024).log()/(arb(8)/7).log();B=(pi/4)/(arb(8)/7).log()
 assert M<512 and C>arb('.5') and A<100 and B<7
 N=230;r=16;p=32;L=arb(20).log()
 weight=arb(107+7*N)/arb(N)**p+arb(107)/(31*arb(N)**31)+arb(7)/(30*arb(N)**30)
 def ratio(k):
  norm=math.comb(2*k,k)**2+2*sum(math.comb(2*k,k-n)**2 for n in range(1,k+1))
  moment=2*sum(math.comb(2*k,k-n)**2*n**32 for n in range(1,k+1))
  return arb(moment)/norm
 out=[]
 for k,h,coarse in [(8,9,'2e-37'),(9,10,'2e-36'),(8,10,'5e-37')]:
  tail=2*arb(20)**arb('1.5')*L*(2*pi/L)**32*(ratio(k)*ratio(h)).sqrt()*weight
  assert tail<arb(coarse)
  out.append({'profiles':[k,h],'tail_interval':str(tail),'coarse_upper':coarse,'strict_upper_checked':True})
 d={'status':'ARB_ARITHMETIC_TAIL_BUDGET_NOT_FINITE_ZERO_CERTIFICATION','precision_bits':600,
 'M':str(M),'C':str(C),'Jensen_intercept':str(A),'Jensen_slope':str(B),
 'unit_slab_bound':'100+7*(j+1)','tail_height':230,'integration_by_parts_order':16,
 'profile_derivative_norm_ratio':'sum_n 2*binomial(2K,K-n)^2*n^32 / (binomial(2K,K)^2 + 2*sum_n binomial(2K,K-n)^2)',
 'bounds':out,'assumptions':'source completion theta representation and FE; full-plane zeros confined to -1<Re rho<2; finite census remains numerical'}
 (P/'tail_budget_arb.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d,indent=2))
if __name__=='__main__':main()
