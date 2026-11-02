"""DIAGNOSTIC_NEVER_A_PROOF: source/zero mixed checks before any new series.

Uses saved pinned DH A, no source matrix edit or new eigenproblem. The finite
zero census is numerical, not interval-isolated; the omitted tail is bounded.
"""
import csv, hashlib, json, os, sys
from pathlib import Path
import mpmath as mp
P=Path(__file__).resolve().parent
INPUT=Path(os.environ.get('DH_INPUTS',str(P.parent)))
if not (INPUT/'dh_matrix.py').exists():INPUT=Path('/workspace/dh_inputs')
sys.path.insert(0,str(INPUT));import dh_matrix
mp.mp.dps=110
fmt=lambda x:mp.nstr(x,85)
def main():
 assert hashlib.sha256((INPUT/'dh_matrix.py').read_bytes()).hexdigest()=='9554c27549fc0970391c06026d8bfb402ab1cfa3b2f1db3c0db6deeb92a39f00'
 assert hashlib.sha256((INPUT/'dh_zeros.json').read_bytes()).hexdigest()=='e2f5f86d960aff5b45a318723072a1a2c67df3f00b6d213535274831c9afdee1'
 a,bc=dh_matrix.coeffs(20);tau=a[2]
 checks={'b3':fmt(bc[3]),'b3_expected':fmt(-tau*mp.log(3)),
 'b6':fmt(bc[6]),'b6_expected':fmt((1+tau*tau)*mp.log(6)),
 'b3_error':fmt(abs(bc[3]+tau*mp.log(3))),
 'b6_error':fmt(abs(bc[6]-(1+tau*tau)*mp.log(6)))}
 def D(s):return mp.dirichlet(s,[0,1,tau,-tau,-1])
 def comp(s):return mp.exp((s+1)*mp.log(5/mp.pi)/2+mp.loggamma((s+1)/2))*D(s)
 fe=[]
 for re,im in [('.7','10'),('.8','85.7'),('1.1','176.7')]:
  s=mp.mpc(re,im);x=comp(s);y=comp(1-s)
  fe.append({'s':[re,im],'relative_error':fmt(abs(x-y)/max(abs(x),abs(y)))})
 # Theta/Jensen coarse count: |a_n|<=1, theta(u)<=e^-a*u/(1-e^-a)^2.
 # Completed Lambda=integral_1^inf theta(u)(u^((s-1)/2)+u^(-s/2))du.
 # In |s-(2+it)|<=4, real s lies[-2,6], so |Lambda|<=M<512.
 # |Lambda(2+it)|>=C exp(-pi|t|/4), C>1/2: |D|>=2-zeta(2),
 # |Gamma(3/2+it/2)|^2=pi(1/4+t^2/4)/cosh(pi*t/2).
 aa=mp.pi/5
 M=2*mp.exp(-aa)/(1-mp.exp(-aa))**2*(1/aa+3/aa**2+6/aa**3+6/aa**4)
 C=(5/mp.pi)**mp.mpf('1.5')*mp.sqrt(mp.pi)/2*(2-mp.zeta(2))
 assert M<512 and C>mp.mpf('.5')
 assert mp.log(1024)/mp.log(mp.mpf(8)/7)<100
 assert (mp.pi/4)/mp.log(mp.mpf(8)/7)<7
 # All completed zeros are in -1<Re s<2 (Dirichlet comparison at2, FE).
 # Jensen radius4/3.5 covers a unit-height slab in that strip.
 # Upper slab j<=gamma<j+1 has at most100+7(j+1) zeros incl multiplicity.
 tail_count={'outer_radius':'4','inner_radius':'3.5','M_upper':'512','M_computed':fmt(M),
 'C_lower':'0.5','C_computed':fmt(C),'unit_slab_count_upper':'100+7*(j+1)',
 'zero_strip':'-1 < Re rho < 2','height_start':230,'scope':'coarse analytic tail budget; finite census not interval-certified'}
 m=20;L=mp.log(m);b=L/2;r=16;N=230;p=2*r
 Adata=json.loads((INPUT/'matrix_cells'/'dh_m20_dps120_gl128.json').read_text());A=mp.matrix(Adata['A'])
 z=json.loads((INPUT/'dh_zeros.json').read_text())
 def vector(k):
  v=mp.matrix(m+1,1)
  v[0]=mp.sqrt(L)*mp.binomial(2*k,k)/2**k
  for n in range(1,k+1):v[n]=mp.sqrt(L)*mp.binomial(2*k,k-n)*2**(1-k)/(mp.sqrt(2)*(-1)**n)
  return v/mp.norm(v)
 def F(v,t):
  return mp.fsum(v[n]*(1 if n==0 else mp.sqrt(2))*(-1)**n*b/mp.sqrt(L)*(mp.sinc((t-2*mp.pi*n/L)*b)+mp.sinc((t+2*mp.pi*n/L)*b)) for n in range(m+1))
 def deriv_l1_bound(v):return mp.sqrt(L)*mp.sqrt(mp.fsum(v[n]**2*(2*mp.pi*n/L)**(2*r) for n in range(1,m+1)))
 # sum_j>=N (107+7j)/j^p <= f(N)+integral_N^inf f(x)dx.
 sum_upper=(107+7*N)/mp.mpf(N)**p+107*mp.mpf(N)**(1-p)/(p-1)+7*mp.mpf(N)**(2-p)/(p-2)
 tests=[]
 for k,h in [(8,9),(9,10),(8,10)]:
  v,w=vector(k),vector(h);source=(v.T*A*w)[0];zero=mp.mpf(0)
  for q in z['critical_line_zeros']:
   g=mp.mpf(q['gamma']);zero+=2*F(v,g)*F(w,g)
  for q in z['off_line_pairs']:
   t=mp.mpf(q['gamma'])+mp.j*(mp.mpf(q['sigma_right'])-mp.mpf('.5'))
   zero+=4*mp.re(F(v,t)*F(w,t))
  bound=2*mp.exp(3*b)*deriv_l1_bound(v)*deriv_l1_bound(w)*sum_upper
  err=abs(source-zero)
  tests.append({'m':m,'profiles':[k,h],'definition':'unit (1+cos(2*pi*x/L))^K on window, zero outside',
   'physical_gram':fmt((v.T*w)[0]),'f_norm2':fmt((v.T*v)[0]),'g_norm2':fmt((w.T*w)[0]),
   'source':fmt(source),'finite_zero_sum':fmt(zero),'absolute_difference':fmt(err),'omitted_zero_tail_upper':fmt(bound),
   'difference_below_tail_upper':bool(err<=bound),'integration_by_parts_order':r,'tail_height':N,
   'tail_to_difference_ratio':fmt(bound/err) if err else 'inf'})
 assert all(x['difference_below_tail_upper'] for x in tests)
 out={'status':'DIAGNOSTIC_NEVER_A_PROOF','check':'Ciii','dps':mp.mp.dps,'source_base':'d26831357b6cb3b2b7d4a569d2031e454952b246',
 'source_script_sha256':hashlib.sha256((INPUT/'dh_matrix.py').read_bytes()).hexdigest(),
 'zero_source_sha256':hashlib.sha256((INPUT/'dh_zeros.json').read_bytes()).hexdigest(),
 'coefficients':checks,'functional_equation':fe,'tail_count_budget':tail_count,'mixed_tests':tests,
 'finite_zero_census_status':'NUMERICAL_COUNT_MATCH_NOT_INTERVAL_CERTIFIED','new_eigenproblems':0,
 'verdict':'PASS_NUMERICAL_SOURCE_CHECK_WITH_EXPLICIT_OMITTED_TAIL_BUDGET'}
 (P/'preflight.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
