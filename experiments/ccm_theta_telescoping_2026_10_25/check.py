from fractions import Fraction
from pathlib import Path
import json
checks=0
# Exact weighted index telescoping: each k has unique k=2^j*odd.
# Retained odd layers j<J plus tail 2^J|k reconstruct coefficient 1.
for J in range(1,13):
 for k in range(1,2049):
  layers=sum(k%(2**j)==0 and (k//(2**j))%2==1 for j in range(J))
  tail=int(k%(2**J)==0)
  assert layers+tail==1;checks+=1
# Finite shift polynomial identity with formal c: S_J(I-cT)+(cT)^J=I.
for J in range(1,33):
 coeff=[0]*(J+1)
 for j in range(J):coeff[j]+=1;coeff[j+1]-=1
 coeff[J]+=1
 assert coeff==[1]+[0]*J;checks+=1
# Exact scale prefactors using n^(-1/2) and shift log n:
# n^-1/2*n^(9/2)=n^4 and n^-1/2*n^(5/2)=n^2.
assert Fraction(-1,2)+Fraction(9,2)==4;checks+=1
assert Fraction(-1,2)+Fraction(5,2)==2;checks+=1
out={'status':'PASS_EXACT_FINITE_TELESCOPE','checks':checks,'theta_indices_tested':2048,'layers_tested':12,'full_CCM_evaluations':0,'numerical_hypothetical_zeros':0,'scope':'exact index and shift algebra, not analytic CCM bound validation'}
Path(__file__).with_name('results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
