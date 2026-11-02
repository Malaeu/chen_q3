"""Actual form pairings on finite endpoint-zero H1 tests; not full deficiency proof."""
from prototype import *
rows=[]
for m in [20,40,60,80,120,160,200,240]:
 for world in ['zeta','dh']:
  d=json.loads((P/f'profile_{world}_m{m}.json').read_text());Ae,Ao,_=build(world,m);lam=d['lambda_shift'];ce=np.array(d['even_coefficients']);co=np.array(d['odd_coefficients']);te=(Ae-lam*np.eye(m+1))@ce;to=(Ao-lam*np.eye(m))@co
  for n in [1,2,3]:
   om=2*np.pi*n/d['L']
   for parity,u,du in [('odd',to[n-1],om*te[n]),('even',te[n]-np.sqrt(2)*te[0],-om*to[n-1])]:
    rows.append(dict(world=world,m=m,n=n,parity=parity,correct_plus_residual=float(abs(du+u)),wrong_sign_residual=float(abs(du-u)),pair_u=float(u),pair_derivative=float(du)))
import csv
with (P/'weak_tests.csv').open('w',newline='') as f:w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
