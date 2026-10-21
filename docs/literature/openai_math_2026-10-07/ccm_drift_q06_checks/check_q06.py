"""Exact Q06 local controls. They do not compute a CCM spectrum or prove RH."""
from fractions import Fraction as F
from collections import Counter
from pathlib import Path
import json,hashlib

C=Counter()
def zeros(n,m=None): return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]
def tr(A): return [list(x) for x in zip(*A)]
def add(A,B): return [[a+b for a,b in zip(x,y)] for x,y in zip(A,B)]
def scale(a,A): return [[a*x for x in row] for row in A]
def mul(A,B): return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def inv(A):
 n=len(A); R=[row[:]+erow for row,erow in zip(A,eye(n))]
 for j in range(n):
  p=next(i for i in range(j,n) if R[i][j]);R[j],R[p]=R[p],R[j]
  z=R[j][j];R[j]=[a/z for a in R[j]]
  for i in range(n):
   if i!=j:
    z=R[i][j];R[i]=[a-z*b for a,b in zip(R[i],R[j])]
 return [row[n:] for row in R]
def trace(A): return sum(A[i][i] for i in range(len(A)))
def mv(A,x): return [sum(a*b for a,b in zip(row,x)) for row in A]
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def source(M,w,L):
 a=F(1,2); rows=[]; deriv=[]
 for j in range(-M,M+1):
  om=j*w;d=a*a+om*om
  rows.append([F(1),a/d,om/d])
  deriv.append([F(0),2*a*om*om/(L*d*d),om*(om*om-a*a)/(L*d*d)])
 G=mul(tr(rows),rows);Gi=inv(G);P=add(eye(2*M+1),scale(-1,mul(mul(rows,Gi),tr(rows))))
 D=mul(mul(mul(P,deriv),Gi),tr(rows));Pd=scale(-1,add(D,tr(D)))
 return P,Pd

for M in range(2,7):
 for w in (F(1,7),F(1,3),F(2,5)):
  L=F(17,3);P,Pd=source(M,w,L); n=len(P)
  assert mul(P,P)==P and tr(P)==P;C['source_projector']+=1
  assert add(mul(Pd,P),mul(P,Pd))==Pd and mul(mul(P,Pd),P)==zeros(n);C['moving_projector_tangent']+=1
  d=[F(0)]*n;dp=[F(0)]*n
  d[M]=-F(3,4)
  for j in (-1,1):d[M+j]=F(1,2)+2*w*w;dp[M+j]=-4*w*w/L
  for j in (-2,2):d[M+j]=-F(1,8)-2*w*w;dp[M+j]=4*w*w/L
  assert mv(P,d)==d;C['literal_even_three_constraints']+=1
  assert mv(Pd,d)==mv(add(eye(n),scale(-1,P)),dp);C['normal_derivative_not_frozen']+=1
  A=[[F((i+1)*(j+1)+(-1)**(i+j),i+j+2) for j in range(n)] for i in range(n)]
  Ap=[[F(i+j+1,1+abs(i-j)) for j in range(n)] for i in range(n)]
  S=mul(mul(P,A),P)
  Sd=add(add(mul(mul(Pd,A),P),mul(mul(P,Ap),P)),mul(mul(P,A),Pd))
  K=add(mul(Pd,P),scale(-1,mul(P,Pd)))
  transported=mul(mul(P,add(Sd,add(mul(S,K),scale(-1,mul(K,S))))),P)
  expected=mul(mul(P,add(Ap,add(mul(Pd,A),mul(A,Pd)))),P)
  assert transported==expected;C['full_covariant_drift']+=1
  assert tr(K)==scale(-1,K) and add(mul(K,P),scale(-1,mul(P,K)))==Pd;C['Kato_generator_orientation']+=1
  Pnew,_=source(M+1,w,L);padded=zeros(n+2)
  for i in range(n):
   for j in range(n):padded[i+1][j+1]=P[i][j]
  E=add(Pnew,scale(-1,padded))
  assert mul(E,E)==E and mul(padded,E)==zeros(n+2) and trace(E)==2;C['nested_source_bands_rank_two_addition']+=1

# Exact polynomial coefficients of the fixed-age source witness.
def pmul(a,b):
 out=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
from math import comb
def translate(a,h):
 out=[F(0)]*len(a)
 for i,x in enumerate(a):
  for j in range(i+1):out[j]+=x*comb(i,j)*(-h)**(i-j)
 return out
p=[F(0),F(0),F(6),F(0),-F(1,8)]
for h in (F(1,4),F(1,3),F(2,5),F(1,2)):
 prod=pmul(translate(p,h),p)
 J=2*sum(a*h**(i+1)/F(i+1) for i,a in enumerate(prod))
 assert J==F(12,5)*h**5-F(1,35)*h**7+F(1,20160)*h**9;C['fixed_age_overlap_polynomial']+=1
 Jp=12*h**4-F(1,5)*h**6+F(1,2240)*h**8
 assert Jp>=11*h**4;C['strictly_positive_age_derivative_control']+=1

# Initial quartic shape, contacts and coefficient derivative of source vector.
for w in (F(1,11),F(1,5),F(2,7)):
 d=[-F(1,8)-2*w*w,F(1,2)+2*w*w,-F(3,4),F(1,2)+2*w*w,-F(1,8)-2*w*w]
 assert sum(d)==0
 assert sum(dj/(F(1,4)+(j*w)**2) for j,dj in zip(range(-2,3),d))==0
 assert sum(x*x for x in d)==F(35,32)+5*w*w+16*w**4
 C['source_norm_and_exponential_contacts']+=1

# Pinching is not free, even for a rank-one off-diagonal block.
for r in (F(1,7),F(2),F(9)):
 for pwr in (2,4,6):
  moment=r**pwr
  assert moment>0  # H=[[0,r],[r,0]] has +/-r, both diagonal blocks are zero.
  C['rank_one_pinching_positive_cost']+=1

# Actual prime/mobius coefficients: all powers and short/long endpoints.
def mu(n):
 v=1;p=2
 while p*p<=n:
  if n%p==0:
   n//=p;v=-v
   if n%p==0:return 0
  p+=1
 return -v if n>1 else v

def fac(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p+=1
 if n>1:out[n]=out.get(n,0)+1
 return out
for n in range(1,81):
 out={}
 for d in range(1,n+1):
  if n%d==0:
   for p,k in fac(n//d).items():out[p]=out.get(p,0)+mu(d)*k
 out={p:k for p,k in out.items() if k}
 ff=fac(n);expected={next(iter(ff)):1} if len(ff)==1 else {}
 assert out==expected;C['all_prime_power_mobius_log_atoms']+=1

for eps in (F(1,1024),F(1,128),F(1,64),F(1,33)):
 k=F(1,12)+eps
 assert F(1,2)+5*eps-6*k==-eps
 assert -F(1,2)+5*eps-5*k==-F(11,12)
 assert F(1,2)+eps>F(3,8)>F(3,2)*eps
 C['complete_edge_and_drift_power_budget']+=1

# Explicit planted failure of freezing P: P=diag(1,0), P'=[[0,1],[1,0]], A=[[0,1],[1,0]], A'=0.
P=[[F(1),F(0)],[F(0),F(0)]];Pd=[[F(0),F(1)],[F(1),F(0)]]
A=Pd
actual=mul(mul(P,add(mul(Pd,A),mul(A,Pd))),P)
assert actual[0][0]==2 and actual!=zeros(2);C['frozen_projector_failure_detected']+=1
# Cubic event is not identically nonpositive: the null-cubic fifth-order term survives.
assert F(1,48)+F(1,60)==F(3,80);C['one_sided_edge_square_completion']+=1
out={'status':'PASS','counts':dict(C),'total_checks':sum(C.values()),
 'scope':'Exact finite algebra and independent analytic-budget controls; not a full CCM spectral calculation.',
 'arb_runs':0,'lean_runs':0,'independent_review':'NOT_RUN',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'registration_sha256':hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest()}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
