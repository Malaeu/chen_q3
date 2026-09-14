from pathlib import Path
from fractions import Fraction as Q
import importlib.util,math,hashlib,json
BASE=Path(__file__).resolve().parent
SOURCE=BASE/'ODD2_ORIGIN_BOX_20260912.py'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()=='545f60cd85a38ee81c01fbfe498e5ab0b6709f5fa2b5f0564d456425510b9b7c'
spec=importlib.util.spec_from_file_location('origin_source',SOURCE);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
B,rat=m.B,m.rat
N=32;delta=Q(1,4);weight=delta**4/4
fv=m.fvals(B(0),2*N)
a=[fv[2*i]*rat(delta**(2*i)/math.factorial(2*i)) for i in range(N+1)]
def mul(p,q):
 out=[B(0) for _ in range(len(p)+len(q)-1)]
 for i,x in enumerate(p):
  for j,y in enumerate(q):out[i+j]=out[i+j]+x*y
 return out
def deriv(p):return [i*x for i,x in enumerate(p)][1:]
a1=deriv(a);a2=deriv(a1)
p=[B(0) for _ in range(2*N+1)]
for k,v in enumerate(mul(a1,a1)):p[k]=p[k]+v
for k,v in enumerate(mul(a,a2)):p[k]=p[k]-v
for k,v in enumerate(mul(a,a)):p[k]=p[k]-rat(weight)*v
bern=[]
for i in range(2*N+1):bern.append(sum((p[k]*rat(Q(math.comb(i,k),math.comb(2*N,k))) for k in range(i+1)),B(0)))
poly=B(min(z.lo for z in bern),max(z.hi for z in bern))
k=N+1;r=Q(1,4);M=Q(1050)
e0=rat(M*r**k/(1-r));e1=rat(M*k*r**k/(1-r*Q(k+1,k)));e2=rat(M*k*(k-1)*r**k/(1-r*Q(k+1,k-1)))
A0=sum((B(x.absup()) for x in a),B(0));A1=sum((B(x.absup()) for x in a1),B(0));A2=sum((B(x.absup()) for x in a2),B(0))
err=(2*A1*e1+e1.square()+A0*e2+A2*e0+e0*e2+rat(weight)*(2*A0*e0+e0.square())).hi
full=poly+m.iv.symmetric(err)
print(json.dumps({'status':'POSITIVE_WHOLE_INTERVAL_CANDIDATE' if full.lo>0 else 'INCONCLUSIVE','accepted':False,'source':'F=Phi, h(u)=log F(sqrt(u))','domain_u':'[0,1/16]','target_h_second_upper':'-1/4','degree':N,'theta_modes':m.MODES,'precision':100,'dependency_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'a_coefficients':[x.out() for x in a],'numerator_polynomial_bernstein':poly.out(),'cauchy_tails':[e.out() for e in (e0,e1,e2)],'numerator_error':str(err),'numerator_full':full.out(),'global_ODD2':False,'RH_claim':False},indent=2))
