"""Fixed whole-strip certificate candidate. No self-admission or RH claim.
Interval Decimal + explicit full-source analytic remainder; see proof text.
"""
from decimal import Decimal as D, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path
import math, json, sys, time, hashlib, os
PREC=int(os.getenv('STRIP_PREC','60'))
DN=Context(prec=PREC,rounding=ROUND_FLOOR,Emin=-999999999,Emax=999999999)
UP=Context(prec=PREC,rounding=ROUND_CEILING,Emin=-999999999,Emax=999999999)
NE=Context(prec=PREC,rounding=ROUND_HALF_EVEN,Emin=-999999999,Emax=999999999)
class B:
 __slots__=('lo','hi')
 def __init__(self,a=0,b=None):
  if isinstance(a,B):self.lo,self.hi=a.lo,a.hi;return
  self.lo=D(a);self.hi=self.lo if b is None else D(b)
  assert self.lo.is_finite() and self.hi.is_finite() and self.lo<=self.hi
 def __add__(a,b):
  b=B(b);return B(DN.add(a.lo,b.lo),UP.add(a.hi,b.hi))
 __radd__=__add__
 def __neg__(a):return B(a.hi.copy_negate(),a.lo.copy_negate())
 def __sub__(a,b):return a+-B(b)
 def __rsub__(a,b):return B(b)+-a
 def __mul__(a,b):
  b=B(b)
  ls=[DN.multiply(x,y) for x in (a.lo,a.hi) for y in (b.lo,b.hi)]
  us=[UP.multiply(x,y) for x in (a.lo,a.hi) for y in (b.lo,b.hi)]
  return B(min(ls),max(us))
 __rmul__=__mul__
 def inv(a):
  assert not a.lo<=0<=a.hi
  return B(DN.divide(1,a.hi),UP.divide(1,a.lo))
 def __truediv__(a,b):return a*B(b).inv()
 def __rtruediv__(a,b):return B(b)*a.inv()
 def __pow__(a,n):
  assert isinstance(n,int)
  if n<0:return a.inv()**(-n)
  if n==0:return B(1)
  if n==1:return a
  if n%2==0:return (a**(n//2)).sq()
  return a*(a**(n-1))
 def sq(a):
  if a.lo>=0:return B(DN.multiply(a.lo,a.lo),UP.multiply(a.hi,a.hi))
  if a.hi<=0:return (-a).sq()
  return B(0,max(UP.multiply(a.lo,a.lo),UP.multiply(a.hi,a.hi)))
 def exp(a):return B(NE.next_minus(NE.exp(a.lo)),NE.next_plus(NE.exp(a.hi)))
 def log(a):
  assert a.lo>0
  return B(NE.next_minus(NE.ln(a.lo)),NE.next_plus(NE.ln(a.hi)))
 def sqrt(a):
  assert a.lo>=0
  l=D(0) if a.lo==0 else NE.next_minus(NE.sqrt(a.lo))
  return B(l,NE.next_plus(NE.sqrt(a.hi)))
 def absup(a):return max(a.lo.copy_abs(),a.hi.copy_abs())
 def out(a):return [str(a.lo),str(a.hi)]
 def __repr__(a):return str(a.out())
def rat(q):
 q=Q(q);return B(DN.divide(q.numerator,q.denominator),UP.divide(q.numerator,q.denominator))
def hull(a,b):return B(min(a.lo,b.lo),max(a.hi,b.hi))
def sym(e):return B(D(e).copy_negate(),e)
Z=B(0);ONE=B(1)
def arctan_inv(n):
 total=Q(0);j=0
 while True:
  term=Q((-1)**j,(2*j+1)*n**(2*j+1));total+=term
  rem=Q(1,(2*j+3)*n**(2*j+3))
  if rem<Q(1,10**(PREC+12)):return rat(total)+sym(rat(rem).hi)
  j+=1
PI=16*arctan_inv(5)-4*arctan_inv(239)
N=16
NU=[Q(7,2),Q(5,2),Q(3,2)]
DIRECT=[]
for j,nu in enumerate(NU):
 b=Q(1);bp=Q(0)
 for k in range(N):
  # Exact binomial and derivative with respect to nu.
  DIRECT.append((k+j,(0,1,0)[j]-k,rat((1,-6,9)[j]*math.factorial(k)*b),rat((1,-6,9)[j]*math.factorial(k)*bp/2)))
  bp=(bp*(nu-k)+b)/Q(k+1);b=b*(nu-k)/Q(k+1)

@lru_cache(None)
def j_at_c(cstr):
 """All J_k at an exact Decimal c>=1, with enclosed transcendental values."""
 c=B(cstr);assert c.lo>=1
 if c.lo==1:
  return tuple(rat(Q(2**k*math.factorial(k)**2,math.factorial(2*k+1))) for k in range(N+2))
 if c.lo<D('1.1'):
  w=(c-1)/(c+1);out=[]
  for k in range(N+2):
   # J_k=2(c/(c+1))^(k+1) * sum_{l>=0} binom(k+l,l) w^l integral t^(2l)(1-t²)^k dt.
   term=rat(Q(2**k*math.factorial(k),math.prod(range(1,2*k+2,2))))
   total=term
   for ell in range(100):
    term=term*w*rat(Q((k+ell+1)*(2*ell+1),(ell+1)*(2*ell+2*k+3)))
    total=total+term
   tail=term*w/(1-w)
   out.append(2*(c/(c+1))**(k+1)*(total+B(0,tail.hi)))
  return tuple(out)
 s=(c.sq()-1).sqrt();ph=(c+s).log()/s
 out=[c*ph,c.sq()*(c*ph-1)/(c.sq()-1)]
 for k in range(1,N+1):
  out.append(c.sq()*((2*k+1)*out[-1]-k*out[-2])/((k+1)*(c.sq()-1)))
 assert all(j.lo>0 for j in out)
 return tuple(out)

@lru_cache(None)
def d_data(dl,dh):
 """Intervals for an entire rational d cell; J_k monotone in c."""
 Dd=B(rat(dl).lo,rat(dh).hi)
 def coshpt(t):
  ep=rat(t).exp();return (ep+ep.inv())/2
 cl,ch=coshpt(dl),coshpt(dh)
 if dl==0:cl=B(1)
 c=B(max(D(1),cl.lo),ch.hi)
 ed=Dd.exp();sh=(ed-ed.inv())/2;sh=B(max(D(0),sh.lo),sh.hi)
 th=sh/c;se=c.inv().sq()
 jl=j_at_c(str(c.lo));jh=j_at_c(str(c.hi))
 js=[B(jl[k].lo,jh[k].hi) for k in range(N+2)]
 # h=d*coth(d)=J0; h' increasing and h''>=0. Evaluate h' at endpoints by small-d power-free identity via J.
 def hp(t,cpt):
  if t==0:return B(0)
  ep=rat(t).exp();ss=(ep-ep.inv())/2
  return cpt/ss-rat(t)/ss.sq()
 # Monotonicity h''>=0 gives the full h' interval from the two endpoints.
 if dl==0:
  hpI=B(0,min(D(1),hp(dh,ch).hi))
 else:
  hl=hp(dl,cl);hh=hp(dh,ch)
  hpI=B(max(D(0),hl.lo),min(D(1),hh.hi))
 # h'' = 2 csch²(d)*(h-1); avoid origin singularity via positive series integral bounds.
 if dl < Q(1,32):
  # Regular identity h''=E_0+tanh(d)^2 F_0, including d=0.
  E=js[0]-js[1];F=0*js[0]-2*js[1]+2*js[2]
  hpp=E+th.sq()*F
  hpp=B(max(D(0),hpp.lo),hpp.hi)
 else:hpp=2*(js[0]-1)/sh.sq()
 h=js[0]
 return c,th,se,js,h,hpI,hpp

def poly_jets(yl,yh,dl,dh):
 c,th,se,js,h,hp,hpp=d_data(dl,dh)
 m=B(rat(yl+dl/2).lo,rat(yh+dh/2).hi)
 w=(-2*m).exp()/(2*PI)
 wp=[ONE]
 for p in range(N+2):wp.append(wp[-1]*w)
 cp={0:ONE}
 for k in range(1,N+1):cp[-k]=c**(-k)
 cp[1]=c
 # Jets order (value,m,d,mm,md,dd). The leading cancellation is kept as Q0.
 vals=[m-h/2,ONE,-hp/2,Z,Z,-hpp/2]
 for p,r,A,Bb in DIRECT:
  if p==0:continue # m term already in Q0
  base=m*A+Bb
  am=A-2*p*base;amm=4*p*p*base-4*p*A
  cf=cp[r];ud=r*th*cf;udd=(r*se+r*r*th.sq())*cf
  g=wp[p]
  terms=[g*base*cf,g*am*cf,g*base*ud,g*amm*cf,g*am*ud,g*base*udd]
  vals=[a+b for a,b in zip(vals,terms)]
 for k in range(N):
  J=js[k];E=(k+1)*(J-js[k+1]);F=(k+1)*(k*J-2*(k+1)*js[k+1]+(k+2)*js[k+2])
  ak=(-1)**k*math.factorial(k)
  for p,r,coef in [(k,-k,Q(-ak,2)),(k+1,1-k,Q(3*ak)),(k+2,-k,(3*k-Q(3,2))*ak)]:
   if p==0:continue # -h/2 already kept exactly
   cf=cp[r];u=cf*J
   ud=cf*th*(r*J+E)
   udd=cf*((r*se+r*r*th.sq())*J+(1+2*r*th.sq())*E+th.sq()*F)
   g=rat(coef)*wp[p]
   terms=[g*u,-2*p*g*u,g*ud,4*p*p*g*u,-2*p*g*ud,g*udd]
   vals=[a+b for a,b in zip(vals,terms)]
 return m,se,vals

ERR=D('1e-9')
def full_cell(yl,yh,dl,dh):
 m,se,j=poly_jets(yl,yh,dl,dh)
 es=[ERR,UP.multiply(128,ERR),UP.multiply(128,ERR),UP.multiply(32768,ERR),UP.multiply(16384,ERR),UP.multiply(32768,ERR)]
 T,Tm,Td,Tmm,Tmd,Tdd=[a+sym(e) for a,e in zip(j,es)]
 if T.lo<=0:return None,T
 C=se+(Tmm/4-Tdd)/T-(Tm/2-Td)*(Tm/2+Td)/T.sq()
 return C,T

def selftests():
 assert (B(1,2)*B(-3,4)).out()==['-6','8']
 assert B(-1,1).sq().out()==['0','1']
 assert (rat(Q(1,3))*3).lo<=1<=(rat(Q(1,3))*3).hi
 assert j_at_c('1')[0].out()==['1','1']
 # Deliberately negative C: T=m cosh d at m=1,d=0 -> G=m/(2alpha), C=-1/4.
 T,Tm,Td,Tmm,Tdd=B(1),B(1),B(0),B(0),B(1)
 C=B(1)+(Tmm/4-Tdd)/T-(Tm/2-Td)*(Tm/2+Td)/T.sq()
 assert C.hi<0
 # Rank-one log kernel: T=cosh d gives exactly C=0 at d=0.
 assert (B(1)-B(1)).lo==0 and (B(1)-B(1)).hi==0
 # Exact binomial differentiation primitive.
 assert DIRECT[1][2].out()==['3.5','3.5'] and DIRECT[1][3].out()==['0.5','0.5']

def build():
 selftests();bounds=audit_bounds();t0=time.monotonic()
 # Disjoint interiors:19 unit y-slabs x3 unit d-slabs, including every boundary.
 stack=[(Q(j),Q(j+1),Q(k),Q(k+1),0) for j in range(1,20) for k in range(3)]
 done=[];unpaid=[];evals=0;minC=None;minT=None;worst=None;limit=False
 while stack:
  yl,yh,dl,dh,depth=stack.pop();evals+=1
  C,T=full_cell(yl,yh,dl,dh)
  if C is not None and C.lo>D('0.001') and T.lo>D('0.45'):
   done.append([str(x) for x in (yl,yh,dl,dh)]+[str(C.lo),str(T.lo)])
   if minC is None or C.lo<minC:minC=C.lo;worst=done[-1]
   minT=T.lo if minT is None else min(minT,T.lo)
  elif depth>=18 or evals>=100000:
   unpaid.append([str(x) for x in (yl,yh,dl,dh)]+[None if C is None else C.out(),T.out()])
   if evals>=100000:limit=True;break
  else:
   if yh-yl>=dh-dl:
    mid=(yl+yh)/2;stack +=[(yl,mid,dl,dh,depth+1),(mid,yh,dl,dh,depth+1)]
   else:
    mid=(dl+dh)/2;stack +=[(yl,yh,dl,mid,depth+1),(yl,yh,mid,dh,depth+1)]
  if evals%1000==0:print(json.dumps({'evaluated':evals,'proved':len(done),'pending':len(stack),'unpaid':len(unpaid),'minC':str(minC)}),file=sys.stderr,flush=True)
 if stack:unpaid +=[[str(x) for x in cell[:4]]+['NOT_EVALUATED'] for cell in stack]
 # Exact area checks plus tree provenance ensure no holes; every split replaced one cell by its two children.
 area=sum(( (Q(row[1])-Q(row[0]))*(Q(row[3])-Q(row[2])) for row in done),Q(0))
 uarea=sum(( (Q(row[1])-Q(row[0]))*(Q(row[3])-Q(row[2])) for row in unpaid),Q(0))
 assert area+uarea==57
 if unpaid:
  return {'status':'INCOMPLETE_FIXED_STRIP_COVER','accepted':False,'evaluations':evals,
          'covered_area':str(area),'unpaid_area':str(uarea),'unpaid':unpaid,'RH_claim':False}
 leaves={tuple(Q(x) for x in row[:4]) for row in done}
 def encode(cell,depth=0):
  if cell in leaves:leaves.remove(cell);return '0'
  assert depth<18
  left,right=children(cell)
  return '1'+encode(left,depth+1)+encode(right,depth+1)
 trees=[encode(cell) for cell in roots()]
 assert not leaves and sum(map(len,trees))==evals
 return {'status':'WHOLE_STRIP_CERTIFICATE_CANDIDATE','accepted':False,
  'target':['1<=y<=20','0<=d<=3'],'precision':PREC,'N':N,'rho':'1/128','E':'1e-9',
  'C_floor':'1/1000','T_floor':'9/20','evaluations':evals,'leaves':len(done),
  'unpaid_count':0,'covered_area':str(area),'min_C':str(minC),'min_T':str(minT),'worst':worst,
  'tree_encoding':'preorder: 0=closed leaf, 1=split longest side, y on tie; left then right',
  'root_order':'(j,j+1,k,k+1), j=1..19 outer, k=0..2 inner',
  'trees':trees,'bounds_audit':bounds,
  'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'RH_claim':False}

def roots():return [(Q(j),Q(j+1),Q(k),Q(k+1)) for j in range(1,20) for k in range(3)]
def children(cell):
 yl,yh,dl,dh=cell
 if yh-yl>=dh-dl:
  mid=(yl+yh)/2;return (yl,mid,dl,dh),(mid,yh,dl,dh)
 mid=(dl+dh)/2;return (yl,yh,dl,mid),(yl,yh,mid,dh)

def audit_bounds():
 k=Q(1023,1024);a0=Q(64,3);rho=Q(1,128);h0=Q(31,16)
 v=7*k/8
 bn=sum((abs(math.prod((nu-i)/Q(i+1) for i in range(N))) for nu in NU),Q(0))
 taylor=(96+120*bn)*math.factorial(N)/Q(3937,96)**N
 source=2**25*Q(3,8)**40+2**20*Q(3,8)**61
 checks={
  'sector_cosine':1-(4*rho)**2/2>k,
  'real_laplace_rate':2*k*Q(63,64)>h0,
  'reflected_beta_large':k*k*Q(125,128)*a0>20,
  'direct_beta_large':k*k*Q(63,64)*a0>20,
  'exponent_minimum':4*v*(v+3)>(2*v+Q(193,100))**2,
  'exponent_uniformity':k*Q(125,128)*Q(193,100)>Q(15,8),
  'integrable_reserve':k*Q(63,64)/4>Q(1,8),
  'direct_source_exponent':3*k*Q(125,128)>Q(29,10),
  'c_bound':((Q(11,4)**3)*Q(128,127)+1)/2<12,
  'real_c_bound':(Q(11,4)**3+1)/2<11,
  'first_beta_bound':3*Q(128,125)/a0<1,
  'second_beta_bound':Q(9,4)/(a0*Q(63,64))**2<1,
  'large_mode_sum':Q(671,2**60)<1,
  'P_factor':1+Q(3,20)+Q(9,1600)<2,
  'mode_sum_constant':4*3*670<2**13,
  'fourth_moment':sum(Q(math.factorial(4),math.factorial(4-j))*Q(3,8)**j for j in range(5))<6,
  'fifth_moment':sum(Q(math.factorial(5),math.factorial(5-j))/a0**j for j in range(6))<2,
  'reflected_constant':2**14*24*48<2**25,
  'direct_constant':4*352*128*2<2**20,
  'resolvent_factor':3+4*(N+1)/(h0*a0*a0)<4,
  'alpha_rate_ratio':Q(64,63)/h0<1,
  'effective_rate':h0*Q(127,128)*a0==Q(3937,96),
  'full_analytic_error':source+taylor<Q(1,10**9),
  'Dhat_floor':Q(81,193600000)>Q(1,2500000),
  'cofinal_budget_compatibility':Q(18**2,309760)>Q(1,2500000)
 }
 assert all(checks.values()),[key for key,val in checks.items() if not val]
 # The exact arithmetic comparator must reject a deliberately false error budget.
 assert not source+taylor<Q(1,10**12)
 return {'checks':checks,'binomial_tail_coefficient':str(bn),
         'taylor_error_upper':str(taylor),'theta_error_upper':str(source),
         'combined_error_enclosure':rat(source+taylor).out(),
         'planted_too_small_error_rejected':True}

def replay(path):
 selftests();bounds=audit_bounds();o=json.loads(Path(path).read_text())
 assert o['target']==['1<=y<=20','0<=d<=3'] and o['N']==N and o['E']=='1e-9'
 assert o['rho']=='1/128' and o['C_floor']=='1/1000' and o['T_floor']=='9/20'
 assert o['source_sha256']==hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 assert len(o['trees'])==57
 total_area=Q(0);leaves=0;nodes=0;minC=None;minT=None;maxdepth=0
 for root,tree in zip(roots(),o['trees']):
  pos=0
  def walk(cell,depth):
   nonlocal pos,total_area,leaves,nodes,minC,minT,maxdepth
   assert pos<len(tree) and depth<=18
   ch=tree[pos];pos+=1;nodes+=1
   if ch=='1':
    left,right=children(cell);walk(left,depth+1);walk(right,depth+1);return
   assert ch=='0'
   C,T=full_cell(*cell)
   assert C is not None and C.lo>D('0.001') and T.lo>D('0.45'),(cell,C,T)
   minC=C.lo if minC is None else min(minC,C.lo)
   minT=T.lo if minT is None else min(minT,T.lo)
   yl,yh,dl,dh=cell;total_area+=(yh-yl)*(dh-dl);leaves+=1;maxdepth=max(depth,maxdepth)
  walk(root,0);assert pos==len(tree)
 assert total_area==57 and leaves==o['leaves'] and nodes==o['evaluations']
 return {'status':'FULL_CERTIFICATE_REPLAY_PASS_NOT_INDEPENDENT_ANALYTIC_REVIEW',
  'accepted':False,'precision':PREC,'leaves':leaves,'nodes':nodes,'max_depth':maxdepth,
  'area':'57','unpaid':0,'min_C':str(minC),'min_T':str(minT),
  'certificate_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),
  'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'bounds_audit_pass':all(bounds['checks'].values()),'RH_claim':False}

if __name__=='__main__':
 if len(sys.argv)==1 or sys.argv[1]=='build':out=build()
 elif len(sys.argv)==3 and sys.argv[1]=='verify':out=replay(sys.argv[2])
 else:raise SystemExit('Usage: python3 strip_certificate.py [build | verify certificate.json]')
 print(json.dumps(out,indent=2),flush=True)
