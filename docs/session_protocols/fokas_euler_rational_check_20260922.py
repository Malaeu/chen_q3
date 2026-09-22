from fractions import Fraction as F

def val(p,x): return sum(c*x**i for i,c in enumerate(p))
def diff(p): return [i*p[i] for i in range(1,len(p))]
def integ(p,a,b): return sum(c*(b**(i+1)-a**(i+1))/F(i+1) for i,c in enumerate(p))
def mul(p,q):
 r=[F(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):r[i+j]+=a*b
 return r
count=0
for d in range(1,9):
 p=[-F(1,d+1)]+[F(0)]*(d-1)+[F(1)]
 dp=diff(p); ddp=diff(dp)
 for a in range(1,7):
  for b in range(a+1,23):
   t=F(a,b); N=int(1/t); f=1/t-N
   lhs=sum(val(p,k*t) for k in range(1,N+1))
   pieces=F(0)
   for k in range(N+1):
    lo=k*t; hi=min((k+1)*t,F(1))
    if lo>=hi:continue
    B=[F(k*k+k)+F(1,6),-F(2*k+1)/t,1/t**2]
    pieces+=integ(mul(B,ddp),lo,hi)
   rhs=-val(p,F(0))/2+(F(1,2)-f)*val(p,F(1))+t/2*((f*f-f+F(1,6))*val(dp,F(1))-F(1,6)*val(dp,F(0)))-t/2*pieces
   assert lhs==rhs,(d,t,lhs,rhs)
   count+=1
print('PASS',count,'exact rational polynomial/mesh identities; no Ferrers family certification')
