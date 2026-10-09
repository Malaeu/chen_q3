from fractions import Fraction as F
from itertools import product
from math import gcd

N=0

def mu_e(a): return 1 if a==0 else -1 if a==1 else 0

def e_local(i,j):
    return 1 if i==j==0 else -1 if i>=1 and j>=1 else 0

# Full two-variable coefficient convolution; two independent prime slots.
for a,b,c,d in product(range(6),repeat=4):
    l1=sum(e_local(i,j)*mu_e(a-i)*mu_e(b-j)
           for i in range(a+1) for j in range(b+1))
    l2=sum(e_local(i,j)*mu_e(c-i)*mu_e(d-j)
           for i in range(c+1) for j in range(d+1))
    expected=mu_e(a)*mu_e(b)*mu_e(c)*mu_e(d)*int(min(a,b)==0 and min(c,d)==0)
    assert l1*l2==expected
    N+=1
print('two-prime bivariate convolution:',N)

# Exact polynomial identities represented by coefficient dictionaries in X,Y,V.
def add(*ps):
    out={}
    for p in ps:
        for k,v in p.items(): out[k]=out.get(k,0)+v
    return {k:v for k,v in out.items() if v}
def neg(p):return {k:-v for k,v in p.items()}
def mul(p,q):
    out={}
    for a,x in p.items():
        for b,y in q.items():
            k=tuple(i+j for i,j in zip(a,b));out[k]=out.get(k,0)+x*y
    return {k:v for k,v in out.items() if v}
one={(0,0,0):1};X={(1,0,0):1};Y={(0,1,0):1};V={(0,0,1):1}
assert add(one,neg(V),neg(X),neg(Y))==add(mul(add(one,neg(V)),mul(add(one,neg(X)),add(one,neg(Y)))),neg(mul(add(one,neg(V)),mul(X,Y))),neg(mul(V,add(X,Y))))
N+=1
print('Euler correction rational identity: 1')

# Exact cyclic polynomial for all six powers of a sixth root of unity.
# Arithmetic in Z[z]/(z^2-z+1).
def cadd(a,b):return(a[0]+b[0],a[1]+b[1])
def cmul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]+a[1]*b[1])
def cpow(a,k):
    out=(1,0)
    for _ in range(k):out=cmul(out,a)
    return out
for a in range(6):
    z=cpow((0,1),a)
    poly=[cpow(z,j) for j in range(6)]
    ans=[(0,0)]*7
    for j,x in enumerate(poly):
        ans[j]=cadd(ans[j],x)
        zx=cmul(z,x);ans[j+1]=cadd(ans[j+1],(-zx[0],-zx[1]))
    assert ans==[(1,0)]+[(0,0)]*5+[(-1,0)]
    N+=1
print('sixth-power Euler cancellation: 6')

# Uniform rational budget: all functions affine in r, ell; their extrema are at vertices.
rmin=F(28,25);rmax=F(113,100);c0=F(1,10000);eta=F(1,200);b=F(1,40)
mins=[None]*3
for r in [rmin,rmax]:
    h=r*(1+c0);p=(h-1)/6;target=h-eta
    for ell in [r-F(1,100),r]:
        es=[p+1,p+F(7,12)+F(5,12)*ell-F(5,24)*b,
            p+F(1,6)+F(5,6)*ell-F(5,12)*b]
        for j,e in enumerate(es):
            m=target-e;assert m>0;N+=1
            mins[j]=m if mins[j] is None else min(mins[j],m)
assert min(mins)==F(551,100000)
assert eta-F(5,6)*rmax*c0==F(5887,1200000)
assert F(5887,1200000)>F(1,250)
N+=3
print('budget vertex inequalities: 12; additional rational identities: 3')
print('uniform raw margins:',[str(x) for x in mins])
for r in [rmin,F(5617,5000),rmax]:
    h=r*(1+c0);p=(h-1)/6
    print('r=',r,'head=',p+F(1,6)+F(5,6)*r,'target=',h-eta,
          'unpaid=',eta-F(5,6)*r*c0)

# Local positivity and exact gcd-return density, rational cosines.
# Let r=1/sqrt(q); use q perfect squares >=9 to keep r rational.
for q in [9,16,25,49,121]:
    from math import isqrt
    r=F(1,isqrt(q))
    for C in [F(-1),F(-1,2),F(0),F(1,2),F(1)]:
        den=1-2*r*C+r*r;m=(1-2*r*C)/den
        assert 0<m<1
        assert m+r*r/den==1
        N+=2
print('rational multiplier/return controls: 50 (not prime-family certification)')

# Planted omissions must be detected, not silently accepted.
truncated=sum(e_local(i,j)*mu_e(2-i)*mu_e(1-j)
              for i in range(2) for j in range(2))
assert truncated==1 # true coefficient of (2,1) is zero; missing (2,1) correction.
assert mu_e(1)*mu_e(1)==1 # true coprime (1,1) coefficient is zero.
N+=2
print('planted failures detected: 2')
print('TOTAL EXACT CONTROLS:',N)
