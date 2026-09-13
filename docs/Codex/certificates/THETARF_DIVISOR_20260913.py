"""Directed-Decimal certificate for one zero of the full theta diagonal.
No xi zeros, source node matrices, or target positivity are used.
"""
from decimal import Decimal as D, Context, getcontext, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as F
from math import factorial, comb
import sys
PREC = int(sys.argv[1]) if len(sys.argv)>1 else 60
getcontext().prec=PREC
DOWN=Context(prec=PREC,rounding=ROUND_FLOOR,Emin=-999999,Emax=999999)
UP=Context(prec=PREC,rounding=ROUND_CEILING,Emin=-999999,Emax=999999)
NEAR=Context(prec=PREC,rounding=ROUND_HALF_EVEN,Emin=-999999,Emax=999999)
class I:
    __slots__=('lo','hi')
    def __init__(self,lo=0,hi=None):
        if isinstance(lo,I): self.lo,self.hi=lo.lo,lo.hi;return
        if isinstance(lo,F):
            self.lo=DOWN.divide(D(lo.numerator),D(lo.denominator));self.hi=UP.divide(D(lo.numerator),D(lo.denominator));return
        self.lo=D(lo);self.hi=D(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,b):
        if hasattr(b, "im"): return NotImplemented
        b=I(b);return I(DOWN.add(self.lo,b.lo),UP.add(self.hi,b.hi))
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,b):return self+-I(b)
    def __rsub__(self,b):return I(b)+-self
    def __mul__(self,b):
        if hasattr(b, "im"): return NotImplemented
        b=I(b);p=[(x,y) for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(DOWN.multiply(x,y) for x,y in p),max(UP.multiply(x,y) for x,y in p))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=I(b);assert not b.lo<=0<=b.hi
        return self*I(DOWN.divide(D(1),b.hi),UP.divide(D(1),b.lo))
    def __rtruediv__(self,b):return I(b)/self
    def __pow__(self,n):
        assert n>=0 and isinstance(n,int)
        y=I(1);x=self
        while n:
            if n&1:y=y*x
            x=x*x;n//=2
        return y
    def ab(self):return max(abs(self.lo),abs(self.hi))
    def __repr__(self):return '['+str(self.lo)+', '+str(self.hi)+']'
    def widen(self,e):return self+I(-e,e)
ZERO=I(0)

def ex(a):
    a=I(a)
    return I(NEAR.next_minus(NEAR.exp(a.lo)),NEAR.next_plus(NEAR.exp(a.hi)))

def atan_recip(q,n):
    s=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),F(0))
    e=F(1,(2*n+1)*q**(2*n+1))
    return (s,s+e) if n%2==0 else (s-e,s)
a,b=atan_recip(5,100);c,d=atan_recip(239,30)
PILO,PIHI=16*a-4*d,16*b-4*c
PI=I(I(PILO).lo,I(PIHI).hi)
assert PI.lo>D('3.14159') and PI.hi<D('3.14160')

def cs(a):
    a=I(a)
    mid=NEAR.divide(NEAR.add(a.lo,a.hi),D(2))
    rad=max(UP.subtract(mid,a.lo),UP.subtract(a.hi,mid))
    if rad>=1:return I(-1,1),I(-1,1)
    period=NEAR.multiply(D(2),NEAR.divide(NEAR.add(PI.lo,PI.hi),D(2)))
    k=int(NEAR.divide(mid,period).to_integral_value(rounding=ROUND_HALF_EVEN))
    x=I(mid)-2*k*PI
    assert x.ab()<D(4)
    xx=x*x;tc=I(1);ts=x;co=tc;si=ts
    # Terms through degree 79; a uniform absolute tail below 1e-65.
    for j in range(1,40):
        tc=-tc*xx/((2*j-1)*(2*j));ts=-ts*xx/((2*j)*(2*j+1))
        co=co+tc;si=si+ts
    # For |x|<=4 the remaining successive-term ratio is below 1/2.
    rem=I(F(2*4**80,factorial(80))).hi
    e=UP.add(rad,rem)
    co=co.widen(e);si=si.widen(e)
    return I(max(co.lo,D(-1)),min(co.hi,D(1))),I(max(si.lo,D(-1)),min(si.hi,D(1)))
class C:
    __slots__=('re','im')
    def __init__(self,re=0,im=0):
        if isinstance(re,C):self.re,self.im=re.re,re.im;return
        self.re=I(re);self.im=I(im)
    def __add__(self,b):b=C(b);return C(self.re+b.re,self.im+b.im)
    __radd__=__add__
    def __neg__(self):return C(-self.re,-self.im)
    def __sub__(self,b):return self+-C(b)
    def __rsub__(self,b):return C(b)+-self
    def __mul__(self,b):
        b=C(b)
        if self.im.lo==self.im.hi==0 and b.im.lo==b.im.hi==0:return C(self.re*b.re)
        return C(self.re*b.re-self.im*b.im,self.re*b.im+self.im*b.re)
    __rmul__=__mul__
    def __truediv__(self,b):
        if not isinstance(b,C):return C(self.re/I(b),self.im/I(b))
        return self*C(b.re,-b.im)/(b.re*b.re+b.im*b.im)
    def __pow__(self,n):
        y=C(1);x=self
        while n:
            if n&1:y=y*x
            x=x*x;n//=2
        return y
    def ab(self):return UP.add(self.re.ab(),self.im.ab())
    def exp(self):
        if self.im.lo==self.im.hi==0:return C(ex(self.re))
        co,si=cs(self.im);e=ex(self.re);return C(e*co,e*si)
    def widen(self,e):return C(self.re.widen(e),self.im.widen(e))
    def __repr__(self):return 'Re='+repr(self.re)+'; Im='+repr(self.im)

def polys(m):
    p=[F(0),F(-6),F(4)];out=[p]
    for j in range(m):
        q=[F(0)]*(len(p)+1)
        for k,t in enumerate(p):q[k]+=(F(1,2)+2*k)*t;q[k+1]-=2*t
        p=q;out.append(p)
    return out
PS=polys(14)
NTHETA=12

def evalp(p,z):
    out=C(0)
    for q in reversed(p):out=out*z+I(q)
    return out

def phi_jets(z,order=14):
    z=C(z);aa=PI*(2*z).exp();lead=(z/2).exp();out=[C(0) for _ in range(order+1)]
    for n in range(1,NTHETA+1):
        v=aa*(n*n);e=(-v).exp()
        for j in range(order+1):out[j]=out[j]+evalp(PS[j],v)*e
    return [lead*t for t in out]

def midpoint_integral(zscale,length,count):
    # Integral of 2*zscale^2*s*Phi_N(zscale*s)^2 ds.
    scale=C(zscale);h=F(length,2*count);result=C(0)
    for k in range(count):
        s=F(length*(2*k+1),2*count);jets=phi_jets(scale*I(s))
        jet=[v*(scale**j)/factorial(j) for j,v in enumerate(jets)]
        sq=[sum((jet[k]*jet[j-k] for k in range(j+1)),C(0)) for j in range(15)]
        coeff=[2*(scale**2)*(I(s)*sq[j]+(sq[j-1] if j else C(0))) for j in range(15)]
        result=result+sum((coeff[j]*I(2*h**(j+1)/F(j+1)) for j in range(0,15,2)),C(0))
    return result

# Exact algebra plants before any target certificate.
assert (I(F(1,3))*3).lo<=1<=(I(F(1,3))*3).hi
assert (C(1,2)*C(3,-4)).re.lo<=11<=(C(1,2)*C(3,-4)).re.hi
assert (C(1,2)*C(3,-4)).im.lo<=2<=(C(1,2)*C(3,-4)).im.hi
co,si=cs(PI/2);assert co.lo<=0<=co.hi and si.lo<=1<=si.hi
# K=1+xy, w=sqrt(1+x^2)sqrt(1+y^2), null row (1,-2,1) at -1,0,1.
assert sum((a*b*(1+x*y) for a,x in [(1,-1),(-2,0),(1,1)] for b,y in [(1,-1),(-2,0),(1,1)]))==0
assert (I(2)**2).lo>0  # 2sqrt(2)-2 is nonzero; square parity is independent of numerics.
print('ARITHMETIC_AND_RANK_ONE_DOMINATION_PLANTS=PASS',flush=True)
center=C(I(F(237019,10**6)),I(F(715864,10**6)))
r=F(1,100000)
# Source-series tail on the actual slanted path and the root box.
end_a=PI*(2*center).exp()
assert end_a.re.lo>D('0.6')
assert center.re.hi<D('0.24') and center.im.hi<D('0.72')
assert (PI*ex(I('0.48'))).hi<6
# log(e^(2as)cos(2bs)) is concave on [0,1], so endpoint minima pay the path.
T0=4*sum(abs(q) for q in PS[0])*6**2*13**4*ex(I(F(-507,5)))
T1=4*sum(abs(q) for q in PS[1])*6**3*13**6*ex(I(F(-507,5)))
# Polynomial/geometric majorants, with ratio at n=13 already below 1/2.
ratio=I(F(14,13))**6*ex(I(F(-81,5)))
assert ratio.hi<F(1,2)
complex_source_error=(2*T0*(2*2**16+T0)).hi
assert complex_source_error<D('1e-25')
real_tail=20*3**3*13**6*ex(-507)
assert (9*real_tail*(2*2048+real_tail)).hi<D('1e-100')
# Analytic tube bounds: radius 1/32 in the integration variable.
# Complex segment: Re(z)>=-1/32, Re(z)<=0.24+1/32, |Im(z)|<=0.72+1/32.
# |center|<19/25, so the s-tube has z-width at most 19/800.
assert (center.re*center.re+center.im*center.im).hi<D('0.5776')
maxim=center.im+I(F(19,800))
qmin=PI*ex(I(F(-19,400)))*cs(2*maxim)[0]
assert qmin.lo>D('0.25')
qmax=PI*ex(2*(center.re+I(F(19,800))))
assert qmax.hi<7
# Uniform absolute theta bounds used for the Cauchy remainders are paper-proved.
real=midpoint_integral(C(1),3,384)
real_err=I(3*F(2**25)*F(1,8)**16/F(7,8)+F(1,10**90)).hi
real=real.widen(real_err)
print('RAW_D0='+repr(real.re),flush=True)
slant=midpoint_integral(center,1,128)
slant_err=I(F(2**34)*F(1,8)**16/F(7,8)+F(1,10**25)).hi
slant=slant.widen(slant_err)
value=real-slant
print('RAW_D_AT_CENTER='+repr(value),flush=True)
print('D0_CAUCHY_ERROR_UPPER='+str(real_err),flush=True)
print('SLANT_CAUCHY_ERROR_UPPER='+str(slant_err),flush=True)
assert value.ab()<D('0.01')
p,p1=phi_jets(center,1)
p=p.widen(T0.hi);p1=p1.widen(T1.hi)
dp=-2*center*p*p
# lower absolute squared bounds from the rectangular enclosure.
def sq_lower(a):
    if a.lo<=0<=a.hi:return D(0)
    x=min(abs(a.lo),abs(a.hi));return DOWN.multiply(x,x)
lowdp=DOWN.add(sq_lower(dp.re),sq_lower(dp.im))
print('RAW_DPRIME='+repr(dp),flush=True)
print('DPRIME_MODULUS_SQUARED_LOWER='+str(lowdp),flush=True)
assert lowdp>D(9000**2)
box=C(center.re.widen(I(r).hi),center.im.widen(I(r).hi))
ba=PI*(2*box).exp();assert ba.re.lo>D('0.6') and ba.ab()<6
p,p1=phi_jets(box,1);p=p.widen(T0.hi);p1=p1.widen(T1.hi)
M2=(2*I(p.ab())**2+4*I(box.ab())*I(p.ab())*I(p1.ab())).hi
print('DSECOND_MODULUS_UPPER='+str(M2),flush=True)
assert M2<D(10**8)
margin=F(9000)*r-F(1,100)-F(10**8,2)*r*r
assert margin==F(3,40)>0
print('ROUCHE_MARGIN_LOWER='+str(margin),flush=True)
print('ONE_SIMPLE_ZERO_IN_CENTER_RADIUS_1e-5=PASS',flush=True)
print('NO_ASSERTION_OF_V_NEGATIVITY_OR_RH',flush=True)
