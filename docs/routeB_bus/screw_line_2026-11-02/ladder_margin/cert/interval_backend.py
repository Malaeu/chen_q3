"""Directed mpmath.iv fallback, with explicit dilogarithm series remainders.

This module implements only the operations exercised by certify.py.
All series truncation errors are enclosed; no mp nearest-rounding value is
used as a certified endpoint. Native python-flint remains the preferred path.
"""
import math,os
from decimal import Decimal,localcontext,ROUND_FLOOR,ROUND_CEILING
from mpmath import iv

class Context:
    @property
    def prec(self):return iv.prec
    @prec.setter
    def prec(self,bits):iv.prec=bits
ctx=Context()

def raw(x):return x.v if isinstance(x,arb) else iv.mpf(x)

class arb:
    def __init__(self,x=0):self.v=raw(x)
    @staticmethod
    def pi():return arb(iv.pi)
    @staticmethod
    def const_euler():return arb(iv.euler)
    @staticmethod
    def const_catalan():return arb(iv.catalan)
    def __add__(self,x):return arb(self.v+raw(x))
    __radd__=__add__
    def __sub__(self,x):return arb(self.v-raw(x))
    def __rsub__(self,x):return arb(raw(x)-self.v)
    def __mul__(self,x):return arb(self.v*raw(x))
    __rmul__=__mul__
    def __truediv__(self,x):return arb(self.v/raw(x))
    def __rtruediv__(self,x):return arb(raw(x)/self.v)
    def __pow__(self,n):return arb(self.v**n)
    def __neg__(self):return arb(-self.v)
    def __abs__(self):return arb(abs(self.v))
    def __gt__(self,x):return bool(self.v.a>raw(x).b)
    def __lt__(self,x):return bool(self.v.b<raw(x).a)
    def lower(self):return arb(self.v.a)
    def upper(self):return arb(self.v.b)
    def log(self):return arb(iv.log(self.v))
    def exp(self):return arb(iv.exp(self.v))
    def sqrt(self):return arb(iv.sqrt(self.v))
    def sinh(self):return arb((iv.exp(self.v)-iv.exp(-self.v))/2)
    def atan(self):return arb(iv.atan2(self.v,iv.mpf(1)))
    def atanh(self):return arb(iv.log((1+self.v)/(1-self.v))/2)
    def contains(self,x):return bool(self.v.a<=raw(x).a and self.v.b>=raw(x).b)
    def is_finite(self):return math.isfinite(float(self.v.a)) and math.isfinite(float(self.v.b))
    def str(self,digits=90):
        def endpoint(raw_tuple,rounding):
            sign,mantissa,exponent,_=raw_tuple
            if not mantissa:return '0'
            if exponent>=0:value=Decimal(mantissa<<exponent)
            else:value=Decimal((0,tuple(map(int,str(mantissa*5**(-exponent)))),exponent))
            if sign:value=value.copy_negate()
            with localcontext() as context:
                context.prec=digits;context.rounding=rounding
                return str(+value)
        low,high=self.v._mpi_
        return '['+endpoint(low,ROUND_FLOOR)+', '+endpoint(high,ROUND_CEILING)+']'

def _series(z):
    """Li2(z), |z|<.71, rectangular error from a geometric tail."""
    radius=abs(z).b
    assert radius<iv.mpf('.71')
    power=z;total=iv.mpc(0);target=iv.mpf(os.environ.get('LADDER_LI2_TAIL_TARGET','1e-50'))
    assert target.a>0 and target.b<iv.mpf('1e-20')
    for k in range(1,1000):
        total+=power/(k*k)
        rem=radius**(k+1)/((k+1)**2*(1-radius))
        if rem.b<target.a:
            error=iv.mpf([-rem.b,rem.b])
            return total+iv.mpc(error,error)
        power*=z
    raise ArithmeticError('series truncation budget')

def _real_li2(x):
    if x.a>=0:
        assert x.b<1
        if x.b<=iv.mpf('.5'):
            # The series enclosure is complex; its real component encloses
            # the real-valued result. Imaginary width is irrelevant here.
            return _series(iv.mpc(x,0)).real
        y=1-x
        return iv.pi**2/6-iv.log(x)*iv.log(y)-_series(iv.mpc(y,0)).real
    assert x.b<0 and x.a>-1
    return _real_li2(x*x)/2-_real_li2(-x)

class acb:
    def __init__(self,real=0,imag=0):self.v=iv.mpc(raw(real),raw(imag))
    @classmethod
    def from_value(cls,z):a=cls();a.v=z;return a
    @property
    def real(self):return arb(self.v.real)
    @property
    def imag(self):return arb(self.v.imag)
    def polylog(self,order):
        assert order==2
        z=self.v
        if z.imag.a==0 and z.imag.b==0:
            return acb(_real_li2(z.real),0)
        assert z.real.a==0 and z.real.b==0 and z.imag.a>0
        transformed=z/(z-1)
        # Principal-branch identity holds here: 1-z is in the right
        # half-plane and z is on the positive imaginary axis.
        value=-_series(transformed)-iv.log(1-z)**2/2
        return acb.from_value(value)
