"""Candidate enclosure of one full-source origin jet; no RH/global ODD2 claim.
Decimal directed arithmetic and widened correctly-rounded exp; exact Machin pi.
All intervals include the entire real cell, not just quadrature sample points.
"""
import argparse, json, math, platform, time
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction

PREC = 40
DN = Context(prec=PREC, rounding=ROUND_FLOOR)
UP = Context(prec=PREC, rounding=ROUND_CEILING)
NEAR = Context(prec=PREC, rounding=ROUND_HALF_EVEN)
Z = Decimal(0)
O = Decimal(1)

class B:
    __slots__ = ('lo','hi')
    def __init__(self, lo, hi=None):
        self.lo=lo if isinstance(lo,Decimal) else Decimal(lo)
        self.hi=self.lo if hi is None else (hi if isinstance(hi,Decimal) else Decimal(hi))
        assert self.lo<=self.hi
    def __add__(self,other):
        other=box(other)
        return B(DN.add(self.lo,other.lo),UP.add(self.hi,other.hi))
    __radd__=__add__
    def __neg__(self):return B(self.hi.copy_negate(),self.lo.copy_negate())
    def __sub__(self,other):return self+-box(other)
    def __rsub__(self,other):return box(other)+-self
    def __mul__(self,other):
        other=box(other)
        pairs=((self.lo,other.lo),(self.lo,other.hi),(self.hi,other.lo),(self.hi,other.hi))
        pairs=tuple(pairs)
        return B(min(DN.multiply(x,y) for x,y in pairs),max(UP.multiply(x,y) for x,y in pairs))
    __rmul__=__mul__
    def __truediv__(self,other):
        other=box(other)
        assert other.lo>0
        return self*B(DN.divide(O,other.hi),UP.divide(O,other.lo))
    def square(self):
        hi=max(UP.multiply(self.lo,self.lo),UP.multiply(self.hi,self.hi))
        lo=Z if self.lo<=0<=self.hi else min(DN.multiply(self.lo,self.lo),DN.multiply(self.hi,self.hi))
        return B(lo,hi)
    def exp(self):
        return B(NEAR.next_minus(NEAR.exp(self.lo)),NEAR.next_plus(NEAR.exp(self.hi)))
    def abs_upper(self):return max(self.lo.copy_abs(),self.hi.copy_abs())
    def out(self):return [str(self.lo),str(self.hi)]

def box(x):return x if isinstance(x,B) else B(x)
def rat(x):
    x=Fraction(x)
    return B(DN.divide(Decimal(x.numerator),Decimal(x.denominator)),UP.divide(Decimal(x.numerator),Decimal(x.denominator)))
def atan_inv_bounds(q,n):
    s=sum((Fraction((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),Fraction(0))
    t=Fraction((-1)**n,(2*n+1)*q**(2*n+1))
    return min(s,s+t),max(s,s+t)
a,b=atan_inv_bounds(5,60)
c,d=atan_inv_bounds(239,20)
PI=B(rat(16*a-4*d).lo,rat(16*b-4*c).hi)
assert PI.lo>3 and PI.hi<4
P={0:[0,-6,4],1:[0,-15,30,-8],2:[0,Fraction(-75,2),165,-112,16],3:[0,Fraction(-375,4),Fraction(1635,2),-1058,360,-32]}
P={j:[rat(x) for x in p] for j,p in P.items()}
D={}
for j,p in P.items():
    bj=sum((Fraction(x.lo) for x in p if x.lo>=0),Fraction(0))-sum((Fraction(x.lo) for x in p if x.lo<0),Fraction(0))
    nu=Fraction(4*j+9,4)
    D[j]=rat(Fraction(16,15)*bj*nu**math.ceil(nu))
T={j:(D[j]*(-PI*rat(Fraction(25,2))).exp()).hi for j in D}
TAIL={j:(D[j].square()/(2*PI)*(-PI*B(4).exp()).exp()).hi for j in (1,2,3)}

def values(v, js=(1,2,3)):
    ev=(2*v).exp(); evhalf=(v/2).exp()
    sums={j:B(0) for j in js}
    for n in range(1,5):
        z=PI*n*n*ev
        ez=(-z).exp()
        for j in js:
            p=B(0)
            for a in reversed(P[j]):p=p*z+a
            sums[j]=sums[j]+p*ez
    return {j:evhalf*sums[j] for j in js}

def run(n):
    assert n>0 and n&(n-1)==0
    start=time.monotonic()
    h=rat(Fraction(2,n)); assert h.lo==h.hi
    sums={j:B(0) for j in (1,2,3)}
    maxima={j:Z for j in sums}
    for i in range(n):
        v=B(DN.multiply(Decimal(i),h.lo),UP.multiply(Decimal(i+1),h.hi))
        ff=values(v)
        for j in sums:
            maxima[j]=max(maxima[j],ff[j].abs_upper())
            sums[j]=sums[j]+h*v*ff[j].square()
    full={};errors={}
    for j in sums:
        err=(2*(2*B(maxima[j])*B(T[j])+B(T[j]).square())).hi
        errors[j]=err
        full[j]=B(max(Z,DN.subtract(sums[j].lo,err)),UP.add(UP.add(sums[j].hi,err),TAIL[j]))
    at0=values(B(0),(0,2))
    ff0={j:at0[j]+B(T[j].copy_negate(),T[j]) for j in (0,2)}
    k=4*full[1]-2*ff0[0].square()
    a=-4*full[2]-2*ff0[0]*ff0[2]
    b=4*full[3]-6*ff0[2].square()
    det=k*b-a.square()
    return {'status':'POSITIVE_ENCLOSURE_CANDIDATE' if det.lo>0 else 'INCONCLUSIVE_ENCLOSURE','python':platform.python_version(),'precision':PREC,'cells':n,'theta_modes':4,'v_max':2,'pi':PI.out(),'I':{j:x.out() for j,x in full.items()},'truncated_maxima':{j:str(x) for j,x in maxima.items()},'theta_tail_amplitude_bounds':{j:str(x) for j,x in T.items()},'integral_theta_errors':{j:str(x) for j,x in errors.items()},'v_tail_bounds':{j:str(x) for j,x in TAIL.items()},'Phi0':ff0[0].out(),'Phi2':ff0[2].out(),'K11':k.out(),'K13':a.out(),'K33':b.out(),'jet_determinant':det.out(),'seconds':time.monotonic()-start,'scope':'Raw Phi source; true normalized f jet determinant is this value divided by A^4. One origin jet, not global ODD2/RH. Independent arithmetic and analytic review required.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--cells',type=int,default=16384);args=ap.parse_args()
    print(json.dumps(run(args.cells),indent=2),flush=True)
