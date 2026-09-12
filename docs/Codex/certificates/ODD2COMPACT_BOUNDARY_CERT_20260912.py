"""Full-theta box certificate. All arithmetic affecting enclosures is directed.
No grid of node samples is used: X is a whole interval, including independent s,t.
"""
import json, math, platform, os, hashlib
from decimal import Decimal, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as Q
from functools import lru_cache
PREC=int(os.environ.get("ODD2COMPACT_PREC", "40"))
assert PREC >= 40
DN=Context(prec=PREC,rounding=ROUND_FLOOR)
UP=Context(prec=PREC,rounding=ROUND_CEILING)
NEAR=Context(prec=PREC,rounding=ROUND_HALF_EVEN)
class B:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        self.lo=lo if isinstance(lo,Decimal) else Decimal(lo)
        self.hi=self.lo if hi is None else (hi if isinstance(hi,Decimal) else Decimal(hi))
        assert self.lo<=self.hi
    def __add__(self,o):
        o=box(o);return B(DN.add(self.lo,o.lo),UP.add(self.hi,o.hi))
    __radd__=__add__
    def __neg__(self):return B(self.hi.copy_negate(),self.lo.copy_negate())
    def __sub__(self,o):return self+-box(o)
    def __rsub__(self,o):return box(o)+-self
    def __mul__(self,o):
        o=box(o);p=((self.lo,o.lo),(self.lo,o.hi),(self.hi,o.lo),(self.hi,o.hi))
        return B(min(DN.multiply(a,b) for a,b in p),max(UP.multiply(a,b) for a,b in p))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=box(o);assert o.lo>0
        return self*B(DN.divide(Decimal(1),o.hi),UP.divide(Decimal(1),o.lo))
    def square(self):
        hi=max(UP.multiply(self.lo,self.lo),UP.multiply(self.hi,self.hi))
        lo=Decimal(0) if self.lo<=0<=self.hi else min(DN.multiply(self.lo,self.lo),DN.multiply(self.hi,self.hi))
        return B(lo,hi)
    def exp(self):return B(NEAR.next_minus(NEAR.exp(self.lo)),NEAR.next_plus(NEAR.exp(self.hi)))
    def absup(self):return max(self.lo.copy_abs(),self.hi.copy_abs())
    def out(self):return [str(self.lo),str(self.hi)]
def box(x):return x if isinstance(x,B) else B(x)
def rat(q):
    q=Q(q);return B(DN.divide(Decimal(q.numerator),Decimal(q.denominator)),UP.divide(Decimal(q.numerator),Decimal(q.denominator)))
def symmetric(a):return B(a.copy_negate(),a)
def ipow(x,n):
    ans=B(1)
    for _ in range(n):ans=ans*x
    return ans
def atan(q,n):
    s=sum((Q((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),Q(0))
    r=Q((-1)**n,(2*n+1)*q**(2*n+1));return min(s,s+r),max(s,s+r)
a,b=atan(5,60);c,d=atan(239,20)
PI=B(rat(16*a-4*d).lo,rat(16*b-4*c).hi)
ORDER=8;MODES=6;VMAX=3
P=[[Q(0),Q(-6),Q(4)]]
for j in range(ORDER+1):
    old=P[-1];new=[Q(0)]*(len(old)+1)
    for k,q in enumerate(old):new[k]+=(Q(1,2)+2*k)*q;new[k+1]-=2*q
    P.append(new)
D=[]
for j,p in enumerate(P):
    nu=Q(4*j+9,4)
    D.append(rat(Q(16,15)*sum(abs(q) for q in p)*nu**math.ceil(nu)))
PB=[[rat(q) for q in p] for p in P]
# Full source tail outside n<=MODES. Applies at every absolute argument >=0.
TH=[(q*(-PI*rat(Q((MODES+1)**2,2))).exp()).hi for q in D]
# The common full integration-tail bound for K,K_s,K_st and 2*V_t(x,0), |s|,|t|<=1.
ITAIL=(B(6)/PI*(D[0]+D[1]).square()*(-PI*B(4).exp()).exp()).hi
@lru_cache(maxsize=100000)
def ff(lo,hi):
    if hi<0:
        r=ff(hi.copy_negate(),lo.copy_negate());return tuple((-v if j%2 else v) for j,v in enumerate(r))
    if lo<0:
        top=max(lo.copy_abs(),hi)
        r=ff(Decimal(0),top)
        return tuple((symmetric(v.absup()) if j%2 else v) for j,v in enumerate(r))
    x=B(lo,hi);ex=(2*x).exp();eh=(x/2).exp();s=[B(0) for _ in P]
    for n in range(1,MODES+1):
        z=PI*(n*n)*ex;ez=(-z).exp()
        for j,poly in enumerate(PB):
            p=B(0)
            for q in reversed(poly):p=p*z+q
            s[j]=s[j]+p*ez
    return tuple(eh*s[j]+symmetric(TH[j]) for j in range(len(P)))
def vals(x):return ff(x.lo,x.hi)
def prod(a,b,r,q,k):
    if k<0:return B(0)
    s=B(0)
    for j in range(k+1):s=s+math.comb(k,j)*a[r+j]*b[q+k-j]
    return s
def gd(a,b,w,r,q,k):
    g=w*prod(a,b,r,q,k)
    if k:g=g+2*k*prod(a,b,r,q,k-1)
    if r:g=g+r*prod(a,b,r-1,q,k)
    if q:g=g+q*prod(a,b,r,q-1,k)
    return g
def integrands(v,X,k):
    a,b,c=vals(v+X),vals(v-X),vals(v)
    wp=2*(v+X);wm=2*v;w0=X+2*v
    return (
        gd(a,a,wp,0,0,k)-gd(a,b,wm,0,0,k),
        gd(a,a,wp,1,0,k)-gd(a,b,wm,1,0,k),
        gd(a,a,wp,1,1,k)+gd(a,b,wm,1,1,k),
        2*gd(a,c,w0,0,1,k))
def run_panel(j=0,n=128):
    assert n>0 and not n&(n-1)
    # Fixed spatial panel in the predeclared interval [1/2,3/4].
    left=Q(1,2)+Q(j,4096);right=left+Q(1,4096)
    assert 0<=j<1024
    X=B(rat(left).lo,rat(right).hi)
    h=Q(VMAX,n)
    weights=[rat(h**(k+1)/(2**k*(k+1)*math.factorial(k))) for k in range(0,ORDER,2)]
    remweight=rat(h**(ORDER+1)/(2**ORDER*(ORDER+1)*math.factorial(ORDER)))
    sums=[B(0) for _ in range(4)];er=[B(0) for _ in range(4)]
    for i in range(n):
        v=rat((Q(i)+Q(1,2))*h)
        for k,w in zip(range(0,ORDER,2),weights):
            gs=integrands(v,X,k)
            for z in range(4):sums[z]=sums[z]+w*gs[z]
        cell=B(rat(i*h).lo,rat((i+1)*h).hi)
        gs=integrands(cell,X,ORDER)
        for z in range(4):er[z]=er[z]+remweight*B(gs[z].absup())
    for z in range(4):sums[z]=sums[z]+symmetric((er[z]+ITAIL).hi)
    A,C,E,Baxis=sums
    kappa=B('0.0864','0.0877') # inherited full raw origin enclosure
    axis=kappa*A-Baxis.square()
    # These three entries bound only the diagonal jet (x,x), not X^2.
    ic_lower=DN.subtract((A*E).lo,UP.multiply(C.absup(),C.absup()))
    F=vals(X)[0]
    return {"panel":j,"x_interval":X.out(),"v_cells":n,"taylor_order":ORDER,"modes":MODES,"v_max":VMAX,
        "entries":dict(zip(('K','K_s','K_st','axis_K_t'),[v.out() for v in sums])),
        "v_taylor_errors":[v.out() for v in er],"full_v_tail":str(ITAIL),"theta_tails":[str(v) for v in TH],
        "Phi_on_X":F.out(),"axis_minor":axis.out(),"diagonal_jet_lower":str(ic_lower),
        "axis_normalized_lower":str((B(axis.lo)/F.square()).lo),
        "diagonal_jet_normalized_lower":str((B(ic_lower)/F.square().square()).lo),
        "positive_axis":axis.lo>0,"positive_diagonal_jet":ic_lower>0,
        "precision":PREC,"python":platform.python_version()}
# Additional explicit boundary check, no claim of an independent s,t square
# from the earlier diagonal-only integrands (where s-t=0 exactly).
def full_tail(r,q):
    b=B(0)
    if r:b=b+r*D[r-1]*D[q]
    if q:b=b+q*D[r]*D[q-1]
    return ((6*D[r]*D[q]+b)/(2*PI)*(-PI*B(4).exp()).exp()).hi

def derivative_budgets(n=256):
    X=B('0.5','0.500244140625');Y=rat(Q(1,256));Z=B(-Y.hi,Y.hi)
    h=Q(3,n);m03=B(0);m13=B(0)
    for i in range(n):
        v=B(rat(i*h).lo,rat((i+1)*h).hi)
        a,b=vals(v+X),vals(v+Z)
        c=gd(a,b,X+2*v+Z,0,3,0)
        d=gd(b,b,2*v+2*Z,1,3,0)
        m03=m03+2*rat(h)*B(c.absup())
        m13=m13+2*rat(h)*B(d.absup())
    m03=m03+full_tail(0,3);m13=m13+full_tail(1,3)
    return m03.hi,m13.hi

def square_integrands(v,X,k):
    a,b=vals(v+X),vals(v-X)
    width=UP.subtract(X.hi,X.lo)
    wp=2*(v+X);wm=2*v+symmetric(width)
    return (gd(a,a,wp,0,0,k)-gd(a,b,wm,0,0,k),
            gd(a,a,wp,1,0,k)-gd(a,b,wm,1,0,k),
            gd(a,a,wp,1,1,k)+gd(a,b,wm,1,1,k))

def square_run(n=128):
    X=B('0.5',rat(Q(1,2)+Q(1,2**20)).hi)
    h=Q(3,n);s=[B(0) for _ in range(3)];err=[B(0) for _ in range(3)]
    for i in range(n):
        v=rat((Q(i)+Q(1,2))*h)
        for k in range(0,ORDER,2):
            weight=rat(h**(k+1)/(2**k*(k+1)*math.factorial(k)))
            for j,g in enumerate(square_integrands(v,X,k)):s[j]=s[j]+weight*g
        v=B(rat(i*h).lo,rat((i+1)*h).hi)
        weight=rat(h**(ORDER+1)/(2**ORDER*(ORDER+1)*math.factorial(ORDER)))
        for j,g in enumerate(square_integrands(v,X,ORDER)):err[j]=err[j]+weight*B(g.absup())
    s=[g+symmetric((e+ITAIL).hi) for g,e in zip(s,err)]
    lo=DN.subtract((s[0]*s[2]).lo,UP.multiply(s[1].absup(),s[1].absup()))
    return {'square':X.out(),'K':s[0].out(),'K_s_and_K_t':s[1].out(),'K_st':s[2].out(),
            'N_lower':str(lo),'C_lower':str((B(lo)/B(s[0].hi).square()).lo),
            'Delta_gap2_lower':str((B(lo)*(B(s[0].lo)/B(s[0].hi)).square()).lo),
            'errors':[e.out() for e in err],'full_tail':str(ITAIL),'positive':lo>0}


def self_tests():
    assert B(-1,2).square().out()==['0','4']
    assert (B(1)*B(1)-B(2).square()).out()==['-3','-3']
    assert (B(2)*B(2)-B(1).square()).out()==['3','3']
    assert B(0).exp().lo<1<B(0).exp().hi
    assert PI.lo>3 and PI.hi<4
    assert P[1]==[Q(0),Q(-15),Q(30),Q(-8)]
    # Independent s,t must retain a nonzero interval for s-t.
    X=B('0.5','0.500244140625')
    width=UP.subtract(X.hi,X.lo);wm=symmetric(width)
    assert wm.lo <= DN.subtract(X.lo,X.hi) < 0 < wm.hi
    # A negative enclosure lower endpoint alone does not certify a negative value.
    straddle=B(-1,1);assert not(straddle.hi<0) and not(straddle.lo>=0)
    return 'EXACT_PLANTS_AND_ARITHMETIC_PASS'

def main():
    plants=self_tests()
    axis=run_panel(0,128)
    m03,m13=derivative_budgets(256)
    a=B(*axis['entries']['K']);b=B(*axis['entries']['axis_K_t'])
    h=B(*axis['axis_minor']);y=rat(Q(1,256))
    loss=y.square()*(B(a.hi)*B(m13)/3+B(b.absup())*B(m03)/3+B(m03).square()*y.square()/36)
    floor=DN.subtract(h.lo,loss.hi)
    square=square_run(128)
    # Rational outward simplifications used in the written proof.
    assert h.lo > Decimal('0.000000123')
    assert m03 < Decimal('0.75') and m13 < Decimal(171)
    assert a.lo > Decimal('0.00004') and a.hi < Decimal('0.000045')
    assert b.absup() < Decimal('0.0019')
    assert floor > Decimal('0.00000005')
    assert Decimal(square['N_lower']) > Decimal('0.000000002')
    assert Decimal(square['K'][0]) > Decimal('0.000043')
    assert Decimal(square['K'][1]) < Decimal('0.000044')
    assert Decimal(square['Delta_gap2_lower']) > Decimal('0.000000001')
    source_hash=hashlib.sha256(open(__file__,'rb').read()).hexdigest()
    return {'status':'TWO_NEW_SOURCE_SIGN_FAMILIES_CANDIDATE_GLOBAL_ODD2_OPEN',
        'source_sha256':source_hash,'python':platform.python_version(),
        'precision':PREC,'plants':plants,'pi':PI.out(),
        'axis_jets':axis,
        'axis_extension':{'y_max':y.out(),'M03':str(m03),'M13':str(m13),
            'loss_upper':str(loss.hi),'Delta_over_y2_lower':str(floor)},
        'diagonal_square':square,
        'scope':'Raw Phi; normalized determinant bounds divide by A^4; all complex coefficients.',
        'global_ODD2':False,'global_IC':False,'RH_claim':False}

if __name__=='__main__':
    print(json.dumps(main(),indent=2),flush=True)
