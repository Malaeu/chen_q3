#!/usr/bin/env python3
"""Exact local controls for Q45; no theta numerics or spectral certification.
Uses only Python standard library. Logarithms of positive rationals are kept
as formal rational combinations of log(prime). Polynomial fixtures test maps,
not actual-source asymptotics.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

class LogLinear:
    def __init__(self, terms=None):
        self.t = {int(k): F(v) for k,v in (terms or {}).items() if v}
    def __add__(self, other):
        if not isinstance(other, LogLinear): other=LogLinear({0:other})
        z=self.t.copy()
        for p,v in other.t.items(): z[p]=z.get(p,F())+v
        return LogLinear(z)
    __radd__=__add__
    def __neg__(self): return self * -1
    def __sub__(self, other): return self + (-other if isinstance(other,LogLinear) else -F(other))
    def __rsub__(self, other): return -self + other
    def __mul__(self, scalar): return LogLinear({p:v*F(scalar) for p,v in self.t.items()})
    __rmul__=__mul__
    def __truediv__(self, scalar): return self * (1/F(scalar))
    def __eq__(self, other):
        if not isinstance(other, LogLinear): other=LogLinear({0:other})
        return self.t==other.t
    def serial(self): return {str(p):str(v) for p,v in sorted(self.t.items())}

def factors(n):
    if n<1: raise ValueError('positive integer required')
    out={}; p=2
    while p*p<=n:
        while n%p==0: out[p]=out.get(p,0)+1; n//=p
        p+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def logq(x):
    x=F(x)
    if x<=0: raise ValueError('positive rational required')
    out=factors(x.numerator)
    for p,e in factors(x.denominator).items(): out[p]=out.get(p,0)-e
    return LogLinear(out)

def mu(n):
    fs=factors(n)
    return 0 if any(e>=2 for e in fs.values()) else (-1)**len(fs)

def lam(n):
    fs=factors(n)
    return logq(next(iter(fs))) if len(fs)==1 else LogLinear()

def power(x,r):
    """Exact rational power, only for deliberately perfect-power fixtures."""
    x=F(x); r=F(r)
    if r.denominator==1: return x**r.numerator
    q=r.denominator
    def root(n):
        lo,hi=0,n+1
        while hi-lo>1:
            mid=(lo+hi)//2
            if mid**q<=n: lo=mid
            else: hi=mid
        if lo**q!=n: raise ValueError('fixture has a nonrational power')
        return lo
    return F(root(x.numerator),root(x.denominator))**r.numerator

def ant_log(t,d,j):
    j=F(j); den=j+1
    if den==0: raise ValueError('j=-1 not used')
    return power(t,den)*(logq(F(t)/d)/den-1/(den*den))

def continuous(d,m,j):
    return (ant_log(m,d,j)-ant_log(d,d,j))/d

def inner_sum(d,m,j):
    return sum((logq(k)*power(d*k,j) for k in range(1,int(F(m)/d)+1)),LogLinear())

def beta_primitive(t,d,j,k):
    j=F(j); den=j+1
    return k*power(t,j)*logq(F(t)/d) - power(t,den)/d*(j/den*logq(F(t)/d)+1/(den*den))

def euler_parts(d,m,j):
    m=F(m); a=F(d); integ=LogLinear()
    while a<m:
        k=int(a/d); b=min(m,F(d*(k+1)))
        if b<=a: raise AssertionError('nonadvancing floor cell')
        integ += beta_primitive(b,d,j,k)-beta_primitive(a,d,j,k)
        a=b
    top=(int(m/d)-m/d)*power(m,j)*logq(m/d)
    return top,integ

def direct_long(m,R,j):
    return sum((mu(d)*inner_sum(d,m,j) for d in range(R+1,int(m)+1)),LogLinear())

def floor_channels(t,R):
    t=F(t); Q=LogLinear(); primitive=LogLinear(); N=0
    for d in range(R+1,int(t)+1):
        z=mu(d); kmax=int(t/d)
        N+=z*kmax
        Q+=z*kmax*logq(t/d)
        primitive+=sum((z*logq(t/F(d*k)) for k in range(1,kmax+1)),LogLinear())
    return Q,N,primitive

def short_factorial(t,R):
    return sum((mu(d)*sum((logq(k) for k in range(1,int(F(t)/d)+1)),LogLinear())
                for d in range(1,min(R,int(t))+1)),LogLinear())

def psi(t): return sum((lam(n) for n in range(1,int(t)+1)),LogLinear())

def check_all():
    results={}; counts={}; mutations={}
    # Endpoint-sensitive Euler maps. Integer m/d and fractional m/d both included.
    fixtures=[(1,F(8),0),(3,F(10),0),(3,F(10),1),(2,F(17,2),2),
              (3,F(25,3),-2),(5,F(5),1),(2,F(9),0),(5,F(31,3),1)]
    for d,m,j in fixtures:
        top,integ=euler_parts(d,m,j)
        assert inner_sum(d,m,j)==continuous(d,m,j)+top-integ
    counts['euler_endpoint_fixtures']=len(fixtures)
    # Complete signed hyperbola, both long and short coefficients.
    cfg=[(F(12),1),(F(31,2),3),(F(32),5),(F(49,3),2)]
    for m,R in cfg:
        Q,N,I=floor_channels(m,R)
        assert Q-I==psi(m)-short_factorial(m,R)
        for j in (0,1,-2):
            joined=sum((mu(d)*(continuous(d,m,j)+euler_parts(d,m,j)[0]-euler_parts(d,m,j)[1])
                        for d in range(R+1,int(m)+1)),LogLinear())
            assert joined==direct_long(m,R,j)
    counts['hyperbola_configurations']=len(cfg)
    counts['weighted_joint_fixtures']=3*len(cfg)
    # Independent prime-power definition vs mu*log; finite algebra only.
    for n in range(1,65):
        got=sum((mu(d)*logq(n//d) for d in range(1,n+1) if n%d==0),LogLinear())
        assert got==lam(n)
    counts['coefficient_indices']=64
    # Common-edge two-orientation identity for F(x)=exp(-x/4), x=0.
    # This non-theta fixture tests the algebra only. All used roots are rational.
    a=F(1,4); sig=F(1,2)
    kernel_rows=[]
    for d,m in ((1,16),(16,81),(16,256),(81,81)):
        d=F(d); m=F(m); gap=logq(m/d); rhs=LogLinear()
        for sign in (1,-1):
            b=sig+sign*a
            K0m=power(m,sign*a)/b
            K1m=power(m,sign*a)/(b*b)
            K1d=power(d,sign*a)/(b*b)
            rhs+=power(m,sig)/d*(gap*K0m-K1m)+K1d/power(d,sig)
        lhs=continuous(d,m,a-sig)+continuous(d,m,-a-sig)
        assert lhs==rhs
        kernel_rows.append({'d':str(d),'m':str(m),'value':lhs.serial()})
    counts['two_orientation_common_edge_fixtures']=len(kernel_rows)
    # Complex normalisation and the two complete mixed terms, Gaussian rationals.
    # Python complex is not used: pairs are exact rational real/imaginary parts.
    def add(z,w): return (z[0]+w[0],z[1]+w[1])
    def mult(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
    def conj(z): return (z[0],-z[1])
    cw=(F(1),F(1)); kap=(F(),F(1,2)) # 1/conj(1+i)^2 = i/2
    assert mult(mult(conj(cw),conj(cw)),kap)==(F(1),F())
    x=(F(2,3),F(-1,4)); z=(F(-2,5),F(7,9))
    lhs=mult(conj(add(x,z)),add(x,z))
    rhs=add(add(mult(conj(x),x),mult(conj(x),z)),add(mult(conj(z),x),mult(conj(z),z)))
    assert lhs==rhs
    counts['complex_rational_controls']=2
    # Deliberately bad versions must be distinguished.
    d,m,j=3,F(10),0; top,integ=euler_parts(d,m,j)
    mutations['drop_forcing_top']=inner_sum(d,m,j)!=(continuous(d,m,j)-integ)
    mutations['wrong_euler_sign']=inner_sum(d,m,j)!=(continuous(d,m,j)+top+integ)
    Q,N,I=floor_channels(F(31,2),3)
    mutations['drop_floor_derivative']=Q!=psi(F(31,2))-short_factorial(F(31,2),3)
    mutations['delete_prime_powers']=sum((lam(n) for n in range(1,17) if len(factors(n))==1
                                         and next(iter(factors(n).values()))==1),LogLinear())!=psi(16)
    # At d=m, only the lower K1 cancels the common top -K1 term.
    m=F(16); bad= -power(m,F(-1,2))*(power(m,a)/(sig+a)**2+power(m,-a)/(sig-a)**2)
    mutations['drop_lower_kernel_at_d_equals_m']=bad!=0
    mutations['replace_kappa_by_modulus']=mult(mult(conj(cw),conj(cw)),(F(1,2),F()))!=(F(1),F())
    assert all(mutations.values())
    results['scope']='Exact algebra and framing only; no production theta, zero or CCM spectrum'
    results['counts']=counts
    results['planted_errors_detected']=mutations
    results['common_edge_fixture_values']=kernel_rows
    results['checks_passed']=True
    return results

if __name__=='__main__':
    out=check_all()
    data=(json.dumps(out,ensure_ascii=False,sort_keys=True,indent=2)+'\n').encode()
    Path('check_q45_results.json').write_bytes(data)
    print(data.decode(),end='')
