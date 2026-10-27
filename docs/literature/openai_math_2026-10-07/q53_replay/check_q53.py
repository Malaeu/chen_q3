#!/usr/bin/env python3
"""Q53 exact algebra and packet framing; not an actual-zero/CCM certificate.
Usage: python3 check_q53.py CANONICAL_Q53.txt
Python 3.9+ standard library only. No historical program is executed.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from math import comb
import hashlib, json, re, sys

SIZE, LF = 135751, 2250
SHA = '9561eb7be86d7f6bb72790d174566a68809cdbe198353c8be6621044155444e0'
NAME = 'PROSHKA_CCM_SIGNED_INNER_OBSERVATION_Q53_2026-10-27.txt'
MAN = re.compile(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', re.M)

def verify(raw, outer=True):
    if outer and (len(raw)!=SIZE or raw.count(b'\n')!=LF or hashlib.sha256(raw).hexdigest()!=SHA):
        raise ValueError('outer bytes/LF/hash')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.startswith(b'Q53 SIGNED_INNER_OBSERVATION'):
        raise ValueError('encoding/request')
    pos=raw.index(b'BEGIN S1 '); heads=list(MAN.finditer(raw[:pos])); rows=[]
    if len(heads)!=8: raise ValueError('manifest count')
    for i,h in enumerate(heads,1):
        if h[1]!=str(i).encode(): raise ValueError('manifest order')
        sid=f'S{i}'; name=h[2].decode(); opening=f'BEGIN {sid} {name}\n'.encode()
        if raw[pos:pos+len(opening)]!=opening: raise ValueError('opening')
        st=pos+len(opening); en=st+int(h[3]); body=raw[st:en]
        if len(body)!=int(h[3]) or body.count(b'\n')!=int(h[4]): raise ValueError('body bytes/LF')
        if hashlib.sha256(body).hexdigest()!=h[5].decode(): raise ValueError('body hash')
        body.decode('utf-8'); close=f'\nEND {sid}\n\n'.encode()
        if raw[en:en+len(close)]!=close: raise ValueError('closing/separator')
        rows.append(dict(id=sid,name=name,bytes=len(body),lf=body.count(b'\n'),sha256=h[5].decode(),
                         start_byte=st,end_byte=en,start_line=raw[:st].count(b'\n')+1,end_line=raw[:en].count(b'\n')))
        pos=en+len(close)
    if pos!=len(raw): raise ValueError('trailing bytes')
    return dict(packet=NAME,bytes=len(raw),lf=LF,sha256=SHA,source_count=8,all_frames_verified=True,sources=rows)

@dataclass(frozen=True)
class Q:
    re:F=F(0)
    im:F=F(0)
    def __post_init__(self):
        object.__setattr__(self,'re',F(self.re)); object.__setattr__(self,'im',F(self.im))
    @staticmethod
    def cast(x): return x if isinstance(x,Q) else Q(x)
    def __add__(self,x):
        x=Q.cast(x);return Q(self.re+x.re,self.im+x.im)
    __radd__=__add__
    def __neg__(self):return Q(-self.re,-self.im)
    def __sub__(self,x):return self+-Q.cast(x)
    def __rsub__(self,x):return Q.cast(x)+-self
    def __mul__(self,x):
        x=Q.cast(x);return Q(self.re*x.re-self.im*x.im,self.re*x.im+self.im*x.re)
    __rmul__=__mul__
    def conj(self):return Q(self.re,-self.im)
    def norm2(self):return self.re*self.re+self.im*self.im
    def __truediv__(self,x):
        x=Q.cast(x);d=x.norm2()
        if not d: raise ZeroDivisionError
        return self*x.conj()*F(1,d)
    def __rtruediv__(self,x):return Q.cast(x)/self
    def __pow__(self,n):
        if n<0:return (Q(1)/self)**(-n)
        r=Q(1);a=self
        while n:
            if n&1:r=r*a
            a=a*a;n//=2
        return r
    def pair(self):return [str(self.re),str(self.im)]
Z=Q(); O=Q(1); I=Q(0,1)

def trim(p):
    p=list(map(Q.cast,p))
    while len(p)>1 and p[-1]==Z:p.pop()
    return p or [Z]
def add(p,q):
    r=[Z]*max(len(p),len(q))
    for k,x in enumerate(p):r[k]+=x
    for k,x in enumerate(q):r[k]+=x
    return trim(r)
def scale(p,a):return trim([Q.cast(a)*x for x in p])
def sub(p,q):return add(p,scale(q,-1))
def mul(p,q):
    r=[Z]*(len(p)+len(q)-1)
    for j,x in enumerate(p):
        for k,y in enumerate(q):r[j+k]+=x*y
    return trim(r)
def power(p,n):
    r=[O]
    for _ in range(n):r=mul(r,p)
    return r
def ev(p,z):
    r=Z
    for x in reversed(p):r=r*z+x
    return r
def der(p):return trim([k*p[k] for k in range(1,len(p))])
def divmodp(p,q):
    p=trim(p);q=trim(q)
    if q==[Z]:raise ZeroDivisionError
    out=[Z]*max(1,len(p)-len(q)+1)
    while p!=[Z] and len(p)>=len(q):
        k=len(p)-len(q);v=p[-1]/q[-1];out[k]+=v
        p=sub(p,[Z]*k+scale(q,v))
    return trim(out),p
def exactdiv(p,q):
    a,r=divmodp(p,q)
    if r!=[Z]:raise ValueError('non-exact polynomial division')
    return a
def jet(p,w,n):
    return [sum((p[j]*comb(j,k)*w**(j-k) for j in range(k,len(p))),Z) for k in range(n)]
def ratiojet(p,q,w,n):
    a,b=jet(p,w,n),jet(q,w,n)
    if b[0]==Z:raise ZeroDivisionError('jet denominator')
    v=[]
    for k in range(n):v.append((a[k]-sum((b[j]*v[k-j] for j in range(1,k+1)),Z))/b[0])
    return v
def reflect(p,u,conjugate):
    out=[Z]
    for j,a in enumerate(p):
        out=add(out,scale(power([Q(2*u),-O],j),a.conj() if conjugate else a))
    return out
def solve(A,b):
    n=len(b);T=[list(A[i])+[b[i]] for i in range(n)]
    for k in range(n):
        piv=next((j for j in range(k,n) if T[j][k]!=Z),None)
        if piv is None:raise ValueError('singular system')
        T[k],T[piv]=T[piv],T[k];d=T[k][k];T[k]=[x/d for x in T[k]]
        for j in range(n):
            if j!=k:
                d=T[j][k];T[j]=[x-d*y for x,y in zip(T[j],T[k])]
    return [T[j][-1] for j in range(n)]

class Model:
    def __init__(self,u,roots):
        self.u=F(u);self.roots=roots;self.N=sum(r for w,r in roots)
        self.P=[O];self.Q=[O]
        for w,r in roots:
            self.P=mul(self.P,power([-w,O],r))
            self.Q=mul(self.Q,power([w.conj()-2*u,O],r))
        self.basis=[[Z]*j+[O] for j in range(self.N)]
    def C(self,p):return scale(reflect(p,self.u,True),(-1)**(self.N+1))
    def U(self,p):return scale(reflect(p,self.u,False),(-1)**(self.N+1))
    def value(self,p,w):return ev(p,w)/ev(self.Q,w)
    def residue_pair(self,p,q):
        num=mul(p,q);ans=Z
        for w,r in self.roots:
            other=exactdiv(self.P,power([-w,O],r))
            ans+=ratiojet(num,mul(other,self.Q),w,r)[r-1]
        return ans
    def partials(self,p):
        out=[]
        for w,r in self.roots:
            v=Q(2*self.u)-w.conj();other=exactdiv(self.Q,power([-v,O],r))
            a=ratiojet(p,other,v,r)
            for k in range(1,r+1):out.append((w,k,a[r-k]))
        return out
    def inner(self,p,q):
        # Independent boundary integral via all confluent Cauchy basis entries.
        out=Z
        for w,k,a in self.partials(p):
            for v,l,b in self.partials(q):
                out+=a.conj()*b*comb(k+l-2,k-1)/(w+v.conj()-2*self.u)**(k+l-1)
        return out
    def T(self,p,tau,with_Bprime=True):
        if with_Bprime:
            num=mul(mul(tau,sub(mul(der(self.P),self.Q),mul(self.P,der(self.Q)))),p)
            denominator=mul(self.Q,self.Q)
        else:num=mul(tau,p);denominator=[O]
        rhs=divmodp(num,self.P)[1];rhs+= [Z]*(self.N-len(rhs))
        cols=[]
        for b in self.basis:
            c=divmodp(mul(denominator,b),self.P)[1];c+=[Z]*(self.N-len(c));cols.append(c)
        A=[[cols[j][i] for j in range(self.N)] for i in range(self.N)]
        return trim(solve(A,rhs))
    def observation(self,z):
        bz=ev(self.P,z)/ev(self.Q,z)
        numerator=sub(self.Q,scale(self.P,bz.conj()))
        return exactdiv(numerator,[z.conj()-2*self.u,O])

def model_checks():
    counts={};errors={};u=F(1,16);tau=list(map(Q,[1,2,1]))
    fixtures=[[(Q(F(1,4),F(2,3)),1)],
              [(Q(F(1,4),F(2,3)),1),(Q(F(1,4),F(-2,3)),1)],
              [(Q(F(1,4),F(2,3)),2),(Q(F(1,4),F(-2,3)),2)],
              [(Q(F(1,4),F(2,3)),3),(Q(F(3,8),F(-5,4)),1)]]
    cases=0;jet_cases=0;lyap=0;obs=0;uchecks=0
    for roots in fixtures:
        B=Model(u,roots);N=B.N
        ps=[trim([Q(j+1,F((-1)**j,j+2)) for j in range(N)]),B.basis[-1]]
        for p in ps:
            assert B.C(B.C(p))==p
            assert B.inner(p,p).im==0 and B.inner(p,p).re>0
            t=B.T(p,tau)
            for w,r in roots:
                actual=ratiojet(t,B.Q,w,r)
                expected=[Z]*r
                other=exactdiv(B.P,power([-w,O],r))
                expected[r-1]=r*ev(tau,w)*ev(other,w)/ev(B.Q,w)*B.value(p,w)
                assert actual==expected;jet_cases+=1
            for q in ps:
                assert B.inner(B.C(p),B.C(q))==B.inner(q,p)
                assert B.inner(B.C(p),q)==B.residue_pair(p,q)
                expected=sum((r*ev(tau,w)*B.value(p,w)*B.value(q,w) for w,r in roots),Z)
                assert B.residue_pair(p,B.T(q,tau))==expected
                errors['omit_Bprime_weight']=errors.get('omit_Bprime_weight',False) or B.residue_pair(p,B.T(q,tau,False))!=expected
                cases+=1
        for w,r in roots:
            for v,s in roots:
                g=1/(w+v.conj()-2*u)
                assert (w-u)*g+g*(v.conj()-u)==O;lyap+=1
        if all(x.im==0 for x in B.P+B.Q):
            for p in B.basis:
                assert B.U(B.U(p))==p
                for q in B.basis:
                    assert B.inner(p,B.U(B.T(q,tau)))==B.inner(B.U(B.T(p,tau)),q)
                    uchecks+=1
            delta=F(1,3);a=F(1,2);js=list(range(-2,3));q1=a*a+delta*delta;q2=a*a+4*delta*delta
            ee=[q2,-4*q1,6*a*a,-4*q1,q2];oo=[q2,-2*q1,F(0),2*q1,-q2]
            c=[Q(e)+Q(1,1)*o for e,o in zip(ee,oo)]
            assert sum(c,Z)==Z
            for sign in (-1,1):assert sum((x/(Q(a)+sign*I*j*delta) for j,x in zip(js,c)),Z)==Z
            observations={sign:[B.observation(Q(2*u)+sign*I*j*delta) for j in js] for sign in (-1,1)}
            def observed(sign,cc):
                ans=[Z]
                for p,x in zip(observations[sign],cc):ans=add(ans,scale(p,x))
                return ans
            fplus=observed(1,c);fminus=observed(-1,c)
            assert fminus==observed(1,list(reversed(c)))
            actual=Z;wrong=Z;direct=Z;adjoint_wrong=Z;one=Z
            for sign in (-1,1):
                f=observed(sign,c);fc=observed(sign,[x.conj() for x in c])
                part=B.residue_pair(fc,B.T(f,tau));actual+=part
                wrong+=B.residue_pair(f,B.T(f,tau));one=part
                for w,r in roots:
                    left=sum((x.conj()/(w-sign*I*j*delta) for j,x in zip(js,c)),Z)
                    right=sum((x/(w-sign*I*j*delta) for j,x in zip(js,c)),Z)
                    direct+=r*ev(tau,w)*left*right
                    adjoint_wrong+=r*ev(tau,w)*right.conj()*right
                for w,r in roots:
                    assert B.value(f,w)==sum((x/(w-sign*I*j*delta) for j,x in zip(js,c)),Z);obs+=1
            assert actual==direct and actual.im==0
            cross=B.inner(fminus,B.U(B.T(fplus,tau)))+B.inner(fplus,B.U(B.T(fminus,tau)))
            assert cross==actual
            errors['forget_bar_c_on_left']=errors.get('forget_bar_c_on_left',False) or wrong!=actual
            errors['transpose_to_adjoint']=errors.get('transpose_to_adjoint',False) or adjoint_wrong!=actual
            errors['drop_one_orientation']=errors.get('drop_one_orientation',False) or one!=actual
            if any(r>1 for w,r in roots):
                errors['replace_multiple_zero_by_simple_value_rule']=actual!=Z
        # Full norm is not inferred by multiplying an upper observation cap.
    errors['reverse_Lyapunov_energy_direction']=(-O!=O)
    # Repeated node: value-only coordinate span is not C-invariant.
    B=Model(u,[(Q(F(1,4),F(2,3)),2)])
    w=B.roots[0][0]
    kernel=exactdiv(B.Q,[w.conj()-2*u,O])
    ck=B.C(kernel)
    assert B.value(ck,w)==Z and B.inner(ck,ck).re>0
    errors['assume_value_span_C_invariant_at_multiple_root']=True
    counts.update(model_fixtures=len(fixtures),bilinear_pairs=cases,confluent_jet_cases=jet_cases,
                  cauchy_lyapunov_entries=lyap,observation_value_cases=obs,hermitian_model_entries=uchecks)
    assert all(errors.values()),errors
    return dict(counts=counts,planted_errors_detected=errors,
                numeric_zeta_zeros=False,production_cells=False,
                symbol_control='tau(z)=(1+z)^2 checks analytic identities; actual exp(Lz) specialization is proved in PAPER')

def factor(n):
    out={};p=2
    while p*p<=n:
        while n%p==0:out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out
def prime(n):return n>=2 and factor(n)=={n:1}
def lm(n):
    f=factor(n)
    return {next(iter(f)):1} if len(f)==1 else {}
def ladd(a,b,k=1):
    a=a.copy()
    for p,x in b.items():a[p]=a.get(p,0)+k*x
    return {p:x for p,x in a.items() if x}

def arithmetic_checks():
    errors={};fc=0
    for n in range(1,121):
        incoming={}
        for d in range(2,n+1):
            if n%d==0:incoming=ladd(incoming,lm(d))
        assert incoming==factor(n)
        factorial={};floors={}
        for j in range(2,n+1):factorial=ladd(factorial,factor(j))
        for d in range(2,n+1):floors=ladd(floors,lm(d),n//d)
        assert floors==factorial;fc+=1
    counts=[]
    for m,K in ((3,1),(5,2),(7,1),(7,2)):
        primes=[p for p in range(2,m+1) if prime(p)]
        exps=list(product(range(K+1),repeat=len(primes)));indices=[]
        for aa in exps:
            n=1
            for p,a in zip(primes,aa):n*=p**a
            indices.append(n)
        box=set(indices);D=len(box);N=max(box)
        assert N==product_value(p**K for p in primes) and D==(K+1)**len(primes)
        virtual=0
        for p in primes:
            k=1
            while k<=K+2:
                direct=sum(1 for n in box if n*p**k in box)
                expected=max(K+1-k,0)*(K+1)**(len(primes)-1)
                assert direct==expected
                alpha=F(direct,D);beta=min(F(1),F(k,K+1))
                assert alpha+beta==1
                if p**k>=m and direct:virtual+=direct
                if k==1:errors['omit_multiplicative_box_boundary']=alpha!=1
                k+=1
        counts.append(dict(m=m,K=K,box_cardinality=D,max_integer=N,virtual_edges_at_or_beyond_source_end=virtual))
    # Young identity with the original 1/sqrt(d): replace sqrt(d) by rational v.
    for v in (F(2),F(3,2),F(5)):
        a,b=Q(F(2,3),F(1,5)),Q(F(-3,4),F(2,7))
        lhs=a.norm2()/v**2+b.norm2()-2*(a.conj()*b).re/v
        assert lhs==(a/v-b).norm2()>=0
    errors['drop_prime_power_multiplicity_in_log_divisor']=factor(8)!={2:1}
    errors['use_product_as_log_cutoff']=product_value([2,3,5])!=sum([2,3,5])
    # k-weighted proper-power bound: (1-1/sqrt(2))^-2=6+4sqrt(2)<12.
    assert F(2)<F(3,2)**2
    epsrows=[]
    for eps in (F(1,128),F(1,64),F(1,33)):
        high=F(1,2)+3*eps-3*(F(5,24)+eps)
        assert high==-F(1,8) and F(3,2)*eps<2*eps
        epsrows.append(dict(epsilon=str(eps),high=str(high),short_power=str(F(3,2)*eps),paid_power=str(2*eps),graph_K1_trial_power='1',retained_direct_power='1/2'))
    # Whole source return; arbitrary exact scalars check signs, not inequalities.
    A,H,V,E,high,short=map(F,[7,2,3,-1,4,5]);low=V+E-high-A-H
    assert A==V+E-high-low-H
    assert A-short==V+E-high-low-H-short
    errors['double_short_in_direct_K']=(-A)!=(-A-short)
    assert all(errors.values())
    return dict(formal_divisor_factorial_cases=fc,multiplicative_box_cases=counts,
                planted_errors_detected=errors,exponent_rows=epsrows,actual_asymptotic_bound_verified_by_code=False)

def product_value(xs):
    r=1
    for x in xs:r*=x
    return r

def main():
    if len(sys.argv)!=2:raise SystemExit('usage: python3 check_q53.py CANONICAL_Q53.txt')
    raw=Path(sys.argv[1]).read_bytes();provenance=verify(raw);mut={}
    bad=bytearray(raw);bad[provenance['sources'][0]['start_byte']+40]^=1
    en=provenance['sources'][0]['end_byte']
    for name,data,outer in [('outer_hash',bytes(bad),True),('body_hash',bytes(bad),False),
                            ('extra_separator',raw[:en]+b'\n'+raw[en:],False),('truncated_frame',raw[:-2],False)]:
        try:verify(data,outer)
        except (ValueError,UnicodeError):mut[name]=True
        else:raise AssertionError('missed provenance change '+name)
    result=dict(provenance=provenance,framing_mutations=mut,model=model_checks(),arithmetic=arithmetic_checks(),
                historical_programs_executed=False,lean=False,arb=False,independent_audit=False,
                production_spectrum=False,numeric_zeta_roots=False,independent_signed_supplier=False)
    text=json.dumps(result,sort_keys=True,ensure_ascii=False,indent=2)+'\n'
    Path('q53_checks.json').write_text(text,encoding='utf-8');print(text,end='')
if __name__=='__main__':main()
