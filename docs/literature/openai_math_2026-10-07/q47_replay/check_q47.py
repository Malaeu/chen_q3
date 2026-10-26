#!/usr/bin/env python3
"""Q47 exact checks: finite Dirichlet algebra, full signed return and source framing.
Standard library only. Rational fixtures are NOT production CCM cells.
"""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
import hashlib, json, re, sys

NAME='PROSHKA_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47_2026-10-26.txt'
SIZE=129191
LF=2357
SHA='072b38a5e63f8411daf467eceb6ad2598b5c462fda7116cfbf9857cb7be9f11b'
HEAD=re.compile(rb'^BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n',re.M)

def verify(raw: bytes) -> dict:
    if len(raw)!=SIZE or raw.count(b'\n')!=LF or hashlib.sha256(raw).hexdigest()!=SHA:
        raise ValueError('canonical packet mismatch')
    raw.decode('utf-8')
    if b'\r' in raw or not raw.endswith(b'\n'): raise ValueError('newline convention')
    if not raw.startswith(b'OPERATIVE_CLASS: TRY_CCM_SOURCE_DERIVED_JOINT_COMPENSATION_Q47\n'):
        raise ValueError('wrong request')
    pos=0; rows=[]
    for i in range(1,11):
        h=HEAD.search(raw,pos)
        if not h or h[1]!=f'S{i}'.encode(): raise ValueError('source order')
        start=h.end(); end=start+int(h[3]); body=raw[start:end]
        if len(body)!=int(h[3]) or body.count(b'\n')!=int(h[4]): raise ValueError('source length')
        if hashlib.sha256(body).hexdigest()!=h[5].decode(): raise ValueError('source hash')
        body.decode('utf-8')
        suffix=b'\nEND_SOURCE '+h[1]+b'\n'
        if raw[end:end+len(suffix)]!=suffix: raise ValueError('source boundary')
        rows.append(dict(id=h[1].decode(),name=h[2].decode(),bytes=len(body),lf=body.count(b'\n'),
                         sha256=h[5].decode(),start_byte=start,end_byte=end,
                         start_line=raw[:start].count(b'\n')+1,end_line=raw[:end].count(b'\n')))
        pos=end+len(suffix)
    if raw[pos:].strip(): raise ValueError('extra trailing bytes')
    return dict(packet=NAME,bytes=SIZE,lf=LF,sha256=SHA,source_count=10,
                all_source_frames_verified=True,sources=rows)

def factor(n):
    if n<1: raise ValueError('positive integer required')
    out={}; p=2
    while p*p<=n:
        while n%p==0: out[p]=out.get(p,0)+1; n//=p
        p+=1
    if n>1: out[n]=out.get(n,0)+1
    return out

def mu(n):
    fs=factor(n)
    return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)

def lladd(a,b):
    c=a.copy()
    for p,v in b.items(): c[p]=c.get(p,F())+v
    return {p:v for p,v in c.items() if v}

def llscale(a,s): return {p:v*s for p,v in a.items() if v*s}
def logn(n): return {p:F(e) for p,e in factor(n).items()}
def lam(n):
    fs=factor(n)
    return {next(iter(fs)):F(1)} if len(fs)==1 else {}
def divs(n): return [d for d in range(1,n+1) if n%d==0]
def alt(n): return 1 if n%2 else -1

def inv_alt(n):
    j=0
    while n%2==0: j+=1; n//=2
    return mu(n)*(1 if j==0 else 2**(j-1))

def dyadic(n):
    return {2:F(n)} if n>1 and n&(n-1)==0 else {}

def poly(x,co): return sum((F(v)*x**j for j,v in enumerate(co)),F())
def alt_abel(b,co):
    b=F(b); direct=sum((alt(n)*poly(F(n),co) for n in range(1,int(b)+1)),F())
    top=sum(alt(n) for n in range(1,int(b)+1))*poly(b,co)
    integral=F(); x=F(1)
    while x<b:
        k=int(x); y=min(b,F(k+1)); A=sum(alt(n) for n in range(1,k+1))
        integral+=A*(poly(y,co)-poly(x,co)); x=y
    return direct,top,integral

def zero(n): return [[F() for _ in range(n)] for _ in range(n)]
def eye(n):
    a=zero(n)
    for i in range(n): a[i][i]=F(1)
    return a

def madd(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def mscale(a,s): return [[s*x for x in row] for row in a]
def mm(a,b):
    n=len(a)
    return [[sum((a[i][k]*b[k][j] for k in range(n)),F()) for j in range(n)] for i in range(n)]
def mt(a): return [list(row) for row in zip(*a)]

def mv(a,v): return [sum((x*y for x,y in zip(row,v)),F()) for row in a]
def dot(x,y): return sum((a*b for a,b in zip(x,y)),F())
def shift(n,d):
    a=zero(n)
    for j in range(1,n+1):
        if j*d<=n: a[j*d-1][j-1]=F(1)
    return a

def combination(n,coef):
    a=zero(n)
    for d in range(1,n+1): a=madd(a,mscale(shift(n,d),coef(d)))
    return a

def spec_log(n):
    # Rational specialization of FORMAL log-prime variables, not log approximations.
    return sum((F(p,p+1)*e for p,e in factor(n).items()),F())

def math_checks():
    mutations={}; counts={}; N=96
    for n in range(1,N+1):
        assert alt(n)==1-(2 if n%2==0 else 0)
        assert sum(alt(d)*inv_alt(n//d) for d in divs(n))==(1 if n==1 else 0)
        h=sum(2**j*mu(n//(2**j)) for j in range(n.bit_length()) if n%(2**j)==0)
        assert h==inv_alt(n)
        b={}
        for d in divs(n): b=lladd(b,llscale(logn(d),F(alt(d)*inv_alt(n//d))))
        expect=lladd(lam(n),llscale(dyadic(n),F(-1)))
        assert b==expect
        full=lladd(b,dyadic(n)); assert full==lam(n)
    counts['formal_coefficient_indices']=N
    counts['alternating_prefix_indices']=N
    for n in range(1,N+1): assert sum(alt(k) for k in range(1,n+1))==n%2
    fixtures=[(F(7,2),[1]),(F(6),[1,2,3]),(F(17,3),[2,-1,0,1]),
              (F(9),[81,-18,1]),(F(5),[5,-1])]
    for b,co in fixtures:
        val,top,integ=alt_abel(b,co); assert val==top-integ
    counts['alternating_abel_fixtures']=len(fixtures)
    val,top,integ=alt_abel(*fixtures[0]); mutations['drop_nonzero_upper_trace']=val!=-integ
    val,top,integ=alt_abel(*fixtures[2]); mutations['reverse_abel_integral_sign']=val!=top+integ
    mutations['omit_first_dyadic_return']=lladd(lam(2),llscale(dyadic(2),F(-1)))!=lam(2)
    mutations['drop_higher_dyadic_powers']=dyadic(4)!={}
    mutations['replace_dyadic_2power_by_1']=dyadic(8)!={2:F(1)}
    mutations['replace_inverse_by_mu']=inv_alt(4)!=mu(4)
    # A faithful finite quotient of the Dirichlet algebra, NOT a production L2 carrier.
    n=9; I=eye(n)
    Z=combination(n,lambda d:F(1,d)); Mi=combination(n,lambda d:F(mu(d),d))
    D=madd(I,mscale(shift(n,2),-F(1))) # sigma=1: 2^(1-sigma)=1
    Di=combination(n,lambda d:F(1) if d&(d-1)==0 else F())
    Ea=combination(n,lambda d:F(alt(d),d)); Ei=combination(n,lambda d:F(inv_alt(d),d))
    Ep=combination(n,lambda d:-F(alt(d),d)*spec_log(d))
    Dp=mscale(shift(n,2),spec_log(2))
    B=combination(n,lambda d:F(sum(lam(d).get(p,F())*F(p,p+1) for p in lam(d)),d))
    Y=mm(Dp,Di); Be=mscale(mm(Ep,Ei),-1)
    assert mm(Z,Mi)==I and mm(Ea,Ei)==I and mm(D,Di)==I
    assert mm(D,Z)==Ea and madd(Be,Y)==B
    fr=[F((-1)**j,j+1) for j in range(n)]
    fi=[F(j%3-1,j+2) for j in range(n)]
    for f in (fr,fi):
        x=mv(Ei,f); y=mv(Di,f)
        assert mv(Ea,x)==f and mv(D,y)==f
        slope=2*(dot(f,mv(Ep,x))-dot(f,mv(Dp,y)))
        assert -slope==2*dot(f,mv(B,f))
    counts['exact_rational_operator_dimension']=n
    counts['complex_energy_components']=2
    # Continuous-source control is performed after changing BOTH source channels.
    G=mscale(madd(shift(n,2),shift(n,3)),F(1,3))
    Bec=madd(G,mscale(Y,-1))
    assert madd(madd(Bec,Y),mscale(G,-1))==zero(n)
    # Whole Hermitian source congruence, including the continuous term.
    Leta=madd(mscale(madd(mm(mt(Ea),Ep),mm(mt(Ep),Ea)),-1),
              mm(mm(mt(Ea),madd(madd(Y,mt(Y)),mscale(madd(G,mt(G)),-1))),Ea))
    whole=madd(madd(B,mt(B)),mscale(madd(G,mt(G)),-1))
    assert mm(mm(mt(Ei),Leta),Ei)==whole
    counts['full_hermitian_congruence']=1
    mutations['drop_centering_output']=madd(Bec,Y)!=zero(n)
    # A synthetic projector tests the illegality of an interposed compression.
    P=eye(n)
    for i in (0,1):
        for j in (0,1): P[i][j]-=F(1,2)
    assert mm(P,P)==P
    mutations['insert_intermediate_projector']=mm(mm(P,mm(D,Z)),P)!=mm(mm(mm(mm(P,D),P),Z),P)
    mutations['drop_complex_mixed_terms']=2*dot(fr,mv(B,fr))+2*dot(fi,mv(B,fi))!=0
    assert all(mutations.values())
    return dict(scope='Exact finite algebra and rational nonproduction fixtures only',
                passed=True,counts=counts,planted_errors_detected=mutations,
                first_eta_log_derivative_coefficient={'n':2,'log2_coefficient':-1},
                returned_coefficient={'n':2,'log2_coefficient':1},
                asymptotic_signed_inequality_certified=False)

def main():
    if len(sys.argv)!=2: raise SystemExit('usage: python3 check_q47.py CANONICAL_Q47.txt')
    raw=Path(sys.argv[1]).read_bytes(); provenance=verify(raw)
    bad=bytearray(raw);bad[provenance['sources'][0]['start_byte']+100]^=1
    try: verify(bytes(bad))
    except ValueError: provenance['single_byte_corruption_detected']=True
    else: raise AssertionError('missed corrupt byte')
    result=dict(provenance=provenance,mathematics=math_checks(),historical_code_executed=False,
                lean=False,arb=False,production_spectrum=False,independent_audit=False)
    txt=json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    Path('q47_checks.json').write_text(txt,encoding='utf-8');print(txt,end='')
if __name__=='__main__': main()
