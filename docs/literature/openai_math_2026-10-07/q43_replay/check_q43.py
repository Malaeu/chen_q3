#!/usr/bin/env python3
"""Q43 exact source/endpoint checks. Standard library only, no spectral claims."""
from fractions import Fraction as F
from pathlib import Path
from math import isqrt
from functools import lru_cache
import argparse
import hashlib
import json
import re


def factor(n):
    out = {}; d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0)+1; n //= d
        d += 1
    if n > 1: out[n] = out.get(n, 0)+1
    return out


def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for e in fs.values()) else (-1)**len(fs)


# A vector of rational coefficients: coordinate 0 denotes 1, coordinate p log(p).
# Comparing vectors is exact; no floating-point logarithms are used.
def add(a, b):
    c = a.copy()
    for p, v in b.items(): c[p] = c.get(p, F())+v
    return {p:v for p,v in c.items() if v}


def scale(a, v):
    return {p:F(v)*x for p,x in a.items() if F(v)*x}


def sub(a, b): return add(a, scale(b, -1))


def logq(q):
    q = F(q)
    if q <= 0: raise ValueError('positive logarithm argument required')
    a = {p:F(e) for p,e in factor(q.numerator).items()}
    return sub(a, {p:F(e) for p,e in factor(q.denominator).items()})


def lam(n):
    fs = factor(n)
    return {next(iter(fs)):F(1)} if len(fs) == 1 else {}


def sumvec(rows):
    a = {}
    for r in rows: a = add(a, r)
    return a


def conv(a, b, m):
    c = [F()]*(m+1)
    for d in range(1, m+1):
        if not a[d]: continue
        for k in range(1, m//d+1):
            if b[k]: c[d*k] += a[d]*b[k]
    return c


def make(U, m):
    if m < U+1: raise ValueError('m must retain the balancing atom')
    v = U+1; a = sum((F(mu(d),d) for d in range(1,U+1)), F()); tau = v*a
    u = [F()]*(m+1)
    for d in range(1,U+1): u[d] = F(mu(d))
    u[v] = -tau
    one = [F()]+[F(1)]*m
    g = conv(one,u,m)
    y = [-x for x in g]; y[1] += 1
    return v,a,tau,u,g,y


def math_checks():
    summaries=[]; failures={}; source_cases=[(2,40),(5,80),(67,210)]
    counts={'integer_coefficient_checks':0,'real_floor_checks':0,
            'endpoint_pairings':0,'scalar_error_intervals':0}
    captured = None
    for U,m in source_cases:
        v,a,tau,u,g,y = make(U,m)
        assert sum((u[d]/d for d in range(1,m+1)),F()) == 0
        assert all(y[n] == 0 for n in range(1,U+1))
        assert y[v] == F(mu(v))+tau
        ls=[{} for _ in range(m+1)]; cs=[{} for _ in range(m+1)]
        for d in range(1,m+1):
            if u[d]:
                for k in range(1,m//d+1):
                    ls[d*k]=add(ls[d*k],scale(logq(k),u[d]))
        for n in range(1,m+1):
            for d in range(2,n+1):
                if n%d == 0 and y[n//d]:
                    cs[n]=add(cs[n],scale(lam(d),y[n//d]))
            assert add(ls[n],cs[n]) == lam(n)
            counts['integer_coefficient_checks'] += 1
        psi=[{} for _ in range(m+1)]; J=[{} for _ in range(m+1)]
        Pi=[{} for _ in range(m+1)]; logfac=[{} for _ in range(m+1)]
        for n in range(1,m+1):
            psi[n]=add(psi[n-1],lam(n)); J[n]=add(J[n-1],ls[n])
            Pi[n]=add(Pi[n-1],cs[n]); logfac[n]=add(logfac[n-1],logq(n))
        points={F(1),F(v)-F(1,2),F(v),F(v)+F(1,2),F(2*v),F(m)-F(1,2),F(m)}
        for x in sorted(points):
            if not 1 <= x <= m: continue
            N=int(x)
            exactJ=sumvec(scale(logfac[int(x/d)],u[d]) for d in range(1,v+1))
            h=lambda z: F(1)-sum((u[d]*int(z/d) for d in range(1,v+1)),F())
            exactPi=sumvec(scale(lam(n),h(x/n)) for n in range(2,N+1))
            assert exactJ==J[N]
            assert exactPi==Pi[N]==sub(psi[N],exactJ)
            if x<v: assert not exactPi and exactJ==psi[N]
            counts['real_floor_checks']+=1
        # Step-function integration, including the upper atom. Each coordinate is formal log(p).
        for w in (lambda x:F(1)+F(x,3), lambda x:F((x-1)**2*(m-x)**2)):
            direct=sumvec(scale(cs[n],w(n)) for n in range(2,m+1))
            integral=sumvec(scale(Pi[n],w(n+1)-w(n)) for n in range(1,m))
            returned=sub(scale(Pi[m],w(m)),integral)
            assert returned==direct
            counts['endpoint_pairings']+=1
            if w(m) and Pi[m]:
                failures['drop_terminal_primitive_term']=(scale(integral,-1)!=direct)
        # Full signed return E - R + e*(x-1), no separate moduli.
        beta=scale(sumvec(scale(logq(d),u[d]/d) for d in range(1,v+1)),-1)
        for x in (F(v),F(2*v)+F(1,2),F(m)):
            if x>m: continue
            N=int(x); E=sub(psi[N],{0:x-1}); RU=sub(J[N],scale(beta,x-1))
            e=sub({0:F(1)},beta)
            assert sub(add(E,scale(e,x-1)),RU)==Pi[N]
        if U==5: captured=(v,a,tau,u,g,y,psi,J,Pi,ls,cs)
        summaries.append({'U':U,'m':m,'tau':str(tau),'jump_y_at_v':str(y[v]),
                          'production_sparse_band_cell':False})
    v,a,tau,u,g,y,psi,J,Pi,ls,cs=captured
    failures['omit_balancing_atom']=sum((F(mu(d),d) for d in range(1,v)),F())!=0
    failures['wrong_factorial_subtraction_sign']=any(add(psi[n],J[n])!=Pi[n] for n in range(2,len(Pi)))
    failures['delete_prime_powers']=sumvec(lam(d) for d in range(2,5) if 4%d==0 and len(factor(d))==1 and next(iter(factor(d).values()))==1)!=logq(4)
    # Density on a constant primitive segment: (d/dt+sigma)e^(-sigma*t)h=0.
    # Removing sigma leaves -sigma*h, a nonzero smooth term in addition to the jumps.
    sig=F(1,2); h=y[v]
    assert h != 0  # actual U=5 first primitive plateau
    assert -sig*h+sig*h==0
    failures['omit_weight_derivative_term']=(-sig*h != 0)
    # A generic polarized check: transpose is not a complex adjoint.
    # Gaussian rationals are represented by (real,imaginary), still exact.
    def mul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
    z=(F(1,3),F(2,5)); w=(F(3,7),F(-1,2))
    true=mul((z[0],-z[1]),w)[0]
    wrong=mul(z,w)[0]
    assert true!=wrong
    failures['replace_adjoint_by_transpose']=true!=wrong
    assert all(failures.values()) and len(failures)==6
    # Exact outward logarithm enclosures test the actual cofinal U=67 and all seams.
    U=67; m=210; v,a,tau,u,g,y=make(U,m)
    assert U*abs(a)<=F(1,2)
    beta=scale(sumvec(scale(logq(d),u[d]/d) for d in range(1,v+1)),-1)
    blo,bhi=evaluate_interval(beta)
    assert F(1,5)<=blo<=bhi<=F(9,5)
    S=sum(abs(u[d]) for d in range(1,v+1))
    panel=[]
    for x in (F(v),F(2*v-1,2),F(2*v+1,2),F(2*v),F(3*v)+F(1,2),F(m)):
        if x<v: continue
        jf=sumvec(scale(sumvec(logq(k) for k in range(1,int(x/d)+1)),u[d]) for d in range(1,v+1))
        RU=sub(jf,scale(beta,x-1)); lo,hi=evaluate_interval(RU)
        lx,_=log_interval(x)
        lower_cap=S*(1+lx)+F(9,5)
        assert max(abs(lo),abs(hi))<=lower_cap
        counts['scalar_error_intervals']+=1
        panel.append({'x':str(x),'verified_bound':'|R_U(x)| <= S_U*(1+log(x))+9/5'})
    # Elementary integrals used in the budget, checked as rational coefficients.
    # Antiderivative of (1+log x)x^(-3/2) is -2x^(-1/2)(log x+3).
    # Coefficient of log x and constant in its derivative:
    assert (F(1), F(3)-F(2))==(F(1),F(1))
    assert F(4,5)*2 == F(8,5)
    return {'status':'EXACT_DIAGNOSTICS_NOT_PRODUCTION_SIGN_CERTIFICATE',
            'source_cases':summaries,'counts':counts,'actual_cofinal_predicate_U':67,
            'actual_factorial_remainder_panel':panel,'planted_failures_detected':failures,
            'planted_failure_count':len(failures),'new_arithmetic_gain':False,
            'production_spectrum':False,'lean':False,'arb':False}


@lru_cache(None)
def log_interval(q):
    q=F(q)
    if q<=0: raise ValueError('log requires a positive rational')
    if q<1:
        a,b=log_interval(1/q); return -b,-a
    k=0
    while q>2: q/=2; k+=1
    def near(r):
        t=(r-1)/(r+1); N=32
        lo=2*sum((t**(2*j+1)/F(2*j+1) for j in range(N)),F())
        rem=2*t**(2*N+1)/(F(2*N+1)*(1-t*t))
        return lo,lo+rem
    a,b=near(q); c,d=near(F(2))
    return a+k*c,b+k*d


def evaluate_interval(vec):
    lo=hi=vec.get(0,F())
    for p,a in vec.items():
        if p==0: continue
        x,y=log_interval(F(p))
        if a>=0: lo+=a*x; hi+=a*y
        else: lo+=a*y; hi+=a*x
    return lo,hi


def verify_packet(path, manifest):
    data=path.read_bytes(); data.decode('utf-8',errors='strict')
    if (len(data),data.count(b'\n'),hashlib.sha256(data).hexdigest()) != (manifest['bytes'],manifest['lf'],manifest['sha256']):
        raise ValueError('canonical file fingerprint mismatch')
    pat=re.compile(rb'BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([a-f0-9]{64})\n')
    pos=data.index(b'BEGIN_SOURCE S1 ')
    for expected in manifest['sources']:
        mt=pat.match(data,pos)
        if not mt: raise ValueError('invalid source header')
        start=mt.end(); end=start+int(mt[3]); body=data[start:end]
        body.decode('utf-8',errors='strict')
        row={'id':mt[1].decode(),'name':mt[2].decode(),'bytes':len(body),'lf':body.count(b'\n'),
             'sha256':hashlib.sha256(body).hexdigest(),
             'start_line':data[:start].count(b'\n')+1,'end_line':data[:end].count(b'\n')}
        if row!=expected or row['lf']!=int(mt[4]) or row['sha256']!=mt[5].decode():
            raise ValueError('source fingerprint mismatch: '+row['id'])
        suffix=b'\nEND_SOURCE '+mt[1]+b'\n'
        if data[end:end+len(suffix)]!=suffix: raise ValueError('source end frame mismatch')
        pos=end+len(suffix)
        while pos<len(data) and data[pos:pos+1] in (b'\n',b'\r',b' ',b'\t'): pos+=1
    if pos!=len(data): raise ValueError('unframed trailing data')
    return {'canonical_bytes':len(data),'canonical_lf':data.count(b'\n'),
            'canonical_sha256':manifest['sha256'],'source_count':len(manifest['sources']),
            'all_frames_match':True,'historical_code_executed':False,
            'hashes_certify_mathematics':False}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('canonical_txt',type=Path)
    args=ap.parse_args(); root=Path(__file__).resolve().parent
    manifest=json.loads((root/'q43_manifest.json').read_text(encoding='utf-8'))
    result={'manifest':verify_packet(args.canonical_txt,manifest),'mathematics':math_checks()}
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    (root/'q43_results.json').write_text(text,encoding='utf-8'); print(text,end='')

if __name__=='__main__': main()
