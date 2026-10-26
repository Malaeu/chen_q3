#!/usr/bin/env python3
"""Exact algebra/interval diagnostics, not a CCM spectral certificate. Stdlib only."""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json


def factors(n):
    out = {}; d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0)+1; n //= d
        d += 1
    if n > 1: out[n] = out.get(n, 0)+1
    return out


def mu(n):
    d = factors(n)
    return 0 if any(v>1 for v in d.values()) else (-1)**len(d)


def conv(a, b):
    if len(a) != len(b): raise ValueError('different carriers')
    m = len(a)-1; c = [F(0) for _ in a]
    for d in range(1,m+1):
        if a[d]:
            for k in range(1,m//d+1):
                if b[k]: c[d*k] += a[d]*b[k]
    return c


def power(a, j):
    out = [F(0) for _ in a]; out[1] = F(1)
    for _ in range(j): out = conv(out,a)
    return out


def make_inverse(m, U, *, sign=-1, place=None, absolute=False):
    if m < U+1: raise ValueError('need full repair atom')
    v = U+1 if place is None else place
    a = sum((F(mu(d),d) for d in range(1,U+1)),F())
    u = [F(0)]*(m+1)
    for d in range(1,U+1): u[d] = F(abs(mu(d)) if absolute else mu(d))
    u[v] += sign*v*a
    return u,a,v


def expansion(u, K, drop_mixed_base=None):
    m=len(u)-1; one=[F(0)]+[F(1)]*m
    unit=[F(0)]*(m+1); unit[1]=1
    y=[unit[n]-z for n,z in enumerate(conv(one,u))]
    total=[F(0)]*(m+1)
    for j in range(1,K+1):
        uj=power(u,j)
        if drop_mixed_base is not None:
            d=[x-z for x,z in zip(u,drop_mixed_base)]
            uj=[x+z for x,z in zip(power(drop_mixed_base,j),power(d,j))]
        row=conv(uj,power(one,j-1)); c=(-1)**(j-1)*comb(K,j)
        total=[x+c*z for x,z in zip(total,row)]
    return total,y,power(y,K)


def log_coords(m):
    fs=[{}]+[factors(n) for n in range(1,m+1)]
    for p in range(2,m+1):
        if fs[p] != {p:1}: continue
        ell=[F(0)]+[F(fs[n].get(p,0)) for n in range(1,m+1)]
        lam=[F(0)]+[F(int(len(fs[n])==1 and p in fs[n])) for n in range(1,m+1)]
        yield p,ell,lam


def log_unit_interval(q, terms=24):
    """Rational outward bounds for log(q), 1<=q<=2."""
    assert F(1)<=q<=F(2)
    t=(q-1)/(q+1)
    lo=2*sum((t**(2*j+1)/F(2*j+1) for j in range(terms)),F())
    rem=2*t**(2*terms+1)/(F(2*terms+1)*(1-t*t))
    return lo,lo+rem


def log_ratio(q):
    assert q>=1
    k=0
    while q>2: q/=2; k+=1
    a,b=log_unit_interval(q); c,d=log_unit_interval(F(2))
    return a+k*c,b+k*d


def moment_interval(U):
    lo=hi=F(0); v=U+1
    for d in range(1,U+1):
        z=F(mu(d),d)
        if not z: continue
        a,b=log_ratio(F(v,d))
        if z>0: lo+=z*a; hi+=z*b
        else: lo+=z*b; hi+=z*a
    return lo,hi


def poly_add(a,b):
    c={k:a.get(k,F())+b.get(k,F()) for k in a.keys()|b.keys()}
    return {k:v for k,v in c.items() if v}


def poly_mul(a,b):
    c={}
    for k,v in a.items():
        for l,w in b.items(): c[k+l]=c.get(k+l,F())+v*w
    return {k:v for k,v in c.items() if v}


def poly_power(a,j):
    c={0:F(1)}
    for _ in range(j): c=poly_mul(c,a)
    return c


def scale(a,t): return {k:t*v for k,v in a.items() if t*v}


def shift(a,j): return {k+j:v for k,v in a.items()}


def run():
    verified=[]; planted={}
    for m,U,K in [(32,2,4),(127,5,3),(215,5,3),(300,7,3)]:
        u,a,v=make_inverse(m,U)
        total,y,yk=expansion(u,K)
        assert all(y[n]==0 for n in range(1,U+1))
        assert sum((u[d]/d for d in range(1,m+1)),F())==0
        assert v**K>m and not any(yk)
        assert total==[F(0)]+[F(mu(n)) for n in range(1,m+1)]
        for p,ell,lam in log_coords(m): assert conv(total,ell)==lam
        verified.append({'m':m,'U':U,'K':K,'a_U':str(a),'repair':str(-v*a)})
    # A genuinely nonzero finite remainder, retaining formal prime-power logs.
    m,U,K=80,2,2
    u,a,v=make_inverse(m,U); total,y,yk=expansion(u,K)
    remainder_nonzero=False
    for p,ell,lam in log_coords(m):
        remainder=conv(lam,yk); recovered=conv(total,ell)
        assert [x+z for x,z in zip(recovered,remainder)]==lam
        remainder_nonzero |= any(remainder)
        if p==2: assert remainder[18]==F(1,4)
    assert remainder_nonzero
    planted['delete_nonzero_hyperbolic_remainder']=remainder_nonzero
    # Primitive, real-floor seams, not integer samples alone.
    for U in [2,5,7,11]:
        m=4*(U+1); u,a,v=make_inverse(m,U)
        S=sum(abs(z) for z in u)
        for j in range(3,12*v+1):
            x=F(j,3)
            G=sum((u[d]*(x//d) for d in range(1,m+1)),F())
            frac=-sum((u[d]*(x/d-(x//d)) for d in range(1,m+1)),F())
            assert G==frac and abs(G)<=S
            if x<v: assert G==1
    # Select a small source panel by the exact cofinal predicate only.
    candidates=[]; a=F()
    for U in range(1,513):
        a+=F(mu(U),U)
        if U>=64 and U*abs(a)<=F(1,2): candidates.append((U,a))
    assert candidates
    chosen=[candidates[i] for i in sorted({0,len(candidates)//2,len(candidates)-1})]
    panel=[]
    for U,a in chosen:
        v=U+1; Q=sum(mu(d)**2 for d in range(1,U+1))
        theta=(1+F(Q)+v*abs(a))/v
        assert theta<=F(4,5)
        lo,hi=moment_interval(U)
        assert lo>=1-theta and hi<=1+theta
        # Compact decimal-free enclosure for reporting.
        sc=10**8
        lo8=F((lo*sc).__floor__(),sc); hi8=F((hi*sc).__ceil__(),sc)
        panel.append({'U':U,'a_U':str(a),'theta_U':str(theta),
                      'b_U_lower':str(lo8),'b_U_upper':str(hi8)})
    assert F(100,99)*F(101,99)*F(4,5)<F(5,6)
    # Uniform scalar threshold for all U>=64: use decreasing envelope, not a panel extrapolation.
    assert F(3,4)+F(1,65)+F(1,128)<F(4,5)
    # Joint local germs: -zeta' * sum binomial M^j zeta^(j-1).
    germ_cases=[]
    for K,b in [(2,F(1,3)),(3,F(7,5)),(4,F(9,10))]:
        Z={-1:F(1),0:F(2,5),1:F(-1,7),2:F(1,11)}
        MT={1:b,2:F(-2,9),3:F(1,13)}
        negder={k-1:-k*v for k,v in Z.items() if k}
        B={}
        for j in range(1,K+1):
            row=poly_mul(poly_power(MT,j),poly_power(Z,j-1))
            B=poly_add(B,scale(poly_mul(negder,row),F((-1)**(j-1)*comb(K,j))))
        assert min(B)>=-1 and B.get(-1,F())==1-(1-b)**K
        # Before repair, the highest pole survives.
        a=F(-1,30); M0=poly_add(MT,{0:a}); old={}
        for j in range(1,K+1):
            row=poly_mul(poly_power(M0,j),poly_power(Z,j-1))
            old=poly_add(old,scale(poly_mul(negder,row),F((-1)**(j-1)*comb(K,j))))
        assert old[-K-1]==(-1)**(K+1)*a**K
        germ_cases.append({'K':K,'b':str(b),'simple_residue':str(B[-1])})
    # Sensitive failures.
    bad,a,v=make_inverse(80,5,sign=1)
    planted['wrong_balancing_sign']=sum((bad[d]/d for d in range(1,81)),F())!=0
    bad,a,v=make_inverse(80,5,place=5)
    _,y,_=expansion(bad,3)
    planted['repair_inside_preserved_prefix']=any(y[n] for n in range(1,6))
    u,a,v=make_inverse(80,5); base=[F(0)]+[F(mu(n) if n<=5 else 0) for n in range(1,81)]
    wrong,_,_=expansion(u,3,drop_mixed_base=base)
    planted['drop_repair_mixed_products']=wrong!=[F(0)]+[F(mu(n)) for n in range(1,81)]
    bad,a,v=make_inverse(80,5,absolute=True)
    wrong,_,_=expansion(bad,3)
    planted['replace_actual_mu_by_moduli']=wrong!=[F(0)]+[F(mu(n)) for n in range(1,81)]
    # A zero-support remainder can still have nonzero simple-pole germ.
    alo,ahi=moment_interval(chosen[0][0])
    assert alo>1 or ahi<1  # actual cofinal moment: e_U is rigorously nonzero
    planted['discard_remainder_residue_from_support']=(alo>1 or ahi<1)
    # Exact return: E = C0 - e^K H and A = E - (1-e^K)H.
    C,H,e,K=F(7,3),F(5,7),F(-1,3),3
    E=C-e**K*H; A=C-H
    assert E-(1-e**K)*H==A
    planted['wrong_continuum_return_sign']=E+(1-e**K)*H!=A
    assert all(planted.values())
    # Cofinal schedule without floating-point fractional powers.
    for U in (5,64,100):
        m=U**33; assert (U+1)**33>m
        x=U**65; m=isqrt(x)
        if m*m<x: m+=1
        assert U**65<=m*m<(U+1)**65 and (U+1)**33>m
    return {'status':'EXACT_AUXILIARY_ALGEBRA_AND_MOMENT_CONTROLS_ONLY',
            'finite_reconstruction_cases':verified,'nonzero_remainder_case':{'m':80,'U':2,'K':2,'log2_coefficient_at18':'1/4'},
            'actual_mobius_moment_intervals':panel,'generic_germ_cases':germ_cases,
            'primitive_floor_controls':'passed at integer and noninteger seams',
            'cofinal_schedule_integer_controls':'passed',
            'planted_failures_detected':planted,'planted_failure_count':len(planted),
            'source_quantifiers_supplied_by':'paper derivation, not the finite panel',
            'production_spectrum':False,'lean':False,'arb':False,'rh_claim':False}


if __name__=='__main__':
    obj=run(); text=json.dumps(obj,sort_keys=True,indent=2)+'\n'
    Path(__file__).with_name('q42_math_results.json').write_text(text)
    print(text,end='')
