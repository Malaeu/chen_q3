"""Exact finite checks for the mixed Möbius-annihilator corrector.
Requires Python 3.10+ and SymPy; no numerical eigenvalue computation.
The norm-49 example is a complete diagnostic source, not a cofinal bound.
"""
from __future__ import annotations
from collections import Counter
from itertools import product
from math import isqrt
from pathlib import Path
import json
import sympy as s

Ideal = tuple[int, int]
ONE: Ideal = (1, 0)
checks: Counter[str] = Counter()

def check(condition: bool, group: str) -> None:
    if not condition:
        raise AssertionError(f"Failed exact check: {group}")
    checks[group] += 1

def norm(z: Ideal) -> int:
    a, b = z
    return a*a-a*b+b*b

def mul(z: Ideal, w: Ideal) -> Ideal:
    a,b=z; c,d=w
    return a*c-b*d, a*d+b*c-b*d

def div(z: Ideal, w: Ideal) -> Ideal | None:
    a,b=w; c,d=mul(z,(a-b,-b)); q=norm(w)
    return (c//q,d//q) if c%q==0 and d%q==0 else None

def basis(bound: int) -> list[Ideal]:
    h=2*isqrt(bound)+3
    out=[(a,b) for a in range(-h,h+1) for b in range(-h,h+1)
         if a%3==1 and b%3==0 and 0<norm((a,b))<=bound
         and norm((a,b))%2 and norm((a,b))%3]
    return sorted(out,key=lambda z:(norm(z),z))

def data(bound: int):
    ideals=basis(bound); N=len(ideals); ix={n:i for i,n in enumerate(ideals)}
    check(ideals[0]==ONE,'basis')
    primes=[n for n in ideals[1:] if not any(
        norm(d)>1 and norm(d)<norm(n) and div(n,d) is not None for d in ideals)]
    val={}
    for n in ideals:
        row=[]
        for p in primes:
            v=0; m=n
            while div(m,p) is not None:
                m=div(m,p); v+=1
            row.append(v)
        val[n]=row
        check(__import__('math').prod(norm(p)**v for p,v in zip(primes,row))==norm(n),'factorization')
    mu={n:0 if any(v>1 for v in val[n]) else (-1)**sum(val[n]) for n in ideals}
    Z=s.Matrix(N,N,lambda i,j: int(div(ideals[i],ideals[j]) is not None))
    inv=s.Matrix(N,N,lambda i,j: mu.get(div(ideals[i],ideals[j]),0))
    check(Z*inv==s.eye(N),'inverse'); check(inv*Z==s.eye(N),'inverse')
    e=s.eye(N)[:,0]; m=s.Matrix([mu[n] for n in ideals])
    check(Z*m==e,'mobius')
    As=[]; Ds=[]
    for k,p in enumerate(primes):
        A=s.zeros(N); D=s.diag(*[val[n][k] for n in ideals])
        for i,n in enumerate(ideals):
            A[i,i]=val[n][k]; r=n
            for _ in range(val[n][k]):
                r=div(r,p); A[i,ix[r]]+=1
        check(Z*A==D*Z,'similarity'); check(A*m==s.zeros(N,1),'annihilator')
        As.append(A); Ds.append(D)
    for i,A in enumerate(As):
        for B in As[i+1:]:
            check(A*B==B*A,'commuting')
    return ideals,ix,primes,mu,Z,inv,e,m,As,Ds

def correction(G,Z,inv,e,As,Ds,active,tau):
    N=G.rows
    A=sum((As[i] for i in active),s.zeros(N))
    D=sum((Ds[i] for i in active),s.zeros(N))
    F=s.diag(*[int(D[i,i]==0) for i in range(N)])
    K=s.eye(N)-F
    Ddag=s.diag(*[1/D[i,i] if D[i,i]!=0 else 0 for i in range(N)])
    H=inv.H*G*inv
    B=-s.Rational(1,2)*K*H*K-K*H*F-tau*s.Rational(1,2)*K
    Y=Z.H*Ddag*B*Z
    null=A.H*Y+Y.H*A
    target=Z.H*(F*H*F-tau*K)*Z
    check(G+null==target,'corrector_identity')
    return null,F,K,H,Y

def main():
    check(Path(__file__).with_name('registration.json').exists(),'preregistration')
    source=None
    for bound in (30,83):
        ideals,ix,primes,mu,Z,inv,e,m,As,Ds=data(bound)
        N=len(ideals)
        # Deterministic complex Gram tests; these are algebraic controls only.
        T=s.Matrix(3,N,lambda i,j:s.Integer(((i+2)*(j+3))%7-3)
                   +s.I*s.Integer((2*i+3*j)%5-2))
        G=T.H*T
        for active in ([],list(range(min(2,len(primes)))),list(range(len(primes)))):
            for tau in (s.Rational(1,3),s.Integer(2)):
                null,F,K,H,Y=correction(G,Z,inv,e,As,Ds,active,tau)
                check((m.H*null*m)[0]==0,'null_source')
                # Independent directly transformed residual, at 3 budgets.
                energy=(m.H*G*m)[0]
                for delta in (-1,0,1):
                    budget=energy+delta
                    R=budget*e*e.H-G-null
                    rhs=budget*e*e.H-F*H*F+tau*K
                    check(inv.H*R*inv==rhs,'residual_congruence')
                    check((m.H*R*m)[0]==delta,'source_budget_invariant')
                    if len(active)==len(primes):
                        check(rhs==s.diag(delta,*([tau]*(N-1))),'full_inertia_certificate')
        if bound==83:
            source=(ideals,ix,primes,mu,Z,inv,e,m,As,Ds)
    ideals,ix,primes,mu,Z,inv,e,m,As,Ds=source
    N=len(ideals)
    pi=(-2,-3); pib=(1,3); sigma=(1,-3)
    check(norm(pi)==norm(pib)==7 and norm(sigma)==13,'source_primes')
    check(78**25<=49**28 and 78**100>=49**111,'source_scale_band')
    # All 18 elements of norm 49, not a selected subset.
    rows=[(a,b) for a in range(-16,17) for b in range(-16,17) if norm((a,b))==49]
    check(len(rows)==18,'source_rows')
    masks=[(int(div(u,pi) is None),int(div(u,pib) is None)) for u in rows]
    check(Counter(masks)==Counter({(0,0):6,(1,0):6,(0,1):6}),'source_zero_masks')
    # W(7/78)=2, nu=1, rho(1)=1. Cross-terms vanish by actual zeros.
    G=s.zeros(N)
    for a,b in masks:
        check(a*b==0,'source_cross_zeros')
        G[ix[pi],ix[pi]]+=s.Rational(4,78)*a
        G[ix[pib],ix[pib]]+=s.Rational(4,78)*b
    energy=(m.H*G*m)[0]
    check(energy==s.Rational(8,13),'source_energy')
    active=[primes.index(pi),primes.index(sigma)]
    null,F,K,H,Y=correction(G,Z,inv,e,As,Ds,active,s.Integer(1))
    v=inv[:,ix[pib]]
    for i in active:
        check(As[i]*v==s.zeros(N,1),'omitted_prime_kernel')
    for budget in (s.Integer(0),s.Rational(8,13),s.Integer(10)**9):
        R=budget*e*e.H-G-null
        check((v.H*R*v)[0]==-s.Rational(4,13),'omitted_prime_negative')
    source_null,F,K,H,Y=correction(G,Z,inv,e,As,Ds,list(range(len(primes))),s.Integer(1))
    for delta in (-s.Rational(1,13),0,s.Rational(1,13)):
        R=(energy+delta)*e*e.H-G-source_null
        check(inv.H*R*inv==s.diag(delta,*([1]*(N-1))),'source_exact_inertia')
    # Planted failures: dropping p^2 and corrupting the p*q coefficient.
    Ap=As[primes.index(pi)]
    one_power=s.zeros(N)
    for i,n in enumerate(ideals):
        one_power[i,i]=Ap[i,i]
        q=div(n,pi)
        if q is not None:
            one_power[i,ix[q]]=1
    check((one_power*m)[ix[mul(pi,pi)]]==-1,'planted_power_deletion')
    bad=m.copy(); bad[ix[mul(pi,pib)]]=0
    check((Ap*bad)[ix[mul(pi,pib)]]==-1,'planted_mobius_corruption')
    # Exact exponent arithmetic for the old, still conditional, budget.
    rlo=s.Rational(28,25); rhi=s.Rational(113,100); eta=s.Rational(1,200)
    c0=s.Rational(1,10000)
    gaps=[eta-5*r*c0/6 for r in (rlo,rhi)]
    check(gaps==[s.Rational(46,9375),s.Rational(5887,1200000)],'budget')
    check(eta-5*rhi*c0/6-s.Rational(1,250)==s.Rational(1087,1200000),'budget')
    out={'basis_bound_83_size':N,'basis_bound_83_prime_ideals':len(primes),
         'source_rows':len(rows),'source_energy':str(energy),
         'omitted_prime_certificate':str(-s.Rational(4,13)),
         'source_congruence_pivots':['-1/13','0','1/13'],
         'checks_by_group':dict(checks),'total_boolean_checks':sum(checks.values()),
         'scope':'EXACT_FINITE_ALGEBRA_AND_ONE_COMPLETE_DIAGNOSTIC_SOURCE_NOT_COFINAL_MOMENT'}
    print(json.dumps(out,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
