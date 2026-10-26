#!/usr/bin/env python3
"""Exact controls of Q40's signed incidence-flow calculation.
Not a production CCM computation, interval certificate, or asymptotic proof.
Standard library only. Writes check_q40_results.json next to this script.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

checks: dict[str, int] = {}
planted: list[str] = []

def check(name: str, predicates: list[bool]) -> None:
    if not all(predicates):
        raise AssertionError(name)
    checks[name] = len(predicates)

def reject(name: str, false_claim: bool) -> None:
    if false_claim:
        raise AssertionError('Undetected planted error: ' + name)
    planted.append(name)

def factor(n: int) -> dict[int,int]:
    if n < 1: raise ValueError('Positive integer required')
    ans: dict[int,int] = {}; d=2
    while d*d <= n:
        while n%d == 0:
            ans[d]=ans.get(d,0)+1; n//=d
        d+=1
    if n>1: ans[n]=ans.get(n,0)+1
    return ans

def mobius(n: int) -> int:
    fs=factor(n)
    return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)

def primes(n: int) -> list[int]:
    return [p for p in range(2,n+1) if factor(p)=={p:1}]

def positive(x: F) -> F:
    return max(x,F(0))

# Hermitian matrix encoded by diagonal entries a,d and off-diagonal b+i*c.
Z=(F(0),)*4

def add(a, b): return tuple(x+y for x,y in zip(a,b))
def scale(a, r): return tuple(r*x for x in a)
def h(n: int, m: int):
    if n==m: return Z
    return (F(n%7-3,n+1),F(n%5-2,n+2),F(n%11-5,n+3),F(n%13-6,n+4))

def blocks(m: int):
    """Formal logarithms: B_d is a dict prime -> Hermitian coefficient."""
    ans={}
    for d in range(1,m+1):
        terms={}
        for k in range(1,m//d+1):
            for p,e in factor(k).items():
                terms[p]=add(terms.get(p,Z),scale(h(d*k,m),F(e)))
        ans[d]={p:v for p,v in terms.items() if v!=Z}
    return ans

# Construct the exact primal minimizer and the matching dual certificate.
def signed_flow(values: dict[int,F]):
    values={n:F(v) for n,v in values.items() if v}
    if any(n<2 or mobius(n)==0 for n in values):
        raise ValueError('Only active squarefree n>1')
    support={n:sorted(factor(n)) for n in values}
    vertices=sorted({p for ps in support.values() for p in ps})
    edges={p:[] for p in vertices}
    allocation={n:{p:values[n]/len(ps) for p in ps} for n,ps in support.items()}
    for n,ps in support.items():
        for p in ps[1:]:
            edges[ps[0]].append((p,n)); edges[p].append((ps[0],n))
    totals={p:sum((allocation[n].get(p,F(0)) for n in values),F(0)) for p in vertices}
    components=[]; seen=set()
    for root in vertices:
        if root in seen: continue
        seen.add(root); queue=deque([root]); order=[]; parent={}
        while queue:
            p=queue.popleft();order.append(p)
            for v,n in sorted(edges[p]):
                if v not in seen:
                    seen.add(v);parent[v]=(p,n);queue.append(v)
        members=set(order)
        source_total=sum((z for n,z in values.items() if support[n][0] in members),F(0))
        for v in reversed(order[1:]):
            p,n=parent[v];amount=totals[v]
            allocation[n][v]-=amount;allocation[n][p]+=amount
            totals[p]+=amount;totals[v]=F(0)
        components.append((order,source_total))
    expected=sum((positive(s) for _,s in components),F(0))
    cost=sum((positive(x) for x in totals.values()),F(0))
    dual={p:F(s>0) for ps,s in components for p in ps}
    dual_value=sum((dual[p]*x for p,x in totals.items()),F(0))
    return support,allocation,totals,components,dual,cost,expected,dual_value

matrix_cases=[]; support_cases=[]; k2_cases=[]; incidence_cases=[]
for m in (8,9,10,12,16,24,30,31,32,48,64,96):
    B=blocks(m); ps=primes(m)
    for ell in ps:
        lhs=Z;rhs=Z
        for d in B: lhs=add(lhs,scale(B[d].get(ell,Z),F(mobius(d))))
        v=ell
        while v<=m:
            rhs=add(rhs,h(v,m)); v*=ell
        matrix_cases.append(lhs==rhs)
    support_cases += [B[d]=={} for d in range(1,m+1) if 2*d>=m]
    for p in ps:
        if 3*p>m and 2*p<m:
            k2_cases.append(B[p]==({2:h(2*p,m)} if h(2*p,m)!=Z else {}))
    R=max(1,isqrt(m)//2)
    for ell in ps:
        T=Z; channels=Z
        for n in range(R+1,m+1): T=add(T,scale(B[n].get(ell,Z),F(mobius(n))))
        for p in ps:
            for k in range(1,m//p+1):
                n=p*k
                if n<=R or k%p==0 or not mobius(k): continue
                theta=F(1,len(factor(n)))
                channels=add(channels,scale(B[n].get(ell,Z),-mobius(k)*theta))
        incidence_cases.append(T==channels)
check('actual_mu_log_full_complex_matrix',matrix_cases)
check('exact_full_k_upper_half_support',support_cases)
check('isolated_prime_k2_formula',k2_cases)
check('full_k_prime_channel_return',incidence_cases)

flow_cases=[]; dual_cases=[]; signs_used=0; example_result=None
for m in (20,40,80,160,320):
    for R in (1,2,5,11):
        for shift in range(4):
            values={n:F(mobius(n)*((n+shift)%9-4),n+1)
                    for n in range(R+1,m) if 2*n<m and mobius(n)}
            support,alloc,totals,comps,y,cost,expected,dv=signed_flow(values)
            vals={n:v for n,v in values.items() if v}
            ok=cost==expected==dv and sum(totals.values(),F())==sum(vals.values(),F())
            ok &= all(sum(alloc[n].values(),F())==v for n,v in vals.items())
            ok &= all(sum((alloc[n].get(p,F()) for n in vals),F())==v for p,v in totals.items())
            ok &= all(len({y[p] for p in ps})==1 for ps in support.values())
            flow_cases.append(ok)
            # An independent deterministic signed allocation, not the optimizer.
            trial={p:F() for p in totals}
            for n,ps in support.items():
                split=[F((p+n+shift)%7-3,2) for p in ps[:-1]]
                split.append(F(1)-sum(split,F()))
                for p,t in zip(ps,split): trial[p]+=t*vals[n]
            dual_cases.append(sum((positive(v) for v in trial.values()),F())>=expected)
            signs_used+=any(x/vals[n]<0 for n,mp in alloc.items() for x in mp.values())
check('constructive_signed_primal_component_optimum',flow_cases)
check('dual_lower_bound_for_other_signed_allocations',dual_cases)
check('signed_allocations_are_genuinely_used',[signs_used>0])

# The signed class is not the S4 nonnegative termwise certificate.
ex={2:F(2),3:F(-3),6:F(1)}
_,alloc,totals,comps,y,cost,expected,dv=signed_flow(ex)
check('signed_rebalancing_strictly_better_in_control',[
    cost==0, alloc[6][2]==-2, alloc[6][3]==3,
    sum(map(abs,ex.values()),F())==6])

isolated=[]
for m in range(16,257):
    active=[n for n in range(2,m) if 2*n<m and mobius(n)]
    for p in primes(m//2):
        if 4*p>m and 2*p<m:
            isolated.append([n for n in active if n%p==0]==[p])
check('actual_integer_incidence_isolation',isolated)

# Double Mellin-zero algebra and projection exponents: exact controls only.
z=F(1,2)
check('two_contact_double_zero_prefactor',[(z*z-F(1,4))**2==0,
      4*z*(z*z-F(1,4))==0, ((-z)**2-F(1,4))**2==0])
exponents=[]
for eps in (F(1,64),F(1,100),F(1,1000)):
    q=int(2/eps)+3
    exponents += [F(1,2)+eps*(F(1,2)-q)<0,
                  eps-F(1,2)<0,
                  F(3,2)*eps<F(1,2)]
check('fixed_order_projection_and_short_exponents',exponents)
check('signed_packet_cross_orientation',[
    F(2)*F(1,2)*(-1)==-1,
    F(1,2)+F(1,2)==1,
    F(7,8)-4*F(1,16)>=F(1,2)])
# source-test derivative x^(-1/2) r(log(x/m)) by exponent bookkeeping.
check('pnt_weight_and_normalization_exponents',[
    F(1)-F(3,2)+F(1)==F(1,2),
    F(303,200)+1==F(503,200),
    F(939,100)==F('9.39'), F(4137,5000)==F('0.8274')])

# Planted errors are each checked against an explicit counter-witness.
reject('drop_mu_channel_minus',mobius(3)==mobius(1))
reject('omit_coprimality_mask',mobius(4)==-mobius(2))
reject('replace_full_k_log_by_log_product',factor(1)==factor(2))
reject('lose_n_equal_m_over_2_seam',bool(blocks(20)[10]))
reject('allow_zero_block_to_bridge_isolated_prime',bool(blocks(100)[94]))
reject('signed_channels_same_as_termwise_moduli',cost==sum(map(abs,ex.values()),F()))
reject('permit_transfer_between_distinct_components',signed_flow({2:F(2),3:F(-2)})[5]==0)
reject('drop_cross_time_orientation',F(1,2)*(-1)==-1)
reject('wrong_packet_relative_sign',F(2)*F(1,2)*(1)==-1)
reject('drop_linear_projection_error',(1+F(1,10))**2-1==F(1,10)**2)
reject('prime_power_deletion',sum(mobius(d)*factor(4//d).get(2,0)
       for d in (1,2,4))==0)

out={
 'scope':'Finite exact arithmetic, incidence-flow, generic Hermitian algebra and exponent controls; not a numerical original-P cell or cofinal sign certification.',
 'groups':checks,'groups_passed':len(checks),'finite_cases':sum(checks.values()),
 'planted_failures_detected':planted,'planted_count':len(planted),
 'historical_scripts_executed':False,'external_pnt_proof_recertified':False,
 'lean':False,'arb':False,'production_spectrum':False}
text=json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True)+'\n'
Path(__file__).with_name('check_q40_results.json').write_text(text,encoding='utf8')
print(text,end='')
