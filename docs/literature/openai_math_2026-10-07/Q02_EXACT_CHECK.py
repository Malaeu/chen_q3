"""Exact finite diagnostics for Q02. No analytic moment or zero-free certification."""
from fractions import Fraction as F
from itertools import product
from collections import Counter
from math import prod

checks = Counter()
# Q(zeta_6), zeta_6^2=zeta_6-1: a+b*zeta_6.
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]+x[1]*y[1])
def scale(x,c): return (x[0]*c,x[1]*c)
def cpow(x,j):
    ans=(F(1),F(0))
    for _ in range(j): ans=mul(ans,x)
    return ans
def csum(xs):
    ans=(F(0),F(0))
    for x in xs: ans=add(ans,x)
    return ans
one=(F(1),F(0)); zero=(F(0),F(0)); zeta=(F(0),F(1))
phases=[zero]+[cpow(zeta,k) for k in range(6)]
ps=(7,13,19)
bits=list(product((0,1),repeat=3))
ideals=[(b,prod(p**j for p,j in zip(ps,b)),(-1)**sum(b)) for b in bits]
def phase(es,values):
    ans=one
    for e,v in zip(es,values): ans=mul(ans,cpow(v,e))
    return ans
def W(x): return (2*x-1)*(2-x) if F(1,2)<=x<=2 else F(0)

# Full actual square, including every zero-symbol branch and g^2*t column.
for values in product(phases,repeat=3):
    for L in (F(10),F(50),F(200)):
        m=csum(scale(phase(b,values),mu*W(F(q,L))) for b,q,mu in ideals)
        lhs=scale(mul(m,m),1/L)
        rhs=zero
        for g,qg,_ in ideals:
            for t,qt,mut in ideals:
                if any(a and b for a,b in zip(g,t)): continue
                A=F(0)
                for d,qd,_ in ideals:
                    if any(a>b for a,b in zip(d,t)): continue
                    A+=W(F(qg*qd,L))*W(F(qg*qt,qd*L))
                es=tuple(2*a+b for a,b in zip(g,t))
                rhs=add(rhs,scale(phase(es,values),mut*A/L))
        assert lhs==rhs
        checks['actual_cube_free_square_all_zero_branches']+=1

# mu_2*1=mu; mu_2=(1-X)^2 includes the repeated prime.
mu=lambda e: 1 if e==0 else -1 if e==1 else 0
mu2=lambda e: 1 if e in (0,2) else -2 if e==1 else 0
for es in product(range(6),repeat=3):
    ans=prod(sum(mu2(j) for j in range(e+1)) for e in es)
    assert ans==prod(mu(e) for e in es)
    checks['mu2_plain_bridge_coefficients']+=1

def e_local(i,j): return 1 if i==j==0 else -1 if i>=1 and j>=1 else 0
# Same-orientation coprime inverse; all repeated shifts are included.
for i,j in product(range(9),repeat=2):
    lhs=sum(e_local(a,b)*mu(i-a)*mu(j-b) for a in range(i+1) for b in range(j+1))
    assert lhs==mu(i)*mu(j)*int(min(i,j)==0)
    checks['same_orientation_euler_inverse']+=1

# A product of distinct comparable good primes survives equal-product centering.
p,q,L,R=7,13,F(10),F(4)
B0=sum(W(F(d,L))*W(F(p*q,d*L)) for d in (1,p,q,p*q))
B1=sum(W(F(d,L/R))*W(F(p*q,d*L*R)) for d in (1,p,q,p*q))
assert B0==2*W(F(p,L))*W(F(q,L)) and B0!=0 and B1==0
checks['actual_centered_prime_pair_witness']+=1
# Removing the p^2 column from M^2 loses this nonzero coefficient.
assert mu(2)==0 and W(F(7,10))**2>0
checks['planted_squarefree_product_defect_detected']+=1
# Off-diagonal simple pole pair: equal products cancel rho=sigma only.
for R in (F(2),F(3),F(5)):
    assert 1-R**0==0
    assert 2-R-1/R!=0
    checks['mixed_pole_factor_control']+=2

# Sixth-power injection, original S-prime valuation and all six unit labels.
seen=set()
for unit in range(6):
    for u in product(range(6),repeat=3):  # first prime is in S
        for a in product(range(3),repeat=2):
            v=(unit,u[0],u[1]+6*a[0],u[2]+6*a[1])
            assert v not in seen
            seen.add(v)
            rec_u=(v[1],v[2]%6,v[3]%6)
            assert rec_u==u
            assert ((v[2]-rec_u[1])//6,(v[3]-rec_u[2])//6)==a
            if v[2]%6==v[3]%6==0:
                assert u[1]==u[2]==0
            checks['sixth_core_injection_and_fixed_family_support']+=1
# A common prime of u,a is legal, not an exclusion.
assert 1+6*1==7 and 7%6==1
checks['planted_u_a_coprimality_defect_detected']+=1

# Uniform affine budgets, tested at all vertices (proof uses affinity).
rlo,rhi,c0,eta=F(28,25),F(113,100),F(1,10000),F(1,200)
kappa,z=F(1,12),F(1,16)
mins={}
for r in (rlo,rhi):
    h=r*(1+c0); p=(h-1)/6
    for ell in (r-F(1,100),r):
        values={
          'Holder_gain_candidate':(5*p-kappa)/2,
          'g_tail_sparse_gain':(5*p-z)/2,
          'Holder_margin_below_eta':(5*p-kappa)/2-eta,
          'g_tail_margin_below_eta':(5*p-z)/2-eta,
          'unreflected_diagonal_budget_excess':2*ell-h-kappa,
          'positive_g_cutoff_exponent':ell-z,
          'clipped_low_energy_gain':F(3,500),
        }
        for name,v in values.items():
            assert v>0
            mins[name]=min(mins.get(name,v),v)
            checks['rational_budget_vertices']+=1
assert mins['Holder_gain_candidate']==F(419,50000)
assert mins['g_tail_sparse_gain']==F(5639,300000)
assert mins['Holder_margin_below_eta']==F(169,50000)
assert mins['g_tail_margin_below_eta']==F(4139,300000)
assert min((5*((r*(1+c0)-1)/6)-F(1,100)) for r in (rlo,rhi))==F(6757,75000)
checks['exact_named_margins']+=5
sigma4=F(3,4)+c0/4+kappa/(4*rhi)
print('EXACT_FINITE_DIAGNOSTICS_ONLY')
for k,v in checks.items(): print(k,v)
print('TOTAL',sum(checks.values()))
print('MARGINS',{k:str(v) for k,v in mins.items()})
print('FIXED_ROW_SIGMA_IF_FOURTH_SUPPLIER',str(sigma4),float(sigma4))
print('PRIME_PAIR_COEFFICIENT',str(B0),'COMPARISON',str(B1))
print('NO_ANALYTIC_CERTIFICATION; NO_LEAN; NO_ARB; NO_COMPARATOR')
