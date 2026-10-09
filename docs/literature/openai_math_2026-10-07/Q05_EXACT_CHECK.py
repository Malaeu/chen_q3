#!/usr/bin/env python3
"""Exact finite controls for Q05. Not a cofinal or source-analytic certificate."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
import hashlib
from pathlib import Path

checks: Counter[str] = Counter()

def check(kind: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(kind)
    checks[kind] += 1

# Scalar resolvent expansion, including negative Q-Pi and exact zero branches.
def rv(x: F, v: F) -> F:
    return x*x/(x+v)

def expansion(q: F, pi: F, v: F) -> tuple[F, F, F]:
    o = q-pi
    d0 = pi*pi/(pi+v)
    linear = pi*(pi+2*v)/(pi+v)**2*o
    remainder = v*v*o*o/((pi+v)**2*(q+v))
    return d0, linear, remainder

for pi,q,v in product(map(F, [0,1,2,7]),
                      [F(0),F(1,7),F(1),F(2),F(9),F(100)],
                      [F(1,24),F(1,12),F(1),F(10)]):
    d0,linear,remainder=expansion(q,pi,v)
    check('resolvent_identity',rv(q,v)==d0+linear+remainder)
    check('resolvent_sign_and_bound', remainder>=0 and 0<=pi*(pi+2*v)/(pi+v)**2<=2*pi/v)
    if q>0:
        check('actual_remainder_ratio',remainder/rv(q,v)==(v/(pi+v))**2*(1-pi/q)**2)

# Actual full polynomial supported at norm 7 in the diagnostic fixed W.
# O=Z[omega], omega^2+omega+1=0. Split primes have roots omega=4 and 2 mod7.
# zeta6=1+omega; its images are 5 and 3. No floating-point roots of unity.
log5={pow(5,k,7):k for k in range(6)}
log3={pow(3,k,7):k for k in range(6)}
zeta=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]  # basis 1,zeta6

def zadd(x: tuple[int,int],y: tuple[int,int]) -> tuple[int,int]:
    return x[0]+y[0],x[1]+y[1]

def znorm(x: tuple[int,int]) -> int:
    a,b=x
    return a*a+a*b+b*b

def norm(a: int,b: int) -> int:
    return a*a-a*b+b*b

def energy_data(a: int,b: int) -> tuple[F,F,F]:
    x,y=(a+4*b)%7,(a+2*b)%7
    cx=zeta[log5[x]] if x else (0,0)
    cy=zeta[log3[y]] if y else (0,0)
    scale=F(8,39)  # (-4/sqrt(78))^2
    q=scale*znorm(zadd(cx,cy))
    pi=scale*(int(x!=0)+int(y!=0))
    pi4=2*scale*scale if x and y else F(0)
    return q,pi,pi4

# Bounds 25<=norm<=97 fit the plateau of a fixed smooth radial rho at U=49.
rows=[(a,b) for a,b in product(range(-20,21),repeat=2) if 25<=norm(a,b)<=97]
# norm>=3/4*max(a^2,b^2), so this box exhausts the shell.
check('full_shell_exhaustion',F(3,4)*21*21>97)
check('parameter_band',78**25<=49**28 and 78**100>=49**111)
check('cutoff_C',49**3<2**32)
check('cutoff_P',49**7507<2**375000)
# Any nontrivial ideal has norm>=3, and 3^6>97, so all these rows are 6-free.
check('sixth_free_all_rows',3**6>97)
rowset=set(rows)
units=[(1,0),(0,1),(-1,-1),(-1,0),(0,-1),(1,1)]
def mul(x: tuple[int,int],y: tuple[int,int]) -> tuple[int,int]:
    a,b=x;c,d=y
    return a*c-b*d,a*d+b*c-b*d
for u,z in product(rows,units):
    check('all_six_units_retained',mul(u,z) in rowset)
    check('unit_invariant_actual_Q',energy_data(*mul(u,z))[0]==energy_data(*u)[0])

# Constant four-column contribution by exact enumeration of phase labels.
for x,y in product(range(7),repeat=2):
    active=[k for k,present in enumerate([x!=0,y!=0]) if present]
    labels=[(1,0),(0,1)]
    ocoeff=defaultdict(int)
    for n,m in product(active,repeat=2):
        if n!=m:
            s=tuple((labels[n][j]-labels[m][j])%6 for j in range(2))
            ocoeff[s]+=1
    constant=sum(v*ocoeff.get(tuple((-e)%6 for e in s),0) for s,v in ocoeff.items())
    check('all_residue_zero_masks_and_quartets',constant==(2 if x and y else 0))

hist=Counter(energy_data(*u)[0]/F(8,39) for u in rows)
# All 276 actual rows enter every aggregate; V samples check algebra only.
for v in [F(1,24),F(1,12),F(8,39),F(1),F(5)]:
    total=F(0); d0sum=F(0); lsum=F(0); d4sum=F(0); n4sum=F(0)
    for u in rows:
        q,pi,pi4=energy_data(*u)
        d0,linear,rem=expansion(q,pi,v)
        omega=v*v/((pi+v)**2*(q+v))
        n4=omega*((q-pi)**2-pi4)
        check('full_polynomial_resolvent_quartet',rv(q,v)==d0+linear+omega*pi4+n4)
        total+=rv(q,v);d0sum+=d0;lsum+=linear;d4sum+=omega*pi4;n4sum+=n4
    check('full_shell_return',total==d0sum+lsum+d4sum+n4sum)

# Six actual shell elements with residues (5^s,1), not a replacement row set.
representatives=[]
for s in range(6):
    matches=[u for u in rows if (u[0]+4*u[1])%7==pow(5,s,7) and (u[0]+2*u[1])%7==1]
    u=min(matches,key=lambda ab:(abs(norm(*ab)-49),abs(ab[0])+abs(ab[1]),ab))
    representatives.append(u)
    check('actual_subgroup_representatives',energy_data(*u)[0]==F(8,39)*[4,3,1,0,1,3][s])

# Convolution entrance falsifier: choose exp(-c*t)=1/2, exactly.
minus=[F(1,16),F(1,8),F(1,2),F(1),F(1,2),F(1,8)]
plus =[F(1),F(1,2),F(1,8),F(1,16),F(1,8),F(1,2)]
cos2=[2,1,-1,-2,-1,1]
def eig(h: list[F],k: int) -> F:
    return sum((h[s]*cos2[(k*s)%6]/2 for s in range(6)),F(0))
minus_eigs=[eig(minus,k) for k in range(6)]
plus_eigs=[eig(plus,k) for k in range(6)]
check('positive_distance_kernel_control',all(x>0 for x in plus_eigs))
check('heat_kernel_negative_eigenvalue',minus_eigs[1]==F(-21,16))
check('heat_kernel_full_spectrum',minus_eigs==[F(37,16),F(-21,16),F(7,16),F(-3,16),F(7,16),F(-21,16)])
quad=sum((F(cos2[i]*cos2[j])*minus[(i-j)%6] for i,j in product(range(6),repeat=2)),F(0))
check('heat_kernel_negative_quadratic_form',quad==F(-63,4))
for v in [F(1,24),F(1,12),F(8,39),F(1),F(100)]:
    c=F(8,39)
    h=[1/(v+c*q) for q in [4,3,1,0,1,3]]
    formula=1/(v+4*c)+1/(v+3*c)-1/(v+c)-1/v
    check('reciprocal_kernel_negative_eigenvalue',eig(h,1)==formula and formula<0)

# Full affine parameter rectangle, not grid extrapolation.
mins={}
for r,delta in product([F(28,25),F(113,100)],[F(0),F(1,100)]):
    ell=r-delta;c0=F(1,10000);h=r*(1+c0);p=(h-1)/6;v=5*p-F(3,500)
    gs={'constant':5*p+v,'short':5*p+v-F(3,32),'long':5*r*c0/6+5*(r-ell)/6+v}
    for key,val in gs.items():
        mins[key]=min(mins.get(key,val),val)
        check('affine_vertex_budget',val>F(1,200))
check('uniform_resolvent_error_gain',min(mins.values())==F(883,9375))
check('return_margin',F(883,9375)-F(1,200)==F(6689,75000))
check('inverse_margin',F(1,200)-F(113,1200000)==F(5887,1200000))
check('height_loss_budget',F(5887,1200000)-F(1,250)==F(1087,1200000))

print('EXACT_FINITE_DIAGNOSTICS_ONLY')
print('FULL_SHELL_ROWS',len(rows))
print('Q_OVER_C_HISTOGRAM',{str(k):hist[k] for k in sorted(hist)})
print('SUBGROUP_REPRESENTATIVES',[(a,b,norm(a,b)) for a,b in representatives])
print('HEAT_CONVOLUTION_SPECTRUM',[str(x) for x in minus_eigs])
print('HEAT_NEGATIVE_QUADRATIC_FORM',quad)
print('DISTANCE_CONTROL_SPECTRUM',[str(x) for x in plus_eigs])
print('ERROR_GAINS',{k:str(v) for k,v in mins.items()})
for key,value in sorted(checks.items()): print(key,value)
print('TOTAL',sum(checks.values()))
print('NO_COFINAL_CERTIFICATION; NO_SOURCE_ANALYTIC_CERTIFICATION; NO_LEAN_ARB_COMPARATOR')
