"""Exact Q04 finite diagnostics. No analytic-moment or cofinal certification."""
from collections import Counter
from fractions import Fraction as F
from itertools import product

checks = Counter()
Z, O = (F(0), F(0)), (F(1), F(0))
def ca(x, y): return (x[0]+y[0], x[1]+y[1])
def cs(x, a): return (a*x[0], a*x[1])
def cm(x, y):
    return (x[0]*y[0]-x[1]*y[1],
            x[0]*y[1]+x[1]*y[0]+x[1]*y[1])
def cc(x): return (x[0]+x[1], -x[1])
def cp(x, n):
    ans = O
    for _ in range(n): ans = cm(ans, x)
    return ans
roots = tuple(cp((F(0), F(1)), k) for k in range(6))
def csum(xs):
    ans = Z
    for x in xs: ans = ca(ans, x)
    return ans

def en(x):
    a, b = x
    return a*a-a*b+b*b
def em(x, y):
    a,b=x; c,d=y
    return (a*c-b*d, a*d+b*c-b*d)
def ec(x): return (x[0]-x[1], -x[1])
def shell(n):
    # norm >= 3a^2/4 and >= 3b^2/4; this box is safely larger.
    bnd = 2*n + 1
    return [(a,b) for a in range(-bnd,bnd+1)
            for b in range(-bnd,bnd+1) if en((a,b)) == n]
units = shell(1)
assert len(units) == 6
pi, pibar = (-2,-3), (1,3)
assert en(pi) == en(pibar) == 7 and ec(pi) == pibar
assert {x for x in shell(7) if x[0]%3 == 1 and x[1]%3 == 0} == {pi,pibar}
checks['Eisenstein_data'] += 3

def chi_at(prime, u):
    q=en(prime)
    w=(-prime[0]*pow(prime[1], -1, q)) % q
    residue=(u[0]+u[1]*w) % q
    if not residue: return Z
    zeta=(1+w) % q
    root=pow(residue, (q-1)//6, q)
    return roots[next(k for k in range(6) if pow(zeta,k,q) == root)]

# Complete actual polynomial on the isolated norm-7 window: j_C=-2, W=2.
U,L=49,78
assert L**25 <= U**28 and L**100 >= U**111
assert U**3 < 2**32                       # C < 2
assert U**7507 < 2**375000                # P < 2
assert U**7057 < 2**75000                 # 1 < V0 < 2
checks['Q04_parameter_membership'] += 4
rows=shell(49)
assert len(rows)==18
orbits=[{em(z,u) for z in units} for u in [(7,0), em(pi,pi), em(pibar,pibar)]]
assert len(set.union(*orbits))==18 and all(len(x)==6 for x in orbits)
checks['all_norm49_rows'] += 2

def Jscaled(u): return cs(ca(chi_at(pi,u), chi_at(pibar,u)), F(-4))
def Q(u):
    return sum(cm(Jscaled(em(z,u)), cc(Jscaled(em(z,u))))[0]
               for z in units)/(6*L)
values={u:Q(u) for u in rows}
assert Counter(values.values()) == {F(0):6, F(8,39):12}
checks['complete_polynomial_values'] += 1
for u in rows:
    for z in units:
        assert Q(em(z,u))==Q(u)
        checks['actual_unit_invariance'] += 1
# The actual V=V0/24 belongs to (1/24,1/12); this selector is identical.
selected=[u for u in rows if values[u] > F(1,12)]
assert len(selected)==12 and F(8,39)>F(1,12)
E=sum(values[u] for u in selected)
E_rad=F(len(selected),len(rows))*sum(values.values())
cov=E-E_rad
pair=sum(values[u]-values[v] for u in selected
         for v in rows if v not in selected)/len(rows)
assert E==F(32,13) and E_rad==F(64,39) and cov==pair==F(32,39)
checks['actual_radial_covariance'] += 2
assert -cov == F(-32,39)                  # planted free radial replacement fails
checks['planted_errors_detected'] += 1

# General same-shell conditional covariance and lowered-level repair.
for xs in product((F(0),F(1),F(3)), repeat=4):
    for v in (F(1,2),F(1),F(2)):
        flags=[int(x>v) for x in xs]
        av=sum(flags)/len(xs)
        delta=sum((t-av)*x for t,x in zip(flags,xs))
        pp=sum((flags[i]-flags[j])*(xs[i]-xs[j])
               for i in range(4) for j in range(4))/(2*len(xs))
        assert delta==pp and delta>=0
        tail=sum(max(x-v,0) for x in xs)
        repair=2*len(xs)*max(sum(xs)/len(xs)-v/(2*len(xs)),0)
        assert tail<=repair
        checks['covariance_and_shell_repair'] += 1

# Sixth-power core test with every zero branch (single-prime finite ring).
for prime in (pi,(1,-3)):
    q=en(prime)
    chars=[chi_at(prime,(x,0)) for x in range(q)]
    for i,j in product(range(9),repeat=2):
        if i==j==0: continue
        pairvalues=[]
        for x in range(q):
            lhs=O if i==0 else (Z if x==0 else cp(chars[x],i))
            rhs=O if j==0 else (Z if x==0 else cp(chars[x],j))
            pairvalues.append(cm(lhs,cc(rhs)))
        g0=csum(pairvalues)
        assert g0 == ((F(q-1),F(0)) if (i-j)%6==0 else Z)
        assert pairvalues[0]==Z
        checks['all_power_principal_classifier'] += 1
    assert cp(chars[0],6)==Z               # sixth powers do NOT erase zeros
    checks['planted_errors_detected'] += 1

# Exact cyclotomic computation over Q(zeta_6)[z]/(1+z+...+z^(q-1)).
def canon(a):
    last=a[-1]
    return tuple(ca(v,cs(last,-1)) for v in a[:-1])+(Z,)
def pmul(a,b):
    q=len(a); out=[Z]*q
    for i,x in enumerate(a):
        if x==Z: continue
        for j,y in enumerate(b):
            if y!=Z: out[(i+j)%q]=ca(out[(i+j)%q],cm(x,y))
    return canon(out)
def pconj(a):
    q=len(a); out=[Z]*q
    for i,x in enumerate(a): out[(-i)%q]=ca(out[(-i)%q],cc(x))
    return canon(out)
def const(q,c): return (c,)+(Z,)*(q-1)
def gauss(prime,a,k):
    q=en(prime); out=[Z]*q
    for x in range(1,q):
        char=cp(chi_at(prime,(x,0)),a)
        t=(-prime[1]*k*x)%q                # literal source e(kx/prime)
        out[t]=ca(out[t],char)
    return canon(out)
for prime in (pi,(1,-3)):
    q=en(prime)
    for a in range(6):
        gs=[gauss(prime,a,k) for k in range(q)]
        for k,g in enumerate(gs):
            if a==0: assert g==const(q,(F(q-1 if k==0 else -1),F(0)))
            elif k==0: assert g==const(q,Z)
            else: assert pmul(g,pconj(g))==const(q,(F(q),F(0)))
            checks['literal_local_Gauss'] += 1
        for x in range(q):
            out=[Z]*q
            for k,g in enumerate(gs):
                shift=(prime[1]*k*x)%q
                for t,c in enumerate(g): out[(t+shift)%q]=ca(out[(t+shift)%q],c)
            inv=canon([cs(c,F(1,q)) for c in out])
            expect=Z if x==0 else cp(chi_at(prime,(x,0)),a)
            assert inv==const(q,expect)
            checks['literal_Fourier_inversion'] += 1

for a,b in product(range(9),repeat=2):
    n=7**a*13**b
    assert ((n-1)//6)%6 == (a+2*b)%6
    checks['all_power_unit_class_mod36'] += 1

rlo,rhi,c0,eta=F(28,25),F(113,100),F(1,10000),F(1,200)
for r in (rlo,rhi):
    h=r*(1+c0); p=(h-1)/6
    for ell in (r-F(1,100),r):
        assert 5*p-eta>0
        assert 5*p-F(3,32)-eta>0
        assert 5*p-F(3,32)+F(1,100)-eta>0
        assert F(5,6)*r*c0+F(5,6)*(r-ell)+F(11,600)-eta>0
        checks['affine_return_vertices'] += 4
assert eta-F(5,6)*rhi*c0==F(5887,1200000)
assert eta-F(5,6)*rhi*c0-F(1,250)==F(1087,1200000)
checks['inverse_return_equalities'] += 2
print('Q04 EXACT DIAGNOSTICS')
for k,v in sorted(checks.items()): print(k,v)
print('TOTAL',sum(checks.values()))
print('FINITE_RADIAL_LOSS',cov)
print('FULL_ANALYTIC_TARGET NOT_CERTIFIED')
