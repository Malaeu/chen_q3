#!/usr/bin/env python3
"""Exact algebra controls for Q31. Not a numerical CCM or RH certificate.
Requires Python 3 and SymPy. Writes deterministic JSON to the supplied path.
"""
from __future__ import annotations
import json
import sys
from pathlib import Path
import sympy as s

passed: list[str] = []
planted: list[str] = []

def eq(name, a, b):
    d = a - b
    ok = all(s.simplify(x) == 0 for x in d) if isinstance(d, s.MatrixBase) else s.simplify(d) == 0
    if not ok:
        raise AssertionError(f'{name}: {s.simplify(d)}')
    passed.append(name)

def reject(name, a, b):
    d = a - b
    ok = any(s.simplify(x) != 0 for x in d) if isinstance(d, s.MatrixBase) else s.simplify(d) != 0
    if not ok:
        raise AssertionError(f'planted error went undetected: {name}')
    planted.append(name)

def chi3(n: int) -> int:
    return (0, 1, -1)[n % 3]

def euler_remainder(g, x, b):
    """Integral of fractional part times derivative, exact rational breaks."""
    n = int(s.floor(b))
    out = s.S.Zero
    for k in range(1, n + 1):
        right = min(s.Integer(k + 1), b)
        if right > k:
            out += s.integrate((x-k)*s.diff(g, x), (x, k, right))
    return out

# 1. Additive U2 energy, preserving every complex off-diagonal correlation.
for idx, b in enumerate([
    [s.Integer(1), 1+s.I, -2*s.I, s.Rational(2,3)],
    [1, -1, 1, -1, 1],
    [s.I, 0, 2-s.I, -1],
]):
    N = len(b)
    corr_energy = s.S.Zero
    for h in range(-N+1, N):
        z = sum((b[n+h]*s.conjugate(b[n]) for n in range(N) if 0 <= n+h < N), s.S.Zero)
        corr_energy += z*s.conjugate(z)
    quad = s.S.Zero
    for a in range(N):
        for bb in range(N):
            for c in range(N):
                d = a - bb + c
                if 0 <= d < N:
                    quad += b[a]*s.conjugate(b[bb])*b[c]*s.conjugate(b[d])
    eq(f'U2_complete_energy_{idx}', corr_energy, quad)
    if idx == 0:
        diagonal = sum(s.expand_complex(z*s.conjugate(z)) for z in b)**2
        reject('drop_nonzero_shift_correlations', corr_energy, diagonal)
        wrong = sum((sum((b[n+h]*b[n] for n in range(N) if 0 <= n+h < N), s.S.Zero))**2
                    for h in range(-N+1, N))
        reject('remove_complex_conjugations', corr_energy, wrong)
for N in [1, 2, 3, 7, 11]:
    eq(f'interval_energy_normalization_{N}',
       sum((N-abs(h))**2 for h in range(-N+1, N)), s.Rational(2*N**3+N, 3))

# 2. Finite Fourier Abel identity for the FULL Hermitian matrix weight.
z = s.symbols('z', nonzero=True)
weights = [s.Matrix([[j*j+1, j+s.I*(j+1)], [j-s.I*(j+1), 2-j]]) for j in range(1, 5)]
D = lambda k: sum(z**r for r in range(1, k+1))
lhs = sum((weights[j-1]*z**j for j in range(1,5)), s.zeros(2))
rhs = weights[-1]*D(4) + sum(((weights[j-1]-weights[j])*D(j) for j in range(1,4)), s.zeros(2))
eq('full_matrix_fourier_Abel', lhs, rhs)
reject('remove_Fourier_terminal_matrix', lhs, rhs-weights[-1]*D(4))
# Formal pairing: all positive and negative Fourier coefficients agree exactly.
b = [s.Rational(1,2), -2, 1+s.I, -s.I]
poly_b = sum(b[j-1]*z**j for j in range(1,5))
poly_H = sum((weights[j-1]*z**(-j) for j in range(1,5)), s.zeros(2))
constant = (poly_b*poly_H).applyfunc(lambda v: s.expand(v).coeff(z, 0))
eq('full_matrix_Fourier_pairing', constant,
   sum((b[j]*weights[j] for j in range(4)), s.zeros(2)))

# 3. Exact finite Euler edge, including a nonintegral terminal interval.
x = s.symbols('x', real=True)
for idx, end in enumerate([s.Rational(13,3), s.Integer(5)]):
    g = (end-x)*(x*x+2*x+3)
    actual = sum(g.subs(x,k) for k in range(1,int(s.floor(end))+1))
    restored = s.integrate(g,(x,1,end))+g.subs(x,1)+euler_remainder(g,x,end)
    eq(f'finite_Euler_with_zero_top_{idx}', actual, restored)
# Nonzero top exposes the otherwise necessary -{b}g(b).
end=s.Rational(13,3)
g=x*x+1
actual=sum(g.subs(x,k) for k in range(1,5))
base=s.integrate(g,(x,1,end))+g.subs(x,1)+euler_remainder(g,x,end)
eq('finite_Euler_general_terminal', actual, base-(end-s.floor(end))*g.subs(x,end))
reject('drop_noninteger_top_return', actual, base)

# 4. Dirichlet-character cancellation and its finite Abel identity.
for start in [0,1,2,7]:
    eq(f'complete_character_period_{start}', sum(chi3(start+j) for j in range(1,4)), 0)
for B in [4,7,10]:
    g=(s.Integer(B)-x)*(x+1)
    left=sum(chi3(k)*g.subs(x,k) for k in range(1,B+1))
    right=-sum(sum(chi3(n) for n in range(1,k+1))*s.integrate(s.diff(g,x),(x,k,k+1)) for k in range(1,B))
    eq(f'finite_character_Abel_{B}',left,right)

# 5. Exact Cramer and exceptional-character coefficient return.
# beta=1/2 is ONLY an algebraic model in this control, not an actual Siegel zero.
for m, primes in [(17,[2,3]),(23,[2,3,5]),(11,[2,3,5,7])]:
    P=s.prod(primes); cw=s.Rational(P,int(s.totient(P)))
    for n in range(1,m+1):
        sieve=sum(int(s.mobius(d)) for d in s.divisors(P) if n%d==0)
        model=cw*int(s.gcd(n,P)==1)
        eq(f'sieve_finite_{m}_{n}',cw*sieve,model)
    beta=s.Rational(1,2)
    H=lambda n:s.Matrix([[n-m, s.I*(n-m)],[-s.I*(n-m),(n-m)*(n+1)]])
    direct=sum((cw*int(s.gcd(n,P)==1)*(1-chi3(n)*n**(beta-1))*H(n) for n in range(1,m+1)),s.zeros(2))
    rebuilt=s.zeros(2)
    for d in s.divisors(P):
        if d>m: continue
        inner=sum((H(d*k) for k in range(1,m//d+1)),s.zeros(2))
        twisted=sum((chi3(k)*(d*k)**(beta-1)*H(d*k) for k in range(1,m//d+1)),s.zeros(2))
        rebuilt += cw*int(s.mobius(d))*(inner-chi3(d)*twisted)
    eq(f'full_finite_Siegel_model_{m}',direct,rebuilt)
    if m==17:
        wrong=sum((cw*int(s.gcd(n,P)==1)*H(n) for n in range(1,m+1)),s.zeros(2))
        reject('discard_exceptional_character',direct,wrong)
        without_one=sum((cw*int(s.gcd(n,P)==1)*H(n) for n in range(2,m+1)),s.zeros(2))
        reject('drop_model_atom_one_without_compensation',wrong,without_one)

# 6. Exact inclusion of proper prime powers with actual logarithmic symbols.
logs={2:s.symbols('log2'),3:s.symbols('log3'),5:s.symbols('log5'),7:s.symbols('log7'),11:s.symbols('log11'),13:s.symbols('log13')}
def Lam(n):
    fac=s.factorint(n)
    return logs[next(iter(fac))] if len(fac)==1 else s.S.Zero
cw=s.Rational(3,1)
model=lambda n:cw*int(s.gcd(n,6)==1)
for n in [1,2,4,8,9,12]:
    true=Lam(n) if n>1 else s.S.Zero
    eq(f'original_source_reassembly_{n}',model(n)+(true-model(n)),true)
reject('delete_square_4',Lam(4),0)

# 7. Integer tiling covers every physical index once, including odd top edges.
def ceil_fourth(n:int)->int:
    lo,hi=0,1
    while hi**4<n: hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**4>=n:hi=mid
        else:lo=mid
    return hi
for m,a0 in [(101,10),(255,12),(1000,13),(1001,13)]:
    bs=[m]
    while bs[-1]//2>=a0: bs.append(bs[-1]//2)
    B=bs[-1]
    cells=[]
    for j in range(len(bs)-1):
        X=bs[j+1]; D=bs[j]-X; count=ceil_fourth(X)
        h,r=divmod(D,count); y=X
        for k in range(count):
            length=h+(k<r)
            cells.append((y,y+length)); y+=length
        eq(f'tiling_block_endpoint_{m}_{j}',y,bs[j])
    indices=sorted(n for a,b in cells for n in range(a+1,b+1))
    eq(f'tiling_complete_{m}',s.Matrix(indices),s.Matrix(list(range(B+1,m+1))))
    eq(f'tiling_count_{m}',len(indices),m-B)

# 8. Exact output exponents; no numerical asymptotic sign inference.
e=s.symbols('epsilon',positive=True)
eq('model_exponent',e+e/2,3*e/2)
eq('low_sector_exponent',4*e/2,2*e)
eq('divisor_short_exponent',e+e/2,3*e/2)
eq('uniformity_log_exponent',s.Rational(2,16),s.Rational(1,8))
reject('replace_half_power_by_two_epsilon_at_1_over_64',s.Rational(1,2),2*s.Rational(1,64))
# Exact mapping back to the kept path deficit, with complete short sector.
chi,W,norm,G,Ashort=s.symbols('chi W norm G Ashort')
Aprime=2*chi*W*norm-W*G+Ashort
eq('actual_image_deficit_reassembly',W*G,2*chi*W*norm+Ashort-Aprime)

out={
 'test_kind':'FINITE_EXACT_ALGEBRA_NOT_CCM_SPECTRAL_CERTIFICATION',
 'exact_controls':len(passed),'planted_errors_detected':len(planted),
 'checks':passed,'planted':planted,
 'external_theorem_proof_checked':False,'production_CCM_checked':False,
 'Lean':False,'Arb':False,
}
target=Path(sys.argv[1] if len(sys.argv)>1 else 'exact_results.json')
target.write_text(json.dumps(out,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'exact_controls':len(passed),'planted_errors_detected':len(planted),'output':str(target)}))
