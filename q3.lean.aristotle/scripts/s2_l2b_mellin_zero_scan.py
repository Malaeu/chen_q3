#!/usr/bin/env python3
"""S2-L2b discriminator: do v3-class windows have Mellin zeros INSIDE the open strip?

v3 class (from MuntzV3ExactClassClosure.lean):
  Measurable, supp h ⊂ Icc 0 b, LipschitzOnWith K h (Ico 0 b), ∫_{Ioi 0} h = 0, 0 ≤ b.

Window model scanned here: h(u) = Σ_j c_j u^{a_j} on (0,1], zero outside.
Lipschitz on Ico 0 1 forces each exponent a_j = 0 or a_j >= 1
(for 0 < a < 1 the derivative blows up at 0).

Mellin:  M(w) = ∫_0^1 h(u) u^{w-1} du = Σ_j c_j / (w + a_j)
       = P(w) / Π_j (w + a_j),  deg P = (#terms - 1).

Zero-mass  ⇔  Σ_j c_j/(a_j+1) = 0  ⇔  M(1) = 0.
So w = 1 is ALWAYS a zero for the v3 class -- but w = 1 sits on the BOUNDARY
of the open strip (w = 1/2 + i z, |Im z| < 1/2  ⇔  Re w ∈ (0,1)).

Question that decides reading (i) vs (ii):
  are there zeros with Re w ∈ (0,1) strictly, i.e. OTHER than the forced w = 1?
"""

import itertools
import sympy as sp

w = sp.Symbol('w')


def mellin_numerator(exps, coeffs):
    """P(w) with M(w) = P(w)/Π(w+a_j)."""
    expr = sum(c / (w + a) for c, a in zip(coeffs, exps))
    return sp.Poly(sp.numer(sp.cancel(sp.together(expr))), w)


def zeros_of(exps, coeffs):
    P = mellin_numerator(exps, coeffs)
    if P.degree() < 1:
        return []
    if P.degree() <= 2:
        return [sp.nsimplify(r) for r in sp.roots(P, w)]
    try:
        return sp.nroots(P, n=15, maxsteps=200)
    except Exception:
        import numpy as np
        c = [complex(x) for x in P.all_coeffs()]
        return [sp.sympify(complex(r)) for r in np.roots(c)]


def inside_open_strip(z):
    re = sp.re(sp.N(z))
    return sp.N(0) < re < sp.N(1)


def zero_mass_solve(exps, free_coeffs):
    """Given all but the last coefficient, solve zero-mass for the last one."""
    c_last = sp.Symbol('c_last')
    coeffs = list(free_coeffs) + [c_last]
    mass = sum(c / (a + 1) for c, a in zip(coeffs, exps))
    sol = sp.solve(sp.Eq(mass, 0), c_last)
    return None if not sol else list(free_coeffs) + [sol[0]]


print("=" * 78)
print("PART 0 — the PL2 witness already in Lean (h = u - 3/2 u^2)")
print("=" * 78)
z0 = zeros_of([1, 2], [1, sp.Rational(-3, 2)])
print(f"  zeros: {z0}   inside open strip: {[z for z in z0 if inside_open_strip(z)]}")

print()
print("=" * 78)
print("PART 1 — ALL two-term v3 windows  h = u^a - lam u^b  (lam fixed by zero-mass)")
print("=" * 78)
bad2 = 0
for a, b in itertools.combinations([0, 1, 2, 3, 4, 5, 6, 7], 2):
    coeffs = zero_mass_solve([a, b], [sp.Integer(1)])
    if coeffs is None:
        continue
    zs = zeros_of([a, b], coeffs)
    inside = [z for z in zs if inside_open_strip(z)]
    if inside:
        bad2 += 1
        print(f"  a={a} b={b}: INSIDE {inside}")
print(f"  two-term windows with an interior zero: {bad2}   (all zeros land exactly on w=1)")

print()
print("=" * 78)
print("PART 2 — three-term v3 windows: scan the one free shape parameter")
print("=" * 78)
interior_hits = []
clean = []
for exps in itertools.combinations([0, 1, 2, 3, 4, 5], 3):
    for t in [sp.Rational(k, 4) for k in range(-12, 13) if k != 0]:
        coeffs = zero_mass_solve(list(exps), [sp.Integer(1), t])
        if coeffs is None:
            continue
        zs = zeros_of(list(exps), coeffs)
        inside = [z for z in zs if inside_open_strip(z)]
        if inside:
            interior_hits.append((exps, t, inside))
        else:
            clean.append((exps, t))
print(f"  scanned: {len(interior_hits) + len(clean)} windows")
print(f"  with a zero strictly INSIDE the open strip: {len(interior_hits)}")
print(f"  clean (all zeros outside / on boundary)   : {len(clean)}")
if interior_hits:
    print("  first 8 interior-zero examples (exponents, shape param, zeros inside):")
    for exps, t, inside in interior_hits[:8]:
        print(f"    exps={exps} t={t}  ->  {[sp.N(z, 8) for z in inside]}")
if clean:
    print("  first 8 CLEAN examples (candidate good windows):")
    for exps, t in clean[:8]:
        print(f"    exps={exps} t={t}")

print()
print("=" * 78)
print("PART 3 — four-term windows (does richer structure push zeros inside?)")
print("=" * 78)
hits4 = 0
tot4 = 0
clean4 = []
for exps in itertools.combinations([0, 1, 2, 3, 4, 5], 4):
    for t1 in [sp.Rational(k, 2) for k in range(-4, 5) if k != 0]:
        for t2 in [sp.Rational(k, 2) for k in range(-4, 5) if k != 0]:
            coeffs = zero_mass_solve(list(exps), [sp.Integer(1), t1, t2])
            if coeffs is None:
                continue
            tot4 += 1
            zs = zeros_of(list(exps), coeffs)
            inside = [z for z in zs if inside_open_strip(z)]
            if inside:
                hits4 += 1
            else:
                clean4.append((exps, t1, t2))
print(f"  scanned {tot4} four-term windows")
print(f"  with interior zero: {hits4}    clean: {len(clean4)}")
if clean4:
    print(f"  example clean four-term window: exps={clean4[0][0]} t1={clean4[0][1]} t2={clean4[0][2]}")
