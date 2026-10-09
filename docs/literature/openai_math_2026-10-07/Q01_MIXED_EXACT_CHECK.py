"""Finite algebra diagnostics. Not a certificate of any analytic moment bound."""
from fractions import Fraction as F
from itertools import product
from math import prod
from collections import Counter

checks = Counter()

def mu_power(e: int) -> int:
    return 1 if e == 0 else -1 if e == 1 else 0

def divisors_sf(ps: tuple[int, ...]):
    for bits in product((0, 1), repeat=len(ps)):
        yield prod(p for p, b in zip(ps, bits) if b), (-1) ** sum(bits)

# Coefficient of a full prime-power inverse, on up to three independent slots.
for s in (1, 2, 3):
    for ks in product(range(1, 6), repeat=s):
        lhs = sum(prod(mu_power(k-j) for k, j in zip(ks, js))
                  for js in product(*(range(1, k+1) for k in ks)))
        assert lhs == int(all(k == 1 for k in ks))
        checks['all_power_collapse'] += 1

# The exact PRODUCT-cutoff finite difference, at every breakpoint and midpoint.
for ps in ((7, 13), (7, 13, 19)):
    for ks in product(range(1, 5), repeat=len(ps)):
        dnorm = prod(p**k for p, k in zip(ps, ks))
        eps_primes = tuple(p for p, k in zip(ps, ks) if k >= 2)
        eps = list(divisors_sf(eps_primes))
        breaks = sorted({F(dnorm, e) for e, _ in eps})
        probes = {F(1, 2), *breaks, breaks[-1] + 1}
        probes.update((a+b)/2 for a, b in zip(breaks, breaks[1:]))
        probes.add(breaks[0]/2)
        for x in sorted(probes):
            lhs = sum(prod(mu_power(k-j) for k, j in zip(ks, js))
                      * int(x <= prod(p**j for p, j in zip(ps, js)))
                      for js in product(*(range(1, k+1) for k in ks)))
            rhs = sum(sign * int(x <= F(dnorm, e)) for e, sign in eps)
            assert lhs == rhs
            checks['coupled_cutoff'] += 1

# h = g*t recombination with strict q_g<G, including every boundary equality.
ps = (7, 13, 19, 31)
for selected in product((0, 1), repeat=len(ps)):
    hs = tuple(p for p, b in zip(ps, selected) if b)
    h = prod(hs)
    divs = list(divisors_sf(hs))
    for G in (F(2), F(7), F(8), F(13), F(14), F(20), F(31), F(32)):
        beta = sum((-1)**len(hs) * mug for g, mug in divs if g < G)
        direct = sum(mut for t, mut in divs if F(h, t) < G)
        assert beta == direct
        if h < G:
            assert beta == int(h == 1)
        checks['g_t_recombination'] += 1

# Finite actual Mobius-coefficient polynomial test in a three-prime monoid.
# Any profile values are allowed in this identity; this test is not an analytic input.
ps = (7, 13, 19)
rows = list(product((0, 1), repeat=3))
ideals = [(prod(p for p, b in zip(ps, bits) if b), bits,
           (-1)**sum(bits)) for bits in rows]

def cp(bits, other):
    return not any(a and b for a, b in zip(bits, other))

def phase(bits, values):
    return prod(x for x, b in zip(values, bits) if b)

def W(y):
    return (2*y-1)*(2-y) if F(1, 2) <= y <= 2 else F(0)

for values in product((-1, 0, 1), repeat=3):
    for abits in rows:
        for L in (F(7), F(50), F(250)):
            for G, K in ((F(8), F(14)), (F(20), F(23))):
                direct = F(0)
                collapsed = F(0)
                for qg, gbits, _ in ideals:
                    if not(qg < G and cp(abits, gbits)) or phase(gbits, values) == 0:
                        continue
                    for qb, bbits, mub in ideals:
                        if not cp(bbits, tuple(x or y for x, y in zip(abits, gbits))):
                            continue
                        for qc, cbits, muc in ideals:
                            if not cp(cbits, tuple(x or y for x, y in zip(abits, gbits))):
                                continue
                            # Common primes above K remain permitted.
                            if any(b and cc and prime <= K
                                   for prime, b, cc in zip(ps, bbits, cbits)):
                                continue
                            direct += (mub*muc*phase(bbits, values)*phase(cbits, values)
                                       *W(qg*qb/L)*W(qg*qc/L))
                for qh, hbits, muh in ideals:
                    if any(b and prime > K for prime, b in zip(ps, hbits)):
                        continue
                    if not cp(abits, hbits) or phase(hbits, values) == 0:
                        continue
                    beta = 0
                    for qg, gbits, mug in ideals:
                        if qg < G and all(not b or h for b, h in zip(gbits, hbits)):
                            beta += muh*mug
                    poly = sum(mun*phase(nbits, values)*W(qh*qn/L)
                               for qn, nbits, mun in ideals
                               if cp(nbits, tuple(x or y for x, y in zip(abits, hbits))))
                    collapsed += beta*poly**2
                assert direct == collapsed
                checks['masked_polynomial_recombination'] += 1

# Every exponent is affine in (r, ell), so these are all polytope vertices.
rlo, rhi, c, eta = F(28, 25), F(113, 100), F(1, 10000), F(1, 200)
mins = {}
for r in (rlo, rhi):
    h = r*(1+c)
    p = (h-1)/6
    for ell in (r-F(1, 100), r):
        exponents = {
            'PU': p+1,
            'g_boundary': p+F(1, 6)+F(5, 6)*ell-F(1, 120),
            'Euler_mixed': p+F(7, 12)+F(5, 12)*ell-F(1, 192),
            'Euler_long': p+F(1, 6)+F(5, 6)*ell-F(1, 96),
            'short_scale': p+F(1, 6)+F(5, 6)*(r-F(1, 100)),
        }
        for name, exponent in exponents.items():
            margin = h-eta-exponent
            assert margin > 0
            mins[name] = min(mins.get(name, margin), margin)
            checks['budget_vertices'] += 1
assert mins['PU'] == F(1783,18750)
assert mins['g_boundary'] == mins['short_scale'] == F(257,75000)
assert mins['Euler_mixed'] == F(30181,600000)
assert mins['Euler_long'] == F(551,100000)
assert eta-F(5,6)*rhi*c == F(5887,1200000)
assert F(1,10)*F(1,100) == F(1,1000)
checks['rational_equalities'] += 7

# Planted defects: deleting repeated shifts; independent cutoffs; omitted mixed term;
# centering does not cancel a zero-extended character diagonal; strict-boundary error.
assert mu_power(1) == -1  # n=p^2, retaining only shift j=1 leaves -1 instead of 0.
assert (7*13 >= 50) and not (7 >= 50 and 13 >= 50)
assert tuple(1-int(x<=1183)-int(x<=637)+int(x<=91)
             for x in (F(100), F(2000))) == (-1, 1)
assert 1-1-1+1 == 0 and 1-1-1 != 0  # omitted two-prime intersection fails
assert F(1,2)-F(1,2) == 0 and F(1,2)*1-F(1,2)*0 == F(1,2)
assert sum((-1)*mug for g,mug in divisors_sf((7,)) if g < 7) == -1
checks['planted_defects_detected'] += 6

print('EXACT_FINITE_DIAGNOSTICS_ONLY')
for key, value in checks.items():
    print(key, value)
print('TOTAL', sum(checks.values()))
print('MARGINS', {k: str(v) for k,v in mins.items()})
print('NO_ANALYTIC_SOURCE_CERTIFICATION; NO_LEAN; NO_ARB; NO_COMPARATOR')
