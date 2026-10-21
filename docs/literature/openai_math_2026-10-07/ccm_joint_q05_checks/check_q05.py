"""Exact algebra controls for Q05. NOT a CCM spectral or asymptotic certificate.
Run: python3 check_q05.py. No path or parameter substitution is required.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
from math import floor


def mu(n: int) -> int:
    result, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
        p += 1
    return -result if n > 1 else result


def zero(n=2):
    return tuple(tuple(Q(0) for _ in range(n)) for _ in range(n))


def add(A, B):
    return tuple(tuple(a + b for a, b in zip(ra, rb)) for ra, rb in zip(A, B))


def scale(s, A):
    return tuple(tuple(s * a for a in row) for row in A)


def product(A, B):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n))
                       for j in range(n)) for i in range(n))


def total(matrices, n=2):
    out = zero(n)
    for A in matrices:
        out = add(out, A)
    return out


def psd2(A):
    return (A[0][1] == A[1][0] and A[0][0] >= 0 and A[1][1] >= 0
            and A[0][0] * A[1][1] - A[0][1] ** 2 >= 0)


def polyadd(a, b):
    result = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        result[i] += x
    for i, x in enumerate(b):
        result[i] += x
    return result


def polymul(a, b):
    result = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def derivative(a):
    return [i * a[i] for i in range(1, len(a))] or [Q(0)]


def value(a, x):
    return sum(c * x ** i for i, c in enumerate(a))


def integral(a, lo, hi):
    return sum(c * (hi ** (i + 1) - lo ** (i + 1)) / Q(i + 1)
               for i, c in enumerate(a))

stats = Counter()
removed_cross_detected = False
noncommutation_seen = False
for D in range(2, 19):
    B = [((Q(i + 1, i + 3), Q((-1) ** i, i + 2)),
          (Q((-1) ** i, i + 2), Q(2 * i - 3, i + 4))) for i in range(1, D + 1)]
    X = [scale(mu(D + i + 1), B[i]) for i in range(D)]
    for i in range(D - 1):
        noncommutation_seen |= product(X[i], X[i + 1]) != product(X[i + 1], X[i])
    windows = [total(X[i - 1] for i in range(1, D + 1) if j <= i < j + D)
               for j in range(2 - D, D + 1)]
    G_window = scale(Q(1, D), total(product(C, C) for C in windows))
    # Constant Laurent coefficient of F_D(z) Phi(z)^* Phi(z).
    G_fourier = total(scale(Q(D - abs(i - j), D), product(X[i], X[j]))
                      for i in range(D) for j in range(D))
    assert G_window == G_fourier
    stats['ordered_Fejer_Fourier_window_identity'] += 1
    diagonal = total(product(C, C) for C in X)
    off = total(scale(Q(D - h, D),
                      add(product(X[i], X[i + h]), product(X[i + h], X[i])))
                for h in range(1, D) for i in range(D - h))
    assert add(diagonal, off) == G_fourier
    stats['all_shift_anticommutator_return'] += 1
    # Parseval is the zeroth coefficient of Phi^* Phi, without the Fejer weight.
    laurent = {}
    for i in range(D):
        for j in range(D):
            laurent[j - i] = add(laurent.get(j - i, zero()), product(X[i], X[j]))
    assert laurent[0] == diagonal
    stats['operator_Parseval_diagonal'] += 1
    T = total(X)
    assert psd2(add(scale(Q(2 * D - 1, D), G_fourier), scale(-1, product(T, T))))
    stats['exact_window_reconstruction_inequality'] += 1
    removed_cross_detected |= G_fourier != diagonal
    # Exact discrete Abel formula, including zero-frequency and a second phase.
    for phase in (Q(1), Q(-1)):
        a = [Q(mu(D + i + 1)) * phase ** (D + i + 1) for i in range(D)]
        prefix = []
        running = Q(0)
        for item in a:
            running += item
            prefix.append(running)
        rhs = scale(prefix[-1], B[-1])
        for i in range(D - 1):
            rhs = add(rhs, scale(-prefix[i], add(B[i + 1], scale(-1, B[i]))))
        lhs = total(scale(ai, Bi) for ai, Bi in zip(a, B))
        assert lhs == rhs
        stats['matrix_Abel_with_actual_mu'] += 1
assert noncommutation_seen and removed_cross_detected
stats['discarding_mixed_products_detected'] += 1

# Removing the intermediate projection changes the product, even for a contraction.
P = ((Q(1), Q(0), Q(0)), (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(0)))
Q0 = ((Q(0), Q(0), Q(1)), (Q(0), Q(0), Q(0)), (Q(1), Q(0), Q(0)))
compressed = product(product(P, Q0), P)
assert product(compressed, compressed) == zero(3)
assert product(product(P, product(Q0, Q0)), P) != zero(3)
stats['intermediate_projection_deletion_detected'] += 1

# Euler formula for endpoint-zero polynomials. These are test functions, not A_m.
wrong_sign_detected = False
for y in (Q(3, 2), Q(2), Q(7, 3), Q(3), Q(9, 2), Q(6)):
    for degree in range(4):
        g = polymul(polymul([Q(-1), Q(1)], [y, Q(-1)]), [Q(0)] * degree + [Q(1)])
        assert value(g, Q(1)) == value(g, y) == 0
        err = sum(value(g, Q(k)) for k in range(1, floor(y) + 1)) - integral(g, Q(1), y)
        beta_integral = Q(0)
        gp = derivative(g)
        for k in range(1, floor(y) + 1):
            hi = min(Q(k + 1), y)
            if hi > k:
                beta_integral += integral(polymul([Q(k), Q(-1)], gp), Q(k), hi)
        assert err == -beta_integral
        wrong_sign_detected |= err != beta_integral
        stats['endpoint_exact_Euler_derivative_return'] += 1
assert wrong_sign_detected
stats['wrong_Euler_sign_detected'] += 1

# A disappearing term at x=m/k has zero value AND first derivative only with both conditions.
for m in (12, 17, 31):
    for k in (2, 3, 5):
        x0 = Q(m, k)
        A = [Q(m * m), Q(-2 * m), Q(1)]
        assert value(A, k * x0) == value(derivative(A), k * x0) == 0
        assert value([Q(1)], k * x0) != 0
        assert value([Q(m), Q(-1)], k * x0) == 0
        assert k * value(derivative([Q(m), Q(-1)]), k * x0) != 0
        stats['C1_cutoff_and_planted_endpoint_failures'] += 1

# Derivative-budget arithmetic: integral u^(-3/2)=2, integral log(u)u^(-3/2)=4.
for d1 in (Q(0), Q(1, 2), Q(3), Q(10)):
    for d2 in (Q(0), Q(2), Q(7, 3)):
        quadrature = 6 * (1 + d1) + 4 * (Q(3, 2) + 2 * d1 + d2)
        assert quadrature == 12 + 14 * d1 + 4 * d2
        assert 24 + quadrature == 36 + 14 * d1 + 4 * d2
        stats['variation_constant_arithmetic'] += 1

# Exact coherent-block energy. This is a scope-limited abstract control, not Mobius.
for D in range(2, 35):
    x = Q(1, D + 1)
    G = sum(Q(D - abs(i - j), D) * x * x for i in range(D) for j in range(D))
    assert G == Q(2 * D * D + 1, 3) * x * x
    assert G >= Q(2, 3) * D * D * x * x
    stats['coherent_block_Fejer_formula'] += 1

for eps in (Q(1, 1024), Q(1, 128), Q(1, 64), Q(1, 33)):
    assert Q(1, 2) + 2 * eps > Q(3, 8)
    assert Q(3, 2) * eps < Q(3, 8)
    assert (2 + 5 * eps) - (1 + 3 * eps) == 1 + 2 * eps
    stats['complete_power_and_cofinal_deficit'] += 1

out = {
    'status': 'PASS', 'counts': dict(stats), 'total_checks': sum(stats.values()),
    'scope': 'Finite exact transfer algebra and deliberately distinct control models; not a universal CCM bound.',
    'actual_ccm_spectral_runs': 0, 'arb_runs': 0, 'lean_runs': 0,
    'independent_review': 'NOT_RUN',
    'registration_sha256': hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(out, ensure_ascii=False, indent=2))
