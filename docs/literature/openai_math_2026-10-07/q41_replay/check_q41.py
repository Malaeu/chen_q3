#!/usr/bin/env python3
"""Exact finite controls, not a CCM spectrum computation or a sign certificate.
All logarithms are formal sums of valuations times log(prime). Standard library.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json


def factors(n: int) -> dict[int, int]:
    result = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            result[d] = result.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def mobius(n: int) -> int:
    fs = factors(n)
    return 0 if any(v > 1 for v in fs.values()) else (-1) ** len(fs)


def conv(a: list[int], b: list[int]) -> list[int]:
    """Literal Dirichlet convolution, with the endpoint n=m included."""
    if len(a) != len(b):
        raise ValueError('Mismatched finite carriers')
    m = len(a) - 1
    c = [0] * (m + 1)
    for d in range(1, m + 1):
        if a[d]:
            for k in range(1, m // d + 1):
                c[d * k] += a[d] * b[k]
    return c


def power(a: list[int], k: int) -> list[int]:
    ans = [0] * len(a)
    ans[1] = 1
    for _ in range(k):
        ans = conv(ans, a)
    return ans


def expansion(m: int, U: int, k: int, *, wrong_sign=False,
              drop_binomial=False, unsigned_mu=False):
    if not 1 <= U <= m or k < 1:
        raise ValueError('Require 1 <= U <= m and k >= 1')
    one = [0] + [1] * m
    unit = [0] * (m + 1)
    unit[1] = 1
    mu = [0] + [mobius(n) for n in range(1, m + 1)]
    u = [0] + [mu[n] if n <= U else 0 for n in range(1, m + 1)]
    if unsigned_mu:
        u = [abs(x) for x in u]
    au = conv(one, u)
    y = [unit[n] - au[n] for n in range(m + 1)]
    total = [0] * (m + 1)
    rows = []
    for j in range(1, k + 1):
        row = conv(power(u, j), power(one, j - 1))
        sign = 1 if wrong_sign else (-1) ** (j - 1)
        coefficient = sign * (1 if drop_binomial else comb(k, j))
        total = [x + coefficient * z for x, z in zip(total, row)]
        rows.append(row)
    return mu, y, power(y, k), total, rows


def log_coordinates(m: int):
    fs = [dict()] + [factors(n) for n in range(1, m + 1)]
    ps = [n for n in range(2, m + 1) if fs[n] == {n: 1}]
    for p in ps:
        ell = [0] + [fs[n].get(p, 0) for n in range(1, m + 1)]
        target = [0] + [int(len(fs[n]) == 1 and p in fs[n])
                        for n in range(1, m + 1)]
        yield p, ell, target


def coefficient_ok(m: int, U: int, k: int, **variant) -> bool:
    mu, y, yk, total, _ = expansion(m, U, k, **variant)
    # For the tested invalid variants, the omitted remainder must be zero
    # under the sufficient strict cutoff. Compare directly with actual Lambda.
    return all(conv(total, ell) == target
               for _, ell, target in log_coordinates(m))


def main():
    configurations = []
    counts = 0
    endpoint_checks = 0
    mixed_checks = 0
    for m, U in [(16, 1), (32, 2), (48, 3), (64, 4),
                 (81, 2), (96, 5), (127, 3), (160, 7), (192, 12)]:
        k = 1
        while (U + 1) ** k <= m:
            k += 1
        mu, y, yk, total, rows = expansion(m, U, k)
        assert all(y[n] == 0 for n in range(1, U + 1))
        assert not any(yk)
        assert total == mu
        for p, ell, target in log_coordinates(m):
            lhs = conv(total, ell)
            assert lhs == target
            endpoint_checks += 1
            assert lhs[m] == target[m]
            # Preserve all four real coordinates of a generic complex
            # Hermitian 2x2 linear test; no actual-P spectral interpretation.
            weights = [lambda n: F((-1) ** n * (n % 5), n + 1),
                       lambda n: F((n % 7) - 3, n + 2),
                       lambda n: F(n, n + 3),
                       lambda n: F((-1) ** n, n + 4)]
            for h in weights:
                assert sum((F(lhs[n]) * h(n) for n in range(1, m + 1)), F()) == \
                       sum((F(target[n]) * h(n) for n in range(1, m + 1)), F())
                mixed_checks += 1
        for n in range(U + 1, m + 1):
            if factors(n) == {n: 1}:
                assert sum((-1) ** (j - 1) * comb(k, j)
                           for j in range(1, k + 1)) == 1
        counts += m
        configurations.append({'m': m, 'U': U, 'k': k,
                               'strict_cutoff': (U + 1) ** k > m})

    # General finite remainder, including invalid support cutoffs.
    general_remainder_configurations = []
    for m, U, k in [(64, 2, 1), (64, 2, 2), (64, 2, 3),
                    (96, 3, 2), (160, 5, 2)]:
        mu, y, yk, total, _ = expansion(m, U, k)
        residual_mu = conv(mu, yk)
        assert [a + b for a, b in zip(total, residual_mu)] == mu
        for _, ell, target in log_coordinates(m):
            residual_lambda = conv(target, yk)
            assert [a + b for a, b in zip(conv(total, ell), residual_lambda)] == target
        general_remainder_configurations.append({'m': m, 'U': U, 'k': k})

    # Explicit rough-prime/rough-product signatures are formal log vectors.
    m, U, k = 125, 2, 5
    _, _, _, _, rows = expansion(m, U, k)
    for p, ell, target in log_coordinates(m):
        if p != 3:
            continue
        for j, row in enumerate(rows, 1):
            coeff = conv(row, ell)
            for a in (1, 2, 3, 4):
                assert coeff[3 ** a] == comb(a + j - 1, j)
        assert conv(expansion(m, U, k)[3], ell)[81] == 1
    m, U, k = 60, 2, 4
    _, _, _, _, rows = expansion(m, U, k)
    for p, ell, _ in log_coordinates(m):
        if p in (3, 5):
            for j, row in enumerate(rows, 1):
                assert conv(row, ell)[15] == j

    planted = {}
    planted['wrong_all_positive_outer_signs'] = not coefficient_ok(64, 2, 4, wrong_sign=True)
    planted['omit_binomial_coefficients'] = not coefficient_ok(64, 2, 4, drop_binomial=True)
    planted['replace_actual_mu_by_absolute_value'] = not coefficient_ok(64, 2, 4, unsigned_mu=True)
    planted['drop_nonzero_remainder'] = not coefficient_ok(64, 2, 3)
    # At n=54=2*3^3 the discarded Lambda*y^3 coefficient of log(2) is -1.
    _, _, yk, total, _ = expansion(64, 2, 3)
    ell2 = next(ell for p, ell, _ in log_coordinates(64) if p == 2)
    lam2 = next(target for p, _, target in log_coordinates(64) if p == 2)
    assert conv(lam2, yk)[54] == -1
    planted['erase_prime_power_coefficient'] = (conv(total, ell2)[4] != 0)
    # Endpoint test: multiplication by the original zero h(m) is distinct
    # from a nonlocal smoothing map. This is an exact generic algebra control.
    h = [F(0), F(2), F(0)]
    smoothing = [[F(1), F(1, 3), F(1, 5)],
                 [F(1, 3), F(1), F(1, 3)],
                 [F(1, 5), F(1, 3), F(1)]]
    top = sum((smoothing[2][j] * h[j] for j in range(3)), F())
    assert top == F(2, 3)
    planted['delete_smoothed_top_from_raw_zero'] = (top != h[2])
    assert all(planted.values())

    result = {
        'status': 'LOCAL_EXACT_CONTROLS_ONLY',
        'actual_lambda_coefficient_configurations': configurations,
        'integer_indices_in_these_configurations': counts,
        'formal_log_endpoint_coordinates': endpoint_checks,
        'generic_hermitian_linear_coordinate_checks': mixed_checks,
        'explicit_remainder_configurations': general_remainder_configurations,
        'rough_prime_and_product_signatures': 'passed',
        'planted_failures_detected': planted,
        'planted_failure_count': len(planted),
        'production_CCM_spectra': False,
        'new_signed_inequality_verified': False,
        'historical_scripts_executed': False
    }
    text = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + '\n'
    Path('q41_math_results.json').write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
