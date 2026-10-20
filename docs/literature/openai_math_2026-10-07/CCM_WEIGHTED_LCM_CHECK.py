#!/usr/bin/env python3
"""Finite diagnostics for W1; the universal proof is in the companion note.
Fractions certify coefficient/mean identities; floats only illustrate bounds.
"""
from fractions import Fraction as F
from math import gcd, lcm, log, sqrt
import json


def arithmetic(n):
    left, phi, mu, tau = n, n, 1, 1
    p = 2
    while p * p <= left:
        if left % p == 0:
            exponent = 0
            while left % p == 0:
                left //= p
                exponent += 1
            phi -= phi // p
            mu = 0 if exponent > 1 else -mu
            tau *= exponent + 1
        p += 1
    if left > 1:
        phi -= phi // left
        mu = -mu
        tau *= 2
    return mu, phi, tau


def check(R):
    data = {n: arithmetic(n) for n in range(1, R + 1)}
    C = sum((F(mu * mu, phi) for mu, phi, _ in data.values()), F(0))
    u = {}
    for d, (mu, phi, tau) in data.items():
        inner = sum((F(data[k][0] ** 2, data[k][1])
                     for k in range(1, R // d + 1) if gcd(k, d) == 1), F(0))
        u[d] = F(mu * d, phi) * inner / C
        assert abs(u[d]) <= tau
    g = {}
    for d in u:
        for e in u:
            ell = lcm(d, e)
            g[ell] = g.get(ell, F(0)) + u[d] * u[e]
    mean = sum((weight / ell for ell, weight in g.items()), F(0))
    assert mean == 1 / C
    for n in range(1, 2 * R + 2):
        lhs = sum((u[d] for d in u if n % d == 0), F(0)) ** 2
        rhs = sum((weight for ell, weight in g.items() if n % ell == 0), F(0))
        assert lhs == rhs
    diagonal_only_mean = sum((u[d] ** 2 / d for d in u), F(0))
    assert diagonal_only_mean != mean  # dropping mixed d,e fails source identity
    weighted = sum(float(abs(weight)) / sqrt(ell) for ell, weight in g.items())
    rhs = 324 * R * (1 + log(R)) ** 2
    assert weighted <= rhs
    return {'R': R, 'C_R_exact': str(C), 'coefficient_mean_identity': True,
            'divisor_square_checks': 2 * R + 1, 'mixed_terms_negative_control': 'REJECTED',
            'weighted_l1_float_diagnostic': weighted, 'W1_bound_float': rhs,
            'ratio_float': weighted / rhs}


if __name__ == '__main__':
    print(json.dumps({'boundary': 'FINITE_DIAGNOSTIC_NOT_UNIVERSAL_PROOF',
                      'rows': [check(R) for R in (2, 4, 8, 16, 32, 64, 128)]}, indent=2))
