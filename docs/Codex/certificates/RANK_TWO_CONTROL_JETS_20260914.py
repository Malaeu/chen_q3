#!/usr/bin/env python3
"""Exact rational audit of the NON-THETA control f0=e^-u^2-(1/4)e^-2u^2.
No quadrature, floating-point arithmetic, theta sampling, or RH claim.
"""
from fractions import Fraction as F
from math import factorial
import json


def add(p, q):
    out = dict(p)
    for k, v in q.items():
        out[k] = out.get(k, F(0)) + v
    return {k: v for k, v in out.items() if v}


def scale(p, v, shift=0):
    return {k + shift: v * a for k, a in p.items() if v * a}


def mul(p, q):
    out = {}
    for k, a in p.items():
        for j, b in q.items():
            out[k + j] = out.get(k + j, F(0)) + a * b
    return {k: v for k, v in out.items() if v}


def derivative_gaussian(p, rate):
    derivative = {k - 1: k * a for k, a in p.items() if k}
    return add(derivative, scale(p, -2 * rate, shift=1))


def jet_polynomials(rate):
    p = {0: F(1)}
    out = [p]
    for _ in range(3):
        p = derivative_gaussian(p, rate)
        out.append(p)
    return out


def integrate_odd_polynomial(p, rate):
    result = F(0)
    for power, coefficient in p.items():
        assert power % 2 == 1, (power, coefficient)
        k = (power - 1) // 2
        result += coefficient * F(factorial(k), 2 * rate ** (k + 1))
    return result


TERMS = [(F(1), F(1)), (F(2), F(-1, 4))]
JETS = {rate: jet_polynomials(rate) for rate, _ in TERMS}


def entry(m, n):
    result = F(0)
    for a, ca in TERMS:
        for b, cb in TERMS:
            pm, pn = JETS[a][m], JETS[b][n]
            p = scale(mul(pm, pn), F(2), shift=1)
            p = add(p, scale(mul(JETS[a][m - 1], pn), F(m)))
            p = add(p, scale(mul(pm, JETS[b][n - 1]), F(n)))
            result += ca * cb * integrate_odd_polynomial(p, a + b)
    return result


j11, j13, j31, j33 = (entry(m, n) for m, n in [(1, 1), (1, 3), (3, 1), (3, 3)])
assert (j11, j13, j31, j33) == (F(1, 18), F(-25, 54), F(-25, 54), F(100, 27))
det = j11 * j33 - j13 * j31
energy = F(25, 3) ** 2 * j11 + 2 * F(25, 3) * j13 + j33
assert det == F(-25, 2916)
assert energy == F(-25, 162)

nodes = [-1, -2, -3, -4]
d3 = [1, -3, 3, -1]
d1 = [F(25, 3), F(-25, 3), 0, 0]
mom3 = [sum(F(a * x ** k, factorial(k)) for a, x in zip(d3, nodes)) for k in range(4)]
mom1 = [sum(a * F(x ** k, factorial(k)) for a, x in zip(d1, nodes)) for k in range(2)]
assert mom3 == [F(0), F(0), F(0), F(1)]
assert mom1 == [F(0), F(25, 3)]

print(json.dumps({
    "scope": "EXACT_RATIONAL_NON_THETA_CONTROL_ONLY",
    "matrix": [[str(j11), str(j13)], [str(j31), str(j33)]],
    "determinant": str(det),
    "coefficient_vector": ["25/3", "1"],
    "jet_energy": str(energy),
    "third_difference_Taylor_moments_0_to_3": list(map(str, mom3)),
    "first_difference_Taylor_moments_0_to_1": list(map(str, mom1)),
    "finite_h_explicitly_certified": False,
    "actual_theta_negative_witness": False
}, indent=2))
