#!/usr/bin/env python3
"""Exact controls for a PAPER counterexample, not a Lean or cofinal certificate.

Run from the repository root:
uv run --no-project --with sympy==1.14.0 python \
  docs/routeB_bus/proshka/ccm_source_contract_counterexample_2026-09-20/exact_checks.py

There are no placeholders in that command. The universal analysis and the
source-contract realization are proved in VERDICT.md, not by a finite sweep.
"""
from __future__ import annotations

from fractions import Fraction
from math import isqrt
import sympy as sp

COUNT = 0


def check(name: str, condition: object) -> None:
    global COUNT
    if not bool(condition):
        raise AssertionError(name)
    COUNT += 1
    print(f"PASS {name}")


def main() -> None:
    print(f"SYMPY {sp.__version__}; EXACT_ARITHMETIC; PAPER_CONTROLS; NOT_LEAN")
    a, b, c, d = sp.symbols("a b c d", real=True)
    K = sp.Matrix([[a, b, c], [b, d, b], [c, b, a]])
    q = sp.Matrix([sp.Rational(1, 2), 1 / sp.sqrt(2), sp.Rational(1, 2)])
    y = sp.Matrix([-sp.Rational(1, 2), 1 / sp.sqrt(2), -sp.Rational(1, 2)])
    J = sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    check("unit_rows_and_orthogonality", (q.dot(q), y.dot(y), q.dot(y)) == (1, 1, 0))
    check("real_even_rows", J * q == q and J * y == y)
    Q = sp.eye(3) - q * q.T
    check("complement_fixes_witness", sp.simplify(Q * y - y) == sp.zeros(3, 1))
    rayleigh = sp.expand((q.T * K * q)[0])
    shifted = sp.simplify((y.T * (K - rayleigh * sp.eye(3)) * y)[0])
    check("negative_energy_identity", sp.simplify(shifted + 2 * sp.sqrt(2) * b) == 0)
    block = Q * (K - rayleigh * sp.eye(3)) * Q
    check("literal_compressed_energy", sp.simplify((y.T * block * y)[0] - shifted) == 0)
    swapped = sp.simplify((q.T * (K - (y.T * K * y)[0] * sp.eye(3)) * q)[0])
    check("planted_trial_swap_reverses_sign", sp.simplify(swapped - 2 * sp.sqrt(2) * b) == 0)
    check("planted_nonorthogonal_witness_rejected", q.dot(q) != 0)

    L, x = sp.symbols("L x", positive=True)
    Q01 = -sp.sin(2 * sp.pi * x / L) / sp.pi
    check("offdiagonal_endpoint_and_prime_zero", Q01.subs(x, 0) == 0 and sp.simplify(Q01.subs(x, L)) == 0)
    W02_raw = 32 * L * sp.sinh(L / 4)**2 * L**2 / ((L**2 + 16 * sp.pi**2) * L**2)
    W02 = 32 * L * sp.sinh(L / 4)**2 / (L**2 + 16 * sp.pi**2)
    check("literal_W02_offdiagonal", sp.simplify(W02_raw - W02) == 0)
    w = sp.exp(x / 2) / (sp.exp(x) - sp.exp(-x))
    derivative = -sp.exp(x / 2) * (sp.exp(x) + 3 * sp.exp(-x)) / (2 * (sp.exp(x) - sp.exp(-x))**2)
    check("decreasing_weight_derivative", sp.simplify(sp.diff(w, x) - derivative) == 0)
    check("sine_reflection", sp.simplify(sp.sin(2 * sp.pi * (L - x) / L) + sp.sin(2 * sp.pi * x / L)) == 0)
    check("removable_integral_endpoint", sp.limit(w * sp.sin(2 * sp.pi * x / L), x, 0, dir='+') == sp.pi / L)
    # Analytic premises proved in VERDICT.md: 2/3 < log(2) < 1,
    # pi < 4, sinh(t) >= t, and the paired sine integral is positive.
    lower_W02 = Fraction(2) * Fraction(2, 3)**3 / (1 + 16 * 4**2)
    upper_energy = -2 * lower_W02  # sqrt(2) > 1 only weakens the upper bound.
    check("rational_upper_envelope_negative", lower_W02 == Fraction(16, 6939) and upper_energy == Fraction(-32, 6939) and upper_energy < 0)

    # Small exact controls of the divisor identity; its general proof is
    # the product over distinct primes in VERDICT.md.
    for n in range(1, 65):
        s = sum(sp.mobius(k) for k in sp.divisors(n))
        if s != (1 if n == 1 else 0):
            raise AssertionError(f"divisor control failed at {n}")
    check("Mobius_divisor_controls_1_to_64", True)
    check("planted_unsigned_Mobius_rejected", sum(abs(sp.mobius(k)) for k in sp.divisors(2)) != 0)
    values = {n: sp.Rational(n * n + 1, n + 2) for n in range(1, 25)}
    lhs = sum(sp.mobius(n) * values[n * k] for k in values for n in values if n * k in values)
    check("finite_summation_inversion_control", lhs == values[1])

    # Exact coefficients after projection and positive normalization.
    check("N0_projection_nonzero", q[1] > 0)
    central = sp.sqrt(L) / sp.sqrt(2)
    check("P59_central_value_nonzero", sp.simplify((L / sp.sqrt(L)) * q[1] - central) == 0 and central.is_positive)
    # The constant h4 allowed by ProlatePair is not an eigenfunction of
    # the differential expression on the interior: its ratio is 4*pi^2*l^2*x^2.
    lam = sp.symbols("lam", positive=True)
    h4 = 1 / sp.sqrt(2 * lam)
    action_h4 = -sp.diff((lam**2 - x**2) * sp.diff(h4, x), x) + (2 * sp.pi * lam * x)**2 * h4
    check("constant_h4_is_not_a_differential_eigenmode", sp.simplify(action_h4 / h4 - 4 * sp.pi**2 * lam**2 * x**2) == 0 and sp.diff(action_h4 / h4, x) != 0)
    check("constant_h4_center_integral_contract", sp.simplify((2 * lam) * h4 - sp.sqrt(2 * lam)) == 0)
    print(f"CHECK_GROUPS {COUNT}")
    print("ALL_CHECKS_PASSED; UNIVERSAL_TYPE_ONLY_FLOOR_REFUTED_ON_PAPER; SELECTED_SPECTRAL_C_OPEN; LEAN_NOT_RUN")


if __name__ == "__main__":
    main()
