#!/usr/bin/env python3
"""Exact algebraic controls; not a Lean gate or a certificate for project W.

Run from the repository root:
  uv run --no-project --with sympy==1.14.0 python \
    docs/routeB_bus/proshka/ccm_directional_resolvent_2026-09-20/exact_checks.py
No floating-point eigenvalue tests are used. Failed checks exit nonzero.
"""
from __future__ import annotations

import sympy as s


def require(condition: object, name: str) -> None:
    if condition is not True and condition != s.true:
        raise AssertionError(f"FAIL {name}: {condition!r}")
    print(f"PASS {name}")


def zero(value: s.Expr) -> bool:
    return s.simplify(value) == 0


def zero_matrix(value: s.MatrixBase) -> bool:
    return all(zero(entry) for entry in value)


def norm2(vector: s.MatrixBase) -> s.Expr:
    return s.simplify((vector.H * vector)[0])


def main() -> None:
    print(f"SYMPY {s.__version__}; EXACT_ARITHMETIC; NOT_LEAN; NOT_PROJECT_C")
    # Construct a rational complex control with an exact secular root.
    B = s.Matrix([[3, 1 + s.I], [1 - s.I, 4]])
    u = s.Matrix([s.Rational(1, 5), (1 + s.I) / 7])
    delta = s.simplify((u.H * B * u)[0] / (1 - norm2(u)))
    require(delta.is_positive is True, "P1_positive_secular_root")
    r = (B + delta * s.eye(2)) * u
    A = s.zeros(1).row_join(r.H).col_join(r.row_join(B))
    xi_raw = s.Matrix([1, -u[0], -u[1]])
    require(zero(delta - (r.H * u)[0]) and
            zero_matrix((A + delta * s.eye(3)) * xi_raw),
            "P1_secular_and_eigenvector")
    ar, ai, yr, yi, zr, zi = s.symbols("ar ai yr yi zr zi", real=True)
    alpha = ar + s.I * ai
    y = s.Matrix([yr + s.I * yi, zr + s.I * zi])
    x = s.Matrix([alpha, y[0], y[1]])
    z = y + alpha * u
    identity = (x.H * (A + delta * s.eye(3)) * x)[0] - (
        z.H * (B + delta * s.eye(2)) * z)[0]
    require(zero(s.expand(identity)), "P1_complex_completion_identity")
    eta2 = norm2(B.inv() * r)
    require(s.simplify(eta2 - norm2(u)).is_nonnegative is True,
            "P1_directional_bound_control")
    wrong = s.Matrix([1, u[0], u[1]])
    require(not zero_matrix((A + delta * s.eye(3)) * wrong),
            "P2_wrong_eigenvector_sign_rejected")

    # Losing the off-diagonal coupling gives a false positive.
    bad = s.Matrix([[1, 2], [2, 1]])
    witness = s.Matrix([1, -2])
    require((witness.T * bad * witness)[0] == -3,
            "P2_omitted_Schur_coupling_rejected_U_minus_3")

    eps = s.symbols("eps", positive=True)
    W = s.Matrix([[0, 0, eps], [0, eps**3, 0], [eps, 0, 1]])
    de = (s.sqrt(1 + 4 * eps**2) - 1) / 2
    xe = s.Matrix([1, 0, -eps / (1 + de)])
    require(zero_matrix((W + de * s.eye(3)) * xe) and
            zero(de * (1 + de) - eps**2), "P3_epsilon_exact_ground_equation")
    Be = s.diag(eps**3, 1)
    re = s.Matrix([0, eps])
    require(zero(norm2(Be.inv() * re) - eps**2) and
            s.limit(eps**(-2), eps, 0, dir="+") == s.oo and
            s.limit(eps, eps, 0, dir="+") == 0,
            "P3_directional_convergence_despite_worst_gap_divergence")

    # Symbolic Hermitian 2-block identity, including conjugation.
    a = s.symbols("a", real=True)
    d = s.symbols("d", positive=True)
    cr, ci, hr, hi, tr, ti = s.symbols("cr ci hr hi tr ti", real=True)
    c, h, t = cr + s.I * ci, hr + s.I * hi, tr + s.I * ti
    Bh = s.Matrix([[a, c], [s.conjugate(c), d]])
    vht = s.Matrix([h, t])
    sh = a - s.conjugate(c) * c / d
    shifted = t + s.conjugate(c) * h / d
    rhs = d * s.conjugate(shifted) * shifted + sh * s.conjugate(h) * h
    require(zero(s.expand((vht.H * Bh * vht)[0] - rhs)),
            "P4_symbolic_complex_Schur_identity")
    Bc = s.Matrix([[2, 1 + s.I], [1 - s.I, 3]])
    lower_s, lower_d, k = s.Integer(1), s.Integer(3), s.Rational(1, 2)
    floor = min(lower_s, lower_d) / (1 + k)**2
    shifted_B = Bc - floor * s.eye(2)
    require(shifted_B[0, 0] > 0 and shifted_B.det() > 0 and
            k**2 >= s.Rational(2, 9), "P4_rational_lower_floor_G_4_over_9")
    rc = s.Matrix([1 + s.I, 2 - s.I])
    q = rc[1] / 3
    p = rc[0] - (1 + s.I) * q
    Hbound = s.sqrt(s.simplify(s.conjugate(p) * p)) / lower_s
    Qnorm = s.sqrt(s.simplify(s.conjugate(q) * q))
    E2 = s.simplify(Hbound**2 + (Qnorm + k * Hbound)**2)
    require(s.simplify(E2 - norm2(Bc.inv() * rc)).is_nonnegative is True,
            "P4_directional_block_budget_control")

    W0, v0 = s.diag(0, 1), s.Matrix([0, 1])
    J = s.diag(-1, 1)
    ground0 = s.Matrix([1, 0])
    require(zero_matrix((W0 - s.eye(2)) * v0) and
            zero_matrix(J * v0 - v0) and
            zero_matrix(J * ground0 + ground0) and W0[0, 0] < W0[1, 1],
            "P5_zero_residual_does_not_select_ground_or_evenness")
    Wshift = s.diag(2, 1, 1)
    require(Wshift[1:, 1:] == s.eye(2) and Wshift.eigenvals()[s.Integer(1)] == 2,
            "P5_arbitrary_shift_positive_compression_not_simplicity")
    print("ALL_CHECKS_PASSED; PROJECT_C_REMAINS_OPEN; LEAN_NOT_RUN")


if __name__ == "__main__":
    main()
