#!/usr/bin/env python3
"""Numerical candidate search with an independent exact certificate."""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

import scipy
from scipy.optimize import linprog
import sympy as sp


CONTRACT = {
    "family": "even_quartic",
    "domain": ["-1", "1"],
    "target": "1/(1+x^2)",
    "contacts": {"0": "1", "-1": "1/2", "1": "1/2"},
    "objective": "integral_-1^1_p",
}
INCUMBENT = Fraction(8, 5)


def _q(value: Fraction | int | str) -> Fraction:
    """Accept exact rational inputs only; floats must pass reconstruction first."""
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        return Fraction(value)
    raise TypeError("exact rational input required")


def _s(value: Fraction) -> str:
    return str(value)


def _sym(value: Fraction) -> sp.Rational:
    return sp.Rational(value.numerator, value.denominator)


def _objective(a: Fraction, b: Fraction, c: Fraction) -> Fraction:
    return 2 * a + Fraction(2, 3) * b + Fraction(2, 5) * c


def _gap(a: Fraction, b: Fraction, c: Fraction, x: Fraction) -> Fraction:
    t = x * x
    return a + b * t + c * t * t - Fraction(1, 1) / (1 + t)


def _witness_x(c: Fraction) -> Fraction:
    """Find rational x in (0,1) where a contact-constrained c>1/4 fails."""
    margin = 2 * c - Fraction(1, 2)
    if margin <= 0:
        raise ValueError("no strict violation when c <= 1/4")
    n = (2 * c // margin) + 1
    n = max(int(n), 2)
    return Fraction(n - 1, n)


def verify_coefficients(
    a: Fraction | int | str,
    b: Fraction | int | str,
    c: Fraction | int | str,
    *,
    counterexample_x: Fraction | int | str | None = None,
) -> dict:
    """Check contacts and the majorant claim using exact rational arithmetic."""
    a, b, c = _q(a), _q(b), _q(c)
    contacts = {
        "p(0)": _s(a),
        "p(-1)": _s(a + b + c),
        "p(1)": _s(a + b + c),
        "valid": a == 1 and a + b + c == Fraction(1, 2),
    }
    result = {
        "status": "REFUTED" if not contacts["valid"] else "VERIFIED",
        "shape": "even_quartic",
        "contacts": contacts,
        "upper_bound": None,
        "objective": _s(_objective(a, b, c)),
        "optimality": {"status": "NOT_ESTABLISHED", "candidate_is_optimal": False},
    }
    if not contacts["valid"]:
        result["reason"] = "required contacts do not hold"
        return result

    t = sp.symbols("t")
    gap = _sym(a) + _sym(b) * t + _sym(c) * t**2 - 1 / (1 + t)
    factor = t * (1 - t) * (sp.Rational(1, 2) - _sym(c) - _sym(c) * t) / (1 + t)
    factor_identity = sp.factor(gap - factor) == 0
    bernstein = (Fraction(1, 2) - c, Fraction(1, 2) - 2 * c)
    feasible = factor_identity and all(coefficient >= 0 for coefficient in bernstein)
    result.update({
        "factorization": "p-1/(1+x^2)=t(1-t)(1/2-c-c*t)/(1+t), t=x^2",
        "factorization_verified": factor_identity,
        "bernstein_coefficients": [_s(value) for value in bernstein],
        "upper_bound": feasible,
    })
    if not feasible:
        x = _q(counterexample_x) if counterexample_x is not None else _witness_x(c)
        violation = _gap(a, b, c, x)
        if not 0 <= x < 1 or violation >= 0:
            raise ValueError("counterexample does not refute the majorant claim")
        result["status"] = "REFUTED"
        result["counterexample"] = {"x": _s(x), "gap_p_minus_target": _s(violation)}
        return result

    objective = _objective(a, b, c)
    identity_lhs = objective - INCUMBENT
    identity_rhs = (1 - 4 * c) / 15
    identity_verified = identity_lhs == identity_rhs
    result["optimality"] = {
        "status": "VERIFIED" if identity_verified else "REFUTED",
        "objective_lower_bound": _s(INCUMBENT),
        "identity": "integral(p)-8/5=(1-4*c)/15",
        "identity_value": _s(identity_lhs),
        "identity_verified": identity_verified,
        "candidate_is_optimal": identity_verified and objective == INCUMBENT,
    }
    if not identity_verified:
        result["status"] = "REFUTED"
    return result


def certify_family(
    lower: Fraction | int | str,
    upper: Fraction | int | str,
    *,
    name: str,
    counterexample_x: Fraction | int | str | None = None,
) -> dict:
    """Certify a whole contact-constrained c interval or leave it unresolved."""
    lower, upper = _q(lower), _q(upper)
    if lower > upper:
        raise ValueError("family lower endpoint exceeds upper endpoint")
    item = {"name": name, "parameter": "c", "lower": _s(lower), "upper": _s(upper)}
    if lower > Fraction(1, 4):
        x = _q(counterexample_x) if counterexample_x is not None else _witness_x(lower)
        gap_at_lower = _gap(Fraction(1), -Fraction(1, 2) - lower, lower, x)
        slope = -(x * x) * (1 - x * x)
        if gap_at_lower < 0 and slope <= 0:
            item.update({
                "status": "INFEASIBLE",
                "certificate": {
                    "uniform_x": _s(x),
                    "gap_at_lower": _s(gap_at_lower),
                    "gap_slope_in_c": _s(slope),
                    "argument": "gap(c,x)=gap(lower,x)+(c-lower)*slope",
                },
            })
            return item
    if upper <= Fraction(1, 4):
        bernstein_at_upper = (Fraction(1, 2) - upper, Fraction(1, 2) - 2 * upper)
        objective_lower = Fraction(5, 3) - Fraction(4, 15) * upper
        if all(x >= 0 for x in bernstein_at_upper) and objective_lower > INCUMBENT:
            item.update({
                "status": "CANNOT_IMPROVE",
                "certificate": {
                    "bernstein_coefficients_at_upper": [_s(x) for x in bernstein_at_upper],
                    "objective_slope": "-4/15",
                    "objective_lower_bound": _s(objective_lower),
                    "incumbent_objective": _s(INCUMBENT),
                    "strictly_above_incumbent": True,
                },
            })
            return item
    item.update({"status": "UNRESOLVED", "certificate": {"reason": "interval not discharged by exact family rules"}})
    return item


def _rationalize(value: float, *, max_denominator: int = 100_000) -> Fraction:
    candidate = Fraction(str(float(value))).limit_denominator(max_denominator)
    if abs(float(candidate) - float(value)) > 1e-9:
        raise ValueError(f"numeric value {value!r} did not reconstruct rationally")
    return candidate


def solve_numerical_proposal() -> dict:
    """Use LP only to propose coefficients; no solver status is a certificate."""
    result = linprog(
        c=[2.0, 2.0 / 3.0, 2.0 / 5.0],
        A_ub=[[0.0, 0.0, 1.0], [0.0, 0.0, 2.0]],
        b_ub=[0.5, 0.5],
        A_eq=[[1.0, 0.0, 0.0], [1.0, 1.0, 1.0]],
        b_eq=[1.0, 0.5],
        bounds=[(None, None)] * 3,
        method="highs",
    )
    proposal = {
        "solver": "scipy.optimize.linprog",
        "success": bool(result.success),
        "message": str(result.message),
        "coefficients_float": None,
        "objective_float": None,
        "role": "candidate generation only; not a certificate",
    }
    if result.success:
        proposal["coefficients_float"] = {k: float(v) for k, v in zip(("a", "b", "c"), result.x)}
        proposal["objective_float"] = float(result.fun)
    return proposal


def build_report() -> dict:
    proposal = solve_numerical_proposal()
    candidate: dict
    if proposal["success"]:
        try:
            coeff = {key: _rationalize(value) for key, value in proposal["coefficients_float"].items()}
        except (ValueError, OverflowError) as exc:
            candidate = {
                "coefficients": None,
                "verification": {"status": "UNKNOWN", "reason": str(exc)},
            }
        else:
            candidate = {
                "coefficients": {key: _s(value) for key, value in coeff.items()},
                "verification": verify_coefficients(**coeff),
            }
    else:
        candidate = {
            "coefficients": None,
            "verification": {"status": "UNKNOWN", "reason": "LP produced no numerical candidate"},
        }

    bad_coeff = {"a": Fraction(1), "b": Fraction(-19, 25), "c": Fraction(13, 50)}
    bad = {
        "coefficients": {key: _s(value) for key, value in bad_coeff.items()},
        "verification": verify_coefficients(**bad_coeff, counterexample_x=Fraction(49, 50)),
    }
    families = [
        certify_family(Fraction(13, 50), Fraction(1, 2), name="high_c_infeasible", counterexample_x=Fraction(49, 50)),
        certify_family(0, Fraction(1, 5), name="low_c_cannot_improve"),
    ]
    return {
        "contract": CONTRACT,
        "numerical_proposal": proposal,
        "candidate": candidate,
        "bad_candidate": bad,
        "families": families,
        "runtime": {"python": sys.version.split()[0], "scipy": scipy.__version__, "sympy": sp.__version__},
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="create JSON report at this path (must not exist)")
    args = parser.parse_args(argv)
    payload = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.output is None:
        sys.stdout.write(payload)
    else:
        try:
            with args.output.open("x", encoding="utf-8") as stream:
                stream.write(payload)
        except FileExistsError:
            parser.error(f"refusing to overwrite existing output: {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
