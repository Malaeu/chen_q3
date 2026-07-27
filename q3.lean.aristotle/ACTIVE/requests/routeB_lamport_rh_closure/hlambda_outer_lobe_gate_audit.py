#!/usr/bin/env python3
"""Outward-rounded scalar certificate for Route-B goal 027.

This consumes the exact Theta brackets and live recessive-tail budgets from
goal 026.  It evaluates only the requested point t = 1/sqrt(m); no sign grid
or truncated-mode-as-exact substitution is used.
"""

from __future__ import annotations

import csv
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import arb, ctx


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
GOAL = HERE / "027_hlambda_outer_lobe_gate.goal.md"
ANSWER_026 = HERE / "026_lambda_bracket_resume.answer.md"
AUDIT_026 = HERE / "LAMBDA_BRACKET_RESUME_AUDIT.json"
CERT_026_SCRIPT = HERE / "lambda_bracket_resume_audit.py"
PEN = HERE / "proshka" / "PROSHKA_PEN_REDUCTIONS_2026-07-27.md"
SCRIPT = Path(__file__).resolve()
OUT_JSON = HERE / "HLAMBDA_OUTER_LOBE_GATE_AUDIT.json"
OUT_CSV = HERE / "HLAMBDA_OUTER_LOBE_GATE_AUDIT.csv"

sys.path.insert(0, str(HERE))
import lambda_bracket_resume_audit as cert026  # noqa: E402


class GateGap(RuntimeError):
    def __init__(self, code: str, detail: str):
        super().__init__(detail)
        self.code = code


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ball_text(x: arb, digits: int = 70) -> str:
    return x.str(max(64, int(digits * 3.5)))


def theta_ball(case: dict[str, Any]) -> arb:
    bracket = case["Theta_bracket"]
    lo = Fraction(
        int(bracket["lower_exact"]["numerator"]),
        int(bracket["lower_exact"]["denominator"]),
    )
    hi = Fraction(
        int(bracket["upper_exact"]["numerator"]),
        int(bracket["upper_exact"]["denominator"]),
    )
    return cert026.arb_hull(lo, hi)


def raw_coefficients(case: dict[str, Any]) -> list[tuple[int, arb]]:
    """Rebuild the a_0=1 core from the certified Theta interval."""

    m = int(case["m"])
    ctx.dps = cert026.WORKING_DPS[m]
    G = (2 * arb.pi() * m) ** 2
    theta = theta_ball(case)
    previous = arb(0)
    current = arb(1)
    coefficients: list[tuple[int, arb]] = []
    for degree in range(0, int(case["N0"]) + 1, 2):
        coefficients.append((degree, current))
        following = (
            cert026.d_coeff(degree, G, theta) * current
            - cert026.p_coeff(degree, G) * previous
        ) / cert026.r_coeff(degree, G)
        previous, current = current, following
    return coefficients


def legendre(n: int, x: arb) -> arb:
    if n == 0:
        return arb(1)
    p_previous = arb(1)
    p_current = x
    for k in range(1, n):
        p_previous, p_current = (
            p_current,
            ((2 * k + 1) * x * p_current - k * p_previous) / (k + 1),
        )
    return p_current


def raw_core_value(
    case: dict[str, Any], coefficients: list[tuple[int, arb]], t: arb
) -> arb:
    target_degree = int(case["target_degree"])
    value = arb(0)
    for degree, coefficient in coefficients:
        k = (degree - target_degree) // 2
        phase = -1 if k % 2 else 1
        value += phase * coefficient * legendre(degree, t)
    return value


def normalization_data(
    case: dict[str, Any], coefficients: list[tuple[int, arb]]
) -> dict[str, arb]:
    """Repeat the live 026 finite-plus-tail L2 normalization enclosure."""

    finite_l2_sq = arb(0)
    for degree, coefficient in coefficients:
        finite_l2_sq += 2 * coefficient**2 / arb(2 * degree + 1)
    last = coefficients[-1][1]
    tail_l2_sq_upper = (
        2 * last**2 / arb(3 * (2 * int(case["N0"]) + 5))
    )
    tail_l2_sq = arb(0).union(tail_l2_sq_upper)
    scale = 1 / (finite_l2_sq + tail_l2_sq).sqrt()
    if not scale > 0:
        raise GateGap(
            "HLAMBDA_OUTER_POINT_DETERMINANT_GAP",
            f"m={case['m']}, degree={case['target_degree']}: "
            "normalizing scale does not exclude zero",
        )
    return {
        "scale": scale,
        "J": 2 * scale,
        "epsilon": abs(scale * last),
        "tail_l2_sq": tail_l2_sq,
    }


def run_cell(
    m: int, degree0: dict[str, Any], degree4: dict[str, Any]
) -> dict[str, Any]:
    ctx.dps = cert026.WORKING_DPS[m]
    t = arb(1) / arb(m).sqrt()
    coeff0 = raw_coefficients(degree0)
    coeff4 = raw_coefficients(degree4)
    phi0 = raw_core_value(degree0, coeff0, t)
    phi4 = raw_core_value(degree4, coeff4, t)
    norm0 = normalization_data(degree0, coeff0)
    norm4 = normalization_data(degree4, coeff4)

    # With a_0=1, every other Legendre term has positive degree and integral
    # zero on [-1,1].  Hence the physical source integral is J_j=2*s_j>0.
    # The common positive scale cancels algebraically in phi_{j,K}/J_j.
    # On the requested right-hand side, retain independent outward enclosures
    # for eps_j and J_j, so interval division consumes eps_upper/J_lower.
    j0 = norm0["J"]
    j4 = norm4["J"]
    if not j0 > 0 or not j4 > 0:
        raise GateGap(
            "HLAMBDA_OUTER_POINT_DETERMINANT_GAP",
            f"m={m}: a source integral does not exclude zero",
        )
    psi = phi4 / 2 - phi0 / 2
    eps0_over_j0 = norm0["epsilon"] / j0
    eps4_over_j4 = norm4["epsilon"] / j4
    tail_allowance = eps4_over_j4 + eps0_over_j0
    point_margin = psi - tail_allowance
    if not point_margin > 0:
        raise GateGap(
            "HLAMBDA_OUTER_POINT_DETERMINANT_GAP",
            f"m={m}: point margin does not exclude zero: {ball_text(point_margin)}",
        )

    theta4 = theta_ball(degree4)
    barrier = theta4 - cert026.rational(17, 4) * arb.pi() ** 2 * m
    if not barrier > 0:
        raise GateGap(
            "HLAMBDA_EIGENVALUE_BARRIER_GAP",
            f"m={m}: eigenvalue barrier does not exclude zero: {ball_text(barrier)}",
        )

    return {
        "m": m,
        "lambda": f"sqrt({m})",
        "t": f"1/sqrt({m})",
        "theta4_barrier_margin": ball_text(barrier),
        "positive_source_integrals": {
            "J0": ball_text(j0),
            "J4": ball_text(j4),
            "raw_gauge_J0": "2",
            "raw_gauge_J4": "2",
            "proof": (
                "J_j=2*s_j>0: a0=1; every remaining even Legendre "
                "polynomial has positive degree and integral zero"
            ),
        },
        "finite_core": {
            "raw_phi0_at_t": ball_text(phi0),
            "raw_phi4_at_t": ball_text(phi4),
            "normalized_phi0_at_t": ball_text(norm0["scale"] * phi0),
            "normalized_phi4_at_t": ball_text(norm4["scale"] * phi4),
            "Psi_at_t": ball_text(psi),
            "scale_cancellation": (
                "(s_j*raw_phi_j)/(2*s_j)=raw_phi_j/2, with s_j>0"
            ),
        },
        "tails": {
            "eps0": ball_text(norm0["epsilon"]),
            "eps4": ball_text(norm4["epsilon"]),
            "eps0_over_J0": ball_text(eps0_over_j0),
            "eps4_over_J4": ball_text(eps4_over_j4),
            "consumed_allowance": ball_text(tail_allowance),
            "consumed_in_strict_inequality": bool(
                tail_allowance > 0 and point_margin < psi
            ),
        },
        "strict_point_margin": ball_text(point_margin),
        "paper_transport_instantiation": {
            "open_interval": "h_lambda(x)<0 for 1<=x<lambda",
            "midpoint": (
                "x=lambda is handled separately by the locked midpoint "
                "zero-extension; halving the interior endpoint value "
                "preserves the nonpositive sign"
            ),
            "closed_interval": "h_lambda(x)<=0 for 1<=x<=lambda",
        },
    }


def main() -> None:
    required = (
        GOAL,
        ANSWER_026,
        AUDIT_026,
        CERT_026_SCRIPT,
        PEN,
        SCRIPT,
    )
    for path in required:
        if not path.is_file():
            raise SystemExit(f"missing source: {path}")

    audit026 = json.loads(AUDIT_026.read_text())
    by_cell = {
        (int(case["m"]), int(case["target_degree"])): case
        for case in audit026["cases"]
    }
    cells: list[dict[str, Any]] = []
    verdict = "HLAMBDA_LAST_POSITIVE_ZERO_LT_ONE_PROVED"
    failure: dict[str, str] | None = None
    try:
        for m in cert026.M_VALUES:
            cells.append(run_cell(m, by_cell[(m, 0)], by_cell[(m, 4)]))
    except GateGap as exc:
        verdict = exc.code
        failure = {"code": exc.code, "detail": str(exc)}

    payload = {
        "schema": "q3_routeb_hlambda_outer_lobe_gate_audit.v1",
        "status": "CHALLENGER / NOT_RH",
        "verdict": verdict,
        "scope": "m in {13,53,257}; not a cofinal-family theorem",
        "method": (
            "Arb evaluation of certified interval Legendre cores at the "
            "single requested point, with live 026 tail allowance"
        ),
        "sources": [
            {
                "path": str(path.relative_to(ROOT)),
                "sha256": sha256(path),
            }
            for path in required
        ],
        "cells": cells,
        "failure": failure,
        "guards": {
            "sign_grid_used": False,
            "direct_sturm_on_combination_used": False,
            "truncated_mode_promoted_to_exact": False,
            "mu_substituted_by_one": False,
            "tail_interval_consumed": all(
                cell["tails"]["consumed_in_strict_inequality"]
                for cell in cells
            )
            and len(cells) == len(cert026.M_VALUES),
            "state_changed": False,
            "bus_010": "VOID",
        },
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n")

    with OUT_CSV.open("w", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            lineterminator="\n",
            fieldnames=[
                "m",
                "theta4_barrier_margin",
                "Psi_at_t",
                "tail_allowance",
                "strict_point_margin",
            ],
        )
        writer.writeheader()
        for cell in cells:
            writer.writerow(
                {
                    "m": cell["m"],
                    "theta4_barrier_margin": cell["theta4_barrier_margin"],
                    "Psi_at_t": cell["finite_core"]["Psi_at_t"],
                    "tail_allowance": cell["tails"]["consumed_allowance"],
                    "strict_point_margin": cell["strict_point_margin"],
                }
            )

    print(verdict)
    for cell in cells:
        print(
            f"m={cell['m']} margin={cell['strict_point_margin']} "
            f"tail={cell['tails']['consumed_allowance']}"
        )
    if failure is not None:
        raise SystemExit(verdict)


if __name__ == "__main__":
    main()
