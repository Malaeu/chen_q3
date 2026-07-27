#!/usr/bin/env python3
"""Fail-closed source and algebra audit for Route-B goal 025.

This audit deliberately does not turn finite-matrix eigenvalues into point
intervals.  It verifies the exact arithmetic behind the recessive-tail cone,
checks the validation plants, and stops at the first missing proof-grade input.
"""

from __future__ import annotations

import csv
import hashlib
import json
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
Q3 = HERE.parents[2]
ROOT = Q3.parent

GOAL = HERE / "025_legendre_tail_certificate.goal.md"
PROSHKA = HERE / "proshka" / "PROSHKA_PEN_GO_2026-07-27.md"
PROLATE_LAYER = Q3 / "Q3" / "Proofs" / "RouteB" / "ProlateLayer.lean"
FINITE_DIAGNOSTIC = HERE / "E_STAR_CANDIDATE_ADJUDICATION.json"
G3_AUDIT = HERE / "G3_INTERVAL_FOURIER_CERT_AUDIT.json"
SAME_MODE = HERE / "PROLATE_SAME_MODE_LOCK.csv"

OUT_JSON = HERE / "LEGENDRE_RECESSIVE_TAIL_CERTIFICATE_AUDIT.json"
OUT_CSV = HERE / "LEGENDRE_RECESSIVE_TAIL_CERTIFICATE_AUDIT.csv"

VERDICT = "G3_COARSE_EIGENVALUE_INTERVAL_MISSING"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def file_record(path: Path, classification: str, reason: str) -> dict[str, object]:
    return {
        "path": str(path.relative_to(ROOT)),
        "exists": path.is_file(),
        "sha256": sha256(path) if path.is_file() else None,
        "classification": classification,
        "reason": reason,
    }


def exact_algebra() -> list[dict[str, object]]:
    """Return exact rational identities used by the cone proof."""

    # All constants are exact Fractions; no floating-point value enters.
    k0_margin = Fraction(31, 24)
    b_loss = Fraction(1, 2)
    d_lower = k0_margin - b_loss
    r_over_g = Fraction(1, 4)
    cone_upper = Fraction(1, 2)
    denominator_lower = d_lower - r_over_g * cone_upper
    p_over_g = Fraction(1, 3)
    image_upper = p_over_g / denominator_lower
    contraction = (p_over_g * r_over_g) / denominator_lower**2
    lambda_lipschitz = (
        (p_over_g / denominator_lower**2)
        / (Fraction(1, 1) - contraction)
    )

    assert d_lower == Fraction(19, 24)
    assert denominator_lower == Fraction(2, 3)
    assert image_upper == Fraction(1, 2)
    assert contraction == Fraction(3, 16)
    assert lambda_lipschitz == Fraction(12, 13)

    return [
        {
            "name": "p_bound",
            "identity": (
                "(2N-3)(2N-1)-3N(N-1)=N^2-5N+3>0 for N>=5"
            ),
            "conclusion": "0 < p_k/G <= 1/3",
            "status": "EXACT",
        },
        {
            "name": "r_bound",
            "identity": (
                "(2N+3)(2N+5)-4(N+1)(N+2)=4N+7>0"
            ),
            "conclusion": "0 < r_k/G <= 1/4",
            "status": "EXACT",
        },
        {
            "name": "B_bound",
            "identity": (
                "(2N-1)(2N+3)-4(N(N+1)-1)=1"
            ),
            "conclusion": "B_k >= N(N+1)-G/2",
            "status": "EXACT",
        },
        {
            "name": "denominator_bound",
            "identity": "31/24-1/2-(1/4)(1/2)=2/3",
            "conclusion": "d_k-r_k*x >= (2/3)G on x in [0,1/2]",
            "status": "EXACT",
        },
        {
            "name": "cone_image",
            "identity": "(1/3)/(2/3)=1/2",
            "conclusion": "T_k([0,1/2]) subset [0,1/2]",
            "status": "EXACT",
        },
        {
            "name": "contraction",
            "identity": "((1/3)(1/4))/(2/3)^2=3/16",
            "conclusion": "sup |T'_k| <= 3/16",
            "status": "EXACT",
        },
        {
            "name": "lambda_width",
            "identity": "(3/4)/(1-3/16)=12/13",
            "conclusion": (
                "diam(I_K0+1) <= (1/2)(3/16)^L"
                " + (12/(13G))(Lambda_upper-Lambda_lower)"
            ),
            "status": "EXACT",
        },
        {
            "name": "tail_l1_linf",
            "identity": "sum_{j>=1} 2^-j=1",
            "conclusion": "T1 <= |a_K| and Tinf <= |a_K|",
            "status": "EXACT",
        },
        {
            "name": "tail_l2",
            "identity": (
                "sum_{j>=1} 2*4^-j/(2N+4j+1)"
                " <= 2/[3(2N+5)]"
            ),
            "conclusion": "T2^2 <= 2|a_K|^2/[3(2n+4K+5)]",
            "status": "EXACT",
        },
        {
            "name": "tail_derivative",
            "identity": (
                "sum_{j>=1} 2^-j(N+2j)^2=N^2+8N+24"
            ),
            "conclusion": "Tprime <= |a_K|(N^2+8N+24)",
            "status": "EXACT",
        },
        {
            "name": "tail_fourier",
            "identity": "integral_{-1}^1 |P_l(x)| dx <= 2",
            "conclusion": "TF <= 2|a_K|",
            "status": "SOURCE_BOUND_REQUIRED",
        },
    ]


def obligations() -> list[dict[str, str]]:
    return [
        {
            "step": "1",
            "obligation": "exact DLMF A_k,B_k,C_k recurrence",
            "status": "SOURCE_LOCKED",
            "detail": (
                "DLMF 30.8.2--30.8.4; p=-A, r=-C, d=B-Lambda;"
                " project Theta=Lambda+G"
            ),
        },
        {
            "step": "2",
            "obligation": "K0 from certified Lambda interval",
            "status": "BLOCKED",
            "detail": (
                "no source-locked proof-grade [Lambda_lower,Lambda_upper]"
                " for degrees 0 and 4 is materialized"
            ),
        },
        {
            "step": "3",
            "obligation": "invariant cone [0,1/2]",
            "status": "EXACT_CONDITIONAL",
            "detail": "exact once the K0 hypothesis is supplied",
        },
        {
            "step": "4",
            "obligation": "contraction <=3/16",
            "status": "EXACT_CONDITIONAL",
            "detail": "exact once the K0 hypothesis is supplied",
        },
        {
            "step": "5",
            "obligation": "interval continued fraction",
            "status": "NOT_FORMED",
            "detail": "requires a proof-grade Lambda interval",
        },
        {
            "step": "6",
            "obligation": "sup,L2,derivative,Fourier tail",
            "status": "EXACT_CONDITIONAL",
            "detail": "formula ledger verified; no numerical tail ball formed",
        },
        {
            "step": "7",
            "obligation": "finite core consumes tail-ratio interval",
            "status": "NOT_FORMED",
            "detail": "no point tail and no finite=infinite identification used",
        },
        {
            "step": "8",
            "obligation": "full finite-plus-tail normalization",
            "status": "NOT_FORMED",
            "detail": "finite core and tail interval are not yet available",
        },
    ]


def plants() -> list[dict[str, str]]:
    return [
        {
            "plant": "tail interval replaced by {0}",
            "status": "FIRES_SYMBOLICALLY",
            "witness": (
                "last core diagonal is d_K-r_K*rho_{K+1}; r_K>0,"
                " so {0} removes the certified interval term"
            ),
        },
        {
            "plant": "n=4 replaced by n=2",
            "status": "FIRES_SOURCE_LOCK",
            "witness": (
                "ProlatePair locks h0 to chi0 and h4 to chi2;"
                " no degree-2 packet field exists"
            ),
        },
        {
            "plant": "L2 tail deleted",
            "status": "FIRES_SYMBOLICALLY",
            "witness": (
                "DLMF normalization is an infinite weighted square sum;"
                " deleting the positive tail changes its enclosure"
            ),
        },
        {
            "plant": "Lambda interval widened",
            "status": "FIRES_SYMBOLICALLY",
            "witness": (
                "diameter bound increases by"
                " (12/(13G))*Delta(width), strictly positive for G>0"
            ),
        },
    ]


def main() -> None:
    for required in (GOAL, PROSHKA, PROLATE_LAYER):
        if not required.is_file():
            raise SystemExit(f"missing required source: {required}")

    source_inventory = [
        file_record(
            PROLATE_LAYER,
            "TYPE_LAYER_ONLY",
            (
                "ProlatePair stores candidate functions and scalar chi fields"
                " as hypotheses; it has no eigenvalue interval theorem"
            ),
        ),
        file_record(
            FINITE_DIAGNOSTIC,
            "REJECTED_APPROXIMATE_FINITE_DATA",
            (
                "high-precision characteristic strings, residual estimates,"
                " and finite truncations are not interval enclosures of the"
                " exact infinite mode"
            ),
        ),
        file_record(
            G3_AUDIT,
            "PREVIOUS_GAP_REPORT",
            (
                "records that G3ExactModeIntervalEnclosure is absent;"
                " it is not a provider of Lambda bounds"
            ),
        ),
        file_record(
            SAME_MODE,
            "REJECTED_FLOAT_DIAGNOSTIC",
            "float same-mode coordinate lock; no Lambda interval",
        ),
    ]

    payload = {
        "target": "G3ExactModeIntervalEnclosure_LegendreRecessiveTail",
        "primary_theorem": "LegendreRecessiveTailCertificate",
        "epistemic_status": "FAIL_CLOSED_AT_FIRST_MISSING_INPUT",
        "verdict": VERDICT,
        "source_locks": {
            "goal": {
                "path": str(GOAL.relative_to(ROOT)),
                "sha256": sha256(GOAL),
            },
            "directive": {
                "path": str(PROSHKA.relative_to(ROOT)),
                "sha256": sha256(PROSHKA),
            },
            "primary_formula_source": "DLMF 30.8.1--30.8.7",
        },
        "locked_parameters": {
            "spheroidal_order": 0,
            "degrees": [0, 4],
            "DLMF_parameter": "G=gamma^2",
            "eigenvalue_crosswalk": "Theta=Lambda+G",
        },
        "exact_algebra": exact_algebra(),
        "source_inventory": source_inventory,
        "coarse_eigenvalue_interval": {
            "materialized": False,
            "accepted_sources": [],
            "rejected_zero_width_inputs": [
                "finite tridiagonal eigenvalue",
                "high-precision characteristic decimal",
                "float64 same-mode diagnostic",
            ],
            "required_next_input": (
                "source-locked Rayleigh/Temple, Gershgorin plus tail-resolvent,"
                " or interval-Sturm enclosure [Lambda_lower,Lambda_upper]"
                " for degrees 0 and 4"
            ),
        },
        "obligations": obligations(),
        "plants": plants(),
        "forbidden_actions": {
            "terminal_ratio_zero_used": False,
            "finite_eigenpair_identified_with_infinite_mode": False,
            "mu_replaced_by_one": False,
            "float_wrapped_in_zero_width_ball": False,
            "sign_grid_run": False,
        },
        "state_mutated": False,
        "bus_010_created": False,
    }

    OUT_JSON.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )

    with OUT_CSV.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["step", "obligation", "status", "detail"],
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(payload["obligations"])

    print(json.dumps(
        {
            "verdict": VERDICT,
            "exact_checks": len(payload["exact_algebra"]),
            "plants_fired": sum(
                row["status"].startswith("FIRES") for row in payload["plants"]
            ),
            "lambda_interval_materialized": False,
            "state_mutated": False,
            "bus_010_created": False,
            "json": str(OUT_JSON),
            "csv": str(OUT_CSV),
        },
        ensure_ascii=False,
        indent=2,
    ))


if __name__ == "__main__":
    main()
