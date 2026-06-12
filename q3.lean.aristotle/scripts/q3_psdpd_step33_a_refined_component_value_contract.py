#!/usr/bin/env python3
"""Audit the refined subchunk ComponentValue proof contract.

This consumes the fail-closed refined candidate overlay plus the sampled
rational residual audit for one parent chunk.  It does not emit Lean and does
not claim proof closure.

The point of the audit is to separate two routes:

* the existing ComponentValueChunkProofData receiver is the right Lean shape;
* the old coarse product-box raw bounds are far too wide for the tiny
  Taylor remainders, so `diffLower` / `diffUpper` need a direct universal
  residual enclosure or sharper local component bounds.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
from typing import Any


getcontext().prec = 80

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OVERLAY = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0.json"
)
DEFAULT_RESIDUAL_AUDIT = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_rational_residual_audit_primary_finite_0_0.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_component_value_contract_primary_finite_0_0.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_component_value_contract_primary_finite_0_0.md"
)

OVERLAY_SCHEMA = "q3_psdpd_step33_a_refined_subchunk_candidate_overlay.v1"
RESIDUAL_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.v1"
)

COMPONENT_VALUE_RECEIVER = (
    "RawOmegaATaylorModelCertificate.ComponentValueChunkProofData"
)

RECEIVER_LEMMAS = [
    "RawOmegaATaylorModelCertificate.ComponentValueChunkProofData.valid",
    "RawOmegaATaylorModelCertificate.ComponentValueBounds.toValueBounds",
    "RawOmegaATaylorModelCertificate.diff_bounds_of_value_bounds",
    (
        "RawOmegaATaylorModelCertificate."
        "polynomial_value_bounds_of_sum_abs_coeff_mul_radius"
    ),
    "RawOmegaATaylorModelCertificate.product_bounds_of_scale_abs_box",
]


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def rational_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def decimal_string(value: Fraction | Decimal) -> str:
    if isinstance(value, Fraction):
        value = decimal_from_fraction(value)
    return format(value, ".18E")


def positive_part_power(degree: int, x: Fraction) -> Fraction:
    if x <= 0:
        return Fraction(0, 1)
    return x**degree


def centered_cardinal_bspline_zero(degree: int) -> Fraction:
    total = Fraction(0, 1)
    center = Fraction(degree + 1, 2)
    for j in range(degree + 2):
        total += (
            Fraction((-1) ** j * comb(degree + 1, j), 1)
            * positive_part_power(degree, center - j)
        )
    return Fraction(1, factorial(degree)) * total


def shape_majorant(k: int) -> Fraction:
    scale = Fraction(k + 1, 2)
    norm = centered_cardinal_bspline_zero(2 * k + 1)
    if norm <= 0:
        raise ValueError(f"nonpositive autocorrelation norm for k={k}: {norm}")
    return Fraction(1, 1) / (scale * norm)


def raw_box_half_width(k: int) -> Fraction:
    # Coarse first-window product seed:
    # scaleUpper * omegaMajorant * shapeSqUpper = (1/10) * 200 * majorant.
    return Fraction(20, 1) * shape_majorant(k)


def pilot_k(family: str) -> int:
    if family.startswith("primary_"):
        return 11
    if family.startswith("control_"):
        return 9
    raise ValueError(f"unknown family {family!r}")


def residual_rows_by_subchunk(residual_audit: dict[str, Any]) -> dict[int, dict[str, Any]]:
    return {
        int(row["subchunk"]): row
        for row in residual_audit.get("subchunks", [])
    }


def build_contract(
    *,
    overlay: dict[str, Any],
    residual_audit: dict[str, Any],
    overlay_path: Path,
    residual_audit_path: Path,
) -> dict[str, Any]:
    if overlay.get("schema") != OVERLAY_SCHEMA:
        raise ValueError(f"{overlay_path}: unexpected schema {overlay.get('schema')!r}")
    if residual_audit.get("schema") != RESIDUAL_AUDIT_SCHEMA:
        raise ValueError(
            f"{residual_audit_path}: unexpected schema {residual_audit.get('schema')!r}"
        )

    pilot = dict(overlay["pilot"])
    family = str(pilot["family"])
    k = pilot_k(family)
    coarse_half_width = raw_box_half_width(k)
    residual_by_subchunk = residual_rows_by_subchunk(residual_audit)

    rows = []
    coarse_passes = 0
    worst_row: dict[str, Any] | None = None
    for candidate in overlay.get("candidates", []):
        subchunk = int(candidate["subchunk"])
        poly_abs = parse_fraction(candidate["polyAbs"])
        remainder = parse_fraction(candidate["remainder"])
        required_for_coarse_diff = coarse_half_width + poly_abs
        coarse_excess = required_for_coarse_diff - remainder
        coarse_pass = coarse_excess <= 0
        if coarse_pass:
            coarse_passes += 1
        residual = residual_by_subchunk.get(subchunk, {})
        row = {
            "subchunk": subchunk,
            "left": candidate["left"],
            "right": candidate["right"],
            "polyAbs": rational_string(poly_abs),
            "remainder": rational_string(remainder),
            "coarseRawBoxHalfWidth": rational_string(coarse_half_width),
            "coarseRawBoxHalfWidthDecimal": decimal_string(coarse_half_width),
            "coarseDiffRequired": rational_string(required_for_coarse_diff),
            "coarseDiffRequiredDecimal": decimal_string(required_for_coarse_diff),
            "coarseDiffExcess": rational_string(coarse_excess),
            "coarseDiffExcessDecimal": decimal_string(coarse_excess),
            "coarseProductBoxDiffPasses": coarse_pass,
            "sampledMaxResidual": residual.get("sampledMaxResidual"),
            "sampledRemainderPasses": residual.get(
                "currentRemainderPassesSampledAudit"
            ),
        }
        rows.append(row)
        if worst_row is None or coarse_excess > parse_fraction(worst_row["coarseDiffExcess"]):
            worst_row = row

    coarse_failures = len(rows) - coarse_passes
    status = (
        "component_value_contract_ready_but_coarse_product_box_rejected"
        if coarse_failures
        else "component_value_contract_coarse_product_box_feasible_not_proof"
    )
    return {
        "schema": "q3_psdpd_step33_a_refined_component_value_contract.v1",
        "status": status,
        "meaning": (
            "Fail-closed generator-facing contract for the refined "
            "ComponentValueChunkProofData route.  It identifies the existing "
            "Lean receiver and rejects the coarse product-box raw bounds for "
            "the pilot diff inequalities."
        ),
        "overlay": str(overlay_path),
        "residualAudit": str(residual_audit_path),
        "pilot": pilot,
        "receiver": COMPONENT_VALUE_RECEIVER,
        "receiverLemmas": RECEIVER_LEMMAS,
        "counts": {
            "candidateSubchunks": len(rows),
            "proofSafeClosedFields": 0,
            "candidateOverlaySeededFields": overlay.get("counts", {}).get(
                "seededCandidateFields"
            ),
            "candidateOverlayStillMissingFields": overlay.get("counts", {}).get(
                "stillMissingFields"
            ),
            "coarseProductBoxDiffPasses": coarse_passes,
            "coarseProductBoxDiffFailures": coarse_failures,
            "omegaSmallWindowSubsetProofsNeeded": len(rows),
            "directResidualDiffFieldsNeeded": len(rows) * 2,
        },
        "coarseProductBox": {
            "k": k,
            "scaleUpper": "1/10",
            "omegaMajorant": "200",
            "shapeSqUpper": (
                "RawOmegaAChunkIntegral.centeredBSplineImagTransformSqGlobalMajorant "
                f"{k}"
            ),
            "shapeSqUpperExact": rational_string(shape_majorant(k)),
            "shapeSqUpperDecimal": decimal_string(shape_majorant(k)),
            "rawBoxHalfWidthExact": rational_string(coarse_half_width),
            "rawBoxHalfWidthDecimal": decimal_string(coarse_half_width),
            "diffFeasibilityTest": (
                "coarseRawBoxHalfWidth + polyAbs <= remainder"
            ),
            "verdict": (
                "rejected_for_pilot"
                if coarse_failures
                else "feasible_for_pilot_not_proof"
            ),
        },
        "fieldContract": {
            "candidateAlreadyMapped": [
                "coeff",
                "remainder",
                "remainderNonneg",
                "polyLower",
                "polyUpper",
                "polynomialLowerBound",
                "polynomialUpperBound",
                "integralLower",
                "integralUpper",
            ],
            "componentValueFieldsNeeded": [
                "omegaLower",
                "omegaUpper",
                "omegaLowerBound",
                "omegaUpperBound",
                "shapeSqLower",
                "shapeSqUpper",
                "shapeSqLowerBound",
                "shapeSqUpperBound",
                "cosLower",
                "cosUpper",
                "cosLowerBound",
                "cosUpperBound",
                "rawLower",
                "rawUpper",
                "componentProductLower",
                "componentProductUpper",
                "diffLower",
                "diffUpper",
            ],
            "trueOpenProofFields": ["diffLower", "diffUpper"],
        },
        "nextProofRoute": {
            "recommended": "direct_universal_residual_enclosure",
            "fallback": "sharper_local_component_value_bounds",
            "rejected": "coarse_product_abs_box_for_diff",
            "reason": (
                "The existing box raw bounds are order 1e1 while the pilot "
                "Taylor remainders are 1e-18."
            ),
        },
        "worstCoarseProductBoxRow": worst_row,
        "subchunks": rows,
        "routeGuard": [
            "not Lean proof data",
            "do not emit a refined Lean payload from this contract",
            "do not count sampled residual rows as universal diff proofs",
            "do not use the coarse product abs box to prove tiny diff remainders",
            "next generator must produce universal diffLower/diffUpper proofs",
            "do not mutate CSV, ARadius, radius-floor, LDL, H1/PO3, or Q3.Main",
        ],
    }


def render_md(contract: dict[str, Any]) -> str:
    counts = contract["counts"]
    coarse = contract["coarseProductBox"]
    worst = contract["worstCoarseProductBoxRow"]
    lines = [
        "# Step33A.1-A Refined Component-Value Contract",
        "",
        "Fail-closed contract.  This is not Lean proof data.",
        "",
        "## Verdict",
        "",
        f"- schema: `{contract['schema']}`",
        f"- status: `{contract['status']}`",
        f"- receiver: `{contract['receiver']}`",
        f"- candidate subchunks: `{counts['candidateSubchunks']}`",
        f"- proof-safe closed fields: `{counts['proofSafeClosedFields']}`",
        f"- coarse product-box diff passes: `{counts['coarseProductBoxDiffPasses']}`",
        f"- coarse product-box diff failures: `{counts['coarseProductBoxDiffFailures']}`",
        f"- direct residual diff fields still needed: `{counts['directResidualDiffFieldsNeeded']}`",
        "",
        "## Coarse Product-Box Feasibility",
        "",
        f"- k: `{coarse['k']}`",
        f"- scaleUpper: `{coarse['scaleUpper']}`",
        f"- omegaMajorant: `{coarse['omegaMajorant']}`",
        f"- shapeSqUpper decimal: `{coarse['shapeSqUpperDecimal']}`",
        f"- raw box half-width decimal: `{coarse['rawBoxHalfWidthDecimal']}`",
        f"- test: `{coarse['diffFeasibilityTest']}`",
        f"- verdict: `{coarse['verdict']}`",
        "",
    ]
    if worst is not None:
        lines.extend(
            [
                "## Worst Coarse Diff Row",
                "",
                f"- subchunk: `{worst['subchunk']}`",
                f"- interval: `({worst['left']}, {worst['right']}]`",
                f"- polyAbs: `{worst['polyAbs']}`",
                f"- remainder: `{worst['remainder']}`",
                f"- coarse required decimal: `{worst['coarseDiffRequiredDecimal']}`",
                f"- coarse excess decimal: `{worst['coarseDiffExcessDecimal']}`",
                f"- sampled max residual: `{worst['sampledMaxResidual']}`",
                "",
            ]
        )
    lines.extend(
        [
            "## Receiver Lemmas",
            "",
        ]
    )
    for lemma in contract["receiverLemmas"]:
        lines.append(f"- `{lemma}`")
    lines.extend(
        [
            "",
            "## Next Proof Route",
            "",
        ]
    )
    next_route = contract["nextProofRoute"]
    for key in ["recommended", "fallback", "rejected", "reason"]:
        lines.append(f"- {key}: `{next_route[key]}`")
    lines.extend(["", "## Guard", ""])
    for item in contract["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--overlay", type=Path, default=DEFAULT_OVERLAY)
    parser.add_argument("--residual-audit", type=Path, default=DEFAULT_RESIDUAL_AUDIT)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    overlay = load_json(args.overlay)
    residual_audit = load_json(args.residual_audit)
    contract = build_contract(
        overlay=overlay,
        residual_audit=residual_audit,
        overlay_path=args.overlay,
        residual_audit_path=args.residual_audit,
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(contract, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(contract), encoding="utf-8")

    counts = contract["counts"]
    print(
        "status={status} subchunks={subchunks} proof_safe_closed={closed} "
        "coarse_diff_passes={passes} coarse_diff_failures={failures} "
        "recommended={recommended}".format(
            status=contract["status"],
            subchunks=counts["candidateSubchunks"],
            closed=counts["proofSafeClosedFields"],
            passes=counts["coarseProductBoxDiffPasses"],
            failures=counts["coarseProductBoxDiffFailures"],
            recommended=contract["nextProofRoute"]["recommended"],
        )
    )


if __name__ == "__main__":
    run()
