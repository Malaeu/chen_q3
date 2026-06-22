#!/usr/bin/env python3
"""Fail-closed realSinc derivative majorant payload for Step33A.1-A sub0.

This generator emits exact rational rows matching
`Step33Sub0RealSincDerivativeMajorantCert` in
`Q3/Proofs/PSD_CenteredCoeffRawOmegaARealSincDerivativeCert.lean`.

It intentionally does not mark the payload proof-grade.  The first missing
bridge is still the analytic crosswalk from the even power series of
`realSinc` to the iterated derivative majorant on `0 <= u <= 1/400`.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import factorial
from pathlib import Path
import sys
from typing import Any


if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(2_000_000)


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_OUT_JSON = REQUEST_DIR / "step33_a1_sub0_realsinc_derivative_payload.json"
DEFAULT_OUT_MD = REQUEST_DIR / "step33_a1_sub0_realsinc_derivative_payload.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_realsinc_derivative_payload.v1"
ROUTE_ID = "STEP33_A1_SUB0_REALSINC_DERIVATIVE_MAJORANT"
STATUS = "fail_closed_missing_realsinc_iteratedderiv_series_majorant_crosswalk"
FIRST_FAILURE = "STEP33_A1_SUB0_REALSINC_ITERATEDDERIV_SERIES_MAJORANT_CROSSWALK_GAP"
LEAN_CONTRACT_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaARealSincDerivativeCert.lean"
)
SCALED_RECEIVER_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver.lean"
)


def rat_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def start_index(k: int) -> int:
    return (k + 1) // 2


def majorant_term(k: int, m: int) -> Fraction:
    n = start_index(k) + m
    e = 2 * n - k
    return Fraction(1, 400**e) / Fraction((2 * n + 1) * factorial(e), 1)


def row(k: int, prefix_n: int) -> dict[str, Any]:
    prefix = sum((majorant_term(k, m) for m in range(prefix_n)), Fraction(0, 1))
    next_term = majorant_term(k, prefix_n)
    ratio = Fraction(1, 400**2)
    tail = next_term / (1 - ratio)
    base_abs = prefix + tail
    return {
        "k": k,
        "startIndex": start_index(k),
        "prefixN": prefix_n,
        "nextTerm": rat_text(next_term),
        "tailRatioUpper": rat_text(ratio),
        "tailAbs": rat_text(tail),
        "prefixExactRational": rat_text(prefix),
        "baseAbs": rat_text(base_abs),
        "rationalArithmeticChecked": True,
        "analyticCrosswalkPresent": False,
        "proofGrade": False,
        "firstFailure": FIRST_FAILURE,
    }


def build_payload(prefix_n: int) -> dict[str, Any]:
    contract_path = ROOT / LEAN_CONTRACT_FILE
    receiver_path = ROOT / SCALED_RECEIVER_FILE
    rows = [row(k, prefix_n) for k in range(18)]
    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": STATUS,
        "firstFailure": FIRST_FAILURE,
        "target": {
            "family": "primary_finite",
            "row": 0,
            "parentChunk": 0,
            "subchunk": 0,
            "uInterval": ["0", "1/400"],
            "orders": "0..17",
        },
        "leanInterfaces": {
            "contractFile": LEAN_CONTRACT_FILE,
            "contractFileHash16": file_hash(contract_path),
            "certStructure": "Step33Sub0RealSincDerivativeMajorantCert",
            "validPredicate": "Step33Sub0RealSincDerivativeMajorantCert.Valid",
            "analyticMajorantPredicate": (
                "Step33Sub0RealSincDerivativeMajorantCert.ProvidesAnalyticMajorant"
            ),
            "scaledReceiverFile": SCALED_RECEIVER_FILE,
            "scaledReceiverFileHash16": file_hash(receiver_path),
            "scaledReceiverTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_realSinc_abs"
            ),
        },
        "proofMode": "exact_rational_prefix_plus_geometric_tail_contract",
        "proofGrade": False,
        "proofGradeBlockedBy": [
            FIRST_FAILURE,
            "STEP33_A1_SUB0_REALSINC_DERIVATIVE_BOUNDS_0_TO_17_GAP",
        ],
        "arithmetic": {
            "termFormula": "(1/400)^(2*n-k) / ((2*n+1) * (2*n-k)!)",
            "nFormula": "ceil(k/2) + m",
            "ceilFormula": "(k+1)//2",
            "tailRatioUpper": "1/160000",
            "prefixN": prefix_n,
            "rationalArithmeticChecked": True,
            "proofGradeAnalyticMajorantPresent": False,
        },
        "rows": rows,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Step33A.1-A sub0 realSinc derivative payload")
    lines.append("")
    lines.append(f"- schema: `{payload['schema']}`")
    lines.append(f"- status: `{payload['status']}`")
    lines.append(f"- firstFailure: `{payload['firstFailure']}`")
    lines.append(f"- proofGrade: `{payload['proofGrade']}`")
    lines.append(
        "- key point: rational prefix/tail arithmetic is checked, but the "
        "analytic `realSinc` derivative crosswalk is not yet proved."
    )
    lines.append("")
    lines.append("## Lean interface")
    lines.append("")
    for key, value in payload["leanInterfaces"].items():
        lines.append(f"- {key}: `{value}`")
    lines.append("")
    lines.append("## Arithmetic")
    lines.append("")
    for key, value in payload["arithmetic"].items():
        lines.append(f"- {key}: `{value}`")
    lines.append("")
    lines.append("## Rows")
    lines.append("")
    lines.append(
        "| k | startIndex | prefixN | tailRatioUpper | prefixExactRational | tailAbs | baseAbs | proofGrade |"
    )
    lines.append("| --- | ---: | ---: | --- | --- | --- | --- | --- |")
    for item in payload["rows"]:
        lines.append(
            "| {k} | {startIndex} | {prefixN} | `{tailRatioUpper}` | "
            "`{prefixExactRational}` | `{tailAbs}` | `{baseAbs}` | `{proofGrade}` |".format(
                **item
            )
        )
    lines.append("")
    lines.append("## Live gap")
    lines.append("")
    lines.append(
        "`STEP33_A1_SUB0_REALSINC_ITERATEDDERIV_SERIES_MAJORANT_CROSSWALK_GAP`:"
    )
    lines.append(
        "prove in Lean that these rational rows majorize "
        "`||iteratedDeriv k realSinc u||` for all `k : Fin 18` and "
        "`u in Set.Icc 0 (1/400)`."
    )
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix-n", type=int, default=32)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    if args.prefix_n <= 0:
        raise SystemExit("--prefix-n must be positive")

    payload = build_payload(args.prefix_n)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_markdown(payload), encoding="utf-8")
    print(f"wrote {args.out_json}")
    print(f"wrote {args.out_md}")
    print(f"status={payload['status']}")
    print(f"firstFailure={payload['firstFailure']}")


if __name__ == "__main__":
    main()
