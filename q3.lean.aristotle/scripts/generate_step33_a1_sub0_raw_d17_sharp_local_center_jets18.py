#!/usr/bin/env python3
"""Fail-closed audit for sharp raw-D17 local center-jet rows.

The coarse two-segment raw-D17 payload is Lean-checked but budget-killed.  The
first route review asked for proof-grade local center-jet values at centers
1/40 and 3/40, not rows rederived from full-cell absolute majorants.  After
those sharp rows checked, the exact budget comparison still failed.  This
script records both the sharp interfaces and the route kill for this
two-segment factorwise class.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_raw_d17_sharp_local_center_jets18.v1"
ROUTE = "raw_d17_sharp_local_center_jets18"
SHARP_LOCAL_CENTER_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SHARP_LOCAL_CENTER_JET_ROWS_GAP"
)
SHARP_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SHARP_TWO_SEGMENT_BUDGET_CONSTANT_FAIL"
)
SHARP_BUDGET_CHECK_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SHARP_TWO_SEGMENT_BUDGET_CHECK_GAP"
)
COARSE_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
SCRIPTS = ROOT / "scripts"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

TARGET_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean"
)
SHARP_BUDGET_KILL = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0"
    "RawD17SharpTwoSegmentBudgetKill.lean"
)
COARSE_LOCAL_PAYLOAD = (
    PROOFS / "PSD_CenteredCoeffRawOmegaARawD17LocalCenterJets18Payload.lean"
)
COARSE_TWO_SEGMENT_PAYLOAD = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean"
)
OMEGA_PRIME_TAYLOR_SCRIPT = (
    SCRIPTS / "generate_step33_a1_sub0_omega_prime_taylor_payload.py"
)
COMPONENT_TAYLOR_SCRIPT = (
    SCRIPTS / "generate_step33_a1_sub0_component_taylor_residual_payload.py"
)
REFINED_ENDPOINT_SCRIPT = (
    SCRIPTS / "q3_psdpd_step33_a_refined_subchunk_endpoint_rational_lean.py"
)

JSON_OUT = (
    REQUEST_DIR / "step33_a1_sub0_raw_d17_sharp_local_center_jets18_audit.json"
)
MD_OUT = (
    REQUEST_DIR / "step33_a1_sub0_raw_d17_sharp_local_center_jets18_audit.md"
)

REQUIRED_SHARP_THEOREMS = [
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_localCenterJet18_sharp_interval_generated"
        ),
        "purpose": (
            "proof-grade sharp lower/upper rows for normalized OmegaActual "
            "center jets through j < 18 at local centers 1/40 and 3/40"
        ),
    },
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_localCenterJet18_sharp_interval_generated"
        ),
        "purpose": (
            "proof-grade sharp lower/upper rows for normalized ShapeSqActual "
            "center jets through j < 18 at local centers 1/40 and 3/40"
        ),
    },
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_derivative_twoSegment_sharp_interval"
        ),
        "purpose": (
            "two-segment OmegaActual derivative rows derived from sharp local "
            "center jets and centeredTaylorDerivMajorant18"
        ),
    },
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_derivative_twoSegment_sharp_interval"
        ),
        "purpose": (
            "two-segment ShapeSqActual derivative rows derived from sharp "
            "local center jets and centeredTaylorDerivMajorant18"
        ),
    },
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_twoSegment_sharp_valid"
        ),
        "purpose": "raw-D17 signed-factor segment/family receiver fed by sharp rows",
    },
]

COARSE_KILL_THEOREMS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_twoSegment_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_twoSegment_budget_not_spendable"
    ),
]

SHARP_BUDGET_FAIL_THEOREMS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_twoSegment_sharp_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_twoSegment_sharp_budget_not_spendable"
    ),
]

SHARP_ROUTE_KILL_THEOREMS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_sharp_twoSegment_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_sharp_twoSegment_budget_not_spendable"
    ),
]

CANDIDATE_SOURCE_SURFACES = {
    OMEGA_PRIME_TAYLOR_SCRIPT: [
        "build_center_jet_prefix_tail_rows",
        "centerJetPrefixTailRowsProofGrade",
        "centerJetPrefixTailBridgeTheorem",
    ],
    COMPONENT_TAYLOR_SCRIPT: [
        "SHAPESQ_DERIV_TAYLOR_COARSE_CENTER",
        "SHAPESQ_DERIV_TAYLOR_COARSE_REMAINDER",
        "omegaTaylorCenterAnchorSource",
    ],
    REFINED_ENDPOINT_SCRIPT: [
        "shifted_digamma_series_prefix_tail_interval",
        "EndpointIntervalCert_of_shifted_digamma_series",
    ],
}


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def find_symbol(symbol: str, files: list[Path]) -> dict[str, Any]:
    for path in files:
        text = read_text(path)
        for line_no, line in enumerate(text.splitlines(), start=1):
            if symbol in line:
                return {"present": True, "file": rel(path), "line": line_no}
    return {"present": False, "file": None, "line": None}


def symbol_lines(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
    text = read_text(path)
    out: dict[str, dict[str, Any]] = {}
    for symbol in symbols:
        found = False
        line_no = None
        for idx, line in enumerate(text.splitlines(), start=1):
            if symbol in line:
                found = True
                line_no = idx
                break
        out[symbol] = {"present": found, "line": line_no}
    return out


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Raw-D17 Sharp Local Center-Jets18 Audit",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- targetLeanExists: `{ledger['targetLeanExists']}`",
        f"- sharpRowsPresent: `{ledger['sharpRowsPresent']}`",
        f"- sharpBudgetFailPresent: `{ledger['sharpBudgetFailPresent']}`",
        f"- sharpBudgetKillFileExists: `{ledger['sharpBudgetKillFileExists']}`",
        f"- sharpBudgetKillPresent: `{ledger['sharpBudgetKillPresent']}`",
        f"- coarseTwoSegmentBudgetFailPresent: `{ledger['coarseTwoSegmentBudgetFailPresent']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- nextFailureIfSharpBudgetFalse: `{SHARP_BUDGET_FAIL}`",
        "",
        "## Required Sharp Theorems",
        "",
    ]
    for item in ledger["requiredSharpTheorems"]:
        lines.extend(
            [
                f"### `{item['name']}`",
                "",
                f"- status: `{item['status']}`",
                f"- file: `{item['file']}`",
                f"- line: `{item['line']}`",
                f"- purpose: {item['purpose']}",
                "",
            ]
        )

    lines.extend(["## Sharp Budget Kill File", ""])
    lines.extend(
        [
            f"- file: `{ledger['sharpBudgetKillFile']}`",
            f"- exists: `{ledger['sharpBudgetKillFileExists']}`",
            "",
        ]
    )
    for theorem, item in ledger["sharpRouteKillTheorems"].items():
        lines.extend(
            [
                f"### `{theorem}`",
                "",
                f"- present: `{item['present']}`",
                f"- file: `{item['file']}`",
                f"- line: `{item['line']}`",
                "",
            ]
        )

    lines.extend(["## Sharp Budget Theorems", ""])
    for theorem, item in ledger["sharpBudgetFailTheorems"].items():
        lines.extend(
            [
                f"### `{theorem}`",
                "",
                f"- present: `{item['present']}`",
                f"- file: `{item['file']}`",
                f"- line: `{item['line']}`",
                "",
            ]
        )

    lines.extend(["## Candidate Source Surfaces", ""])
    for path, info in ledger["candidateSourceSurfaces"].items():
        lines.extend(
            [
                f"### `{path}`",
                "",
                f"- exists: `{info['exists']}`",
                f"- sha256: `{info['sha256']}`",
                "",
            ]
        )
        for symbol, symbol_info in info["symbols"].items():
            lines.append(
                f"- `{symbol}`: present=`{symbol_info['present']}`, line=`{symbol_info['line']}`"
            )
        lines.append("")

    lines.extend(
        [
            "## Boundary",
            "",
            "- This is not Step33A.1-A closure.",
            "- This audit does not emit the sharp Lean payload.",
            "- The previous full-cell absolute majorants are not sharp local rows.",
            "- The coarse two-segment budget fail remains local to the coarse row class.",
            "- If `sharpBudgetFailPresent = true`, this sharp two-segment class is Lean-killed by the exact budget comparison.",
            "- If `sharpBudgetKillPresent = true`, the route-facing kill alias is available for monitor and downstream ledger references.",
            "",
            "## Next Implementable Patch",
            "",
            ledger["nextImplementablePatch"],
            "",
        ]
    )
    return "\n".join(lines)


def build_ledger() -> dict[str, Any]:
    search_files = [
        TARGET_LEAN,
        SHARP_BUDGET_KILL,
        COARSE_LOCAL_PAYLOAD,
        COARSE_TWO_SEGMENT_PAYLOAD,
    ]
    required = []
    sharp_present = True
    for theorem in REQUIRED_SHARP_THEOREMS:
        found = find_symbol(theorem["name"], search_files)
        if not found["present"]:
            sharp_present = False
        required.append(
            {
                **theorem,
                "present": found["present"],
                "file": found["file"],
                "line": found["line"],
                "status": "present" if found["present"] else "missing",
            }
        )

    coarse_kill = {
        theorem: find_symbol(theorem, [COARSE_TWO_SEGMENT_PAYLOAD])
        for theorem in COARSE_KILL_THEOREMS
    }
    coarse_kill_present = all(info["present"] for info in coarse_kill.values())

    sharp_budget_fail = {
        theorem: find_symbol(theorem, [TARGET_LEAN])
        for theorem in SHARP_BUDGET_FAIL_THEOREMS
    }
    sharp_budget_fail_present = all(
        info["present"] for info in sharp_budget_fail.values()
    )

    sharp_route_kill = {
        theorem: find_symbol(theorem, [SHARP_BUDGET_KILL])
        for theorem in SHARP_ROUTE_KILL_THEOREMS
    }
    sharp_route_kill_present = all(
        info["present"] for info in sharp_route_kill.values()
    )

    candidate_surfaces: dict[str, Any] = {}
    for path, symbols in CANDIDATE_SOURCE_SURFACES.items():
        candidate_surfaces[rel(path)] = {
            "exists": path.exists(),
            "sha256": sha256_file(path),
            "symbols": symbol_lines(path, symbols),
        }

    if not sharp_present:
        proof_status = "fail_closed_sharp_local_center_jet_rows_gap"
        current_gap = SHARP_LOCAL_CENTER_GAP
        next_patch = (
            "Build proof-grade local `Rat`/interval certificates for the "
            "normalized `OmegaActual` and `ShapeSqActual` center jets at "
            "`1/40` and `3/40`; then instantiate the checked "
            "`centeredTaylorDerivMajorant18` bridge."
        )
    elif sharp_budget_fail_present:
        proof_status = "fail_closed_sharp_two_segment_budget_constant_fail"
        current_gap = SHARP_BUDGET_FAIL
        if sharp_route_kill_present:
            next_patch = (
                "Pivot to the direct whole-expression row-source route and keep "
                "`CollapsedExpression` intact through interval widening.  Do not "
                "continue factorwise two-segment sharpening."
            )
        else:
            next_patch = (
                "Record the route-facing sharp two-segment budget kill file, then "
                "pivot to the direct whole-expression row route.  Do not keep "
                "sharpening this same two-segment signed-factor class."
            )
    else:
        proof_status = "sharp_rows_present_budget_check_gap"
        current_gap = SHARP_BUDGET_CHECK_GAP
        next_patch = (
            "Add the exact sharp raw-poly budget comparison theorem; if false, "
            f"record `{SHARP_BUDGET_FAIL}`, otherwise wire the passing payload."
        )

    return {
        "schema": SCHEMA,
        "route": ROUTE,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "proofStatus": proof_status,
        "targetLeanFile": rel(TARGET_LEAN),
        "targetLeanExists": TARGET_LEAN.exists(),
        "sharpBudgetKillFile": rel(SHARP_BUDGET_KILL),
        "sharpBudgetKillFileExists": SHARP_BUDGET_KILL.exists(),
        "sharpRowsPresent": sharp_present,
        "sharpBudgetFailPresent": sharp_budget_fail_present,
        "sharpBudgetFailTheorems": sharp_budget_fail,
        "sharpBudgetKillPresent": sharp_route_kill_present,
        "sharpRouteKillTheorems": sharp_route_kill,
        "coarseTwoSegmentBudgetFailPresent": coarse_kill_present,
        "coarseTwoSegmentBudgetFailTheorems": coarse_kill,
        "currentGap": current_gap,
        "sharpLocalCenterGap": SHARP_LOCAL_CENTER_GAP,
        "sharpBudgetFail": SHARP_BUDGET_FAIL,
        "sharpBudgetCheckGap": SHARP_BUDGET_CHECK_GAP,
        "coarseBudgetFail": COARSE_BUDGET_FAIL,
        "requiredSharpTheorems": required,
        "candidateSourceSurfaces": candidate_surfaces,
        "doNotClaim": [
            "Step33A.1-A closure",
            "all raw-D17 factor routes fail",
            "full-cell absolute majorants are sharp local rows",
        ],
        "computerUseReview": [
            {
                "used": True,
                "choice": "A",
                "meaning": (
                    "first review: sharpen the same two-segment raw-D17 class "
                    "using proof-grade local center-jet values"
                ),
            },
            {
                "used": True,
                "choice": "A",
                "meaning": (
                    "second review after sharp budget fail: stop this "
                    "factorwise two-segment class and pivot to the direct "
                    "whole-expression row-source route"
                ),
            },
        ],
        "nextImplementablePatch": next_patch,
    }


def main() -> None:
    ledger = build_ledger()
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["currentGap"])
    print(f"wrote {rel(JSON_OUT)}")
    print(f"wrote {rel(MD_OUT)}")


if __name__ == "__main__":
    main()
