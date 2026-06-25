#!/usr/bin/env python3
"""Audit for the two-segment collapsed degree-0 raw-D17 signed-factor route.

This is intentionally not a Lean payload generator yet.  The Computer Use route
review chose a fail-closed audit first: do not emit a two-segment Lean payload
until proof-grade local center-jet rows and the derived local signed
derivative rows for OmegaActual and ShapeSqActual exist on both subsegments.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_collapsed_degree0_"
    "raw_d17_signed_factor_two_segment_rows_audit.v3"
)
ROUTE = "collapsed_degree0_raw_d17_signed_factor_two_segment_rows_audit"
PROOF_STATUS = "fail_closed_two_segment_rows_gap"
ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_ROWS_GAP"
)
LOCAL_CENTER_JETS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_LOCAL_CENTER_JET_ROWS_GAP"
)
SHAPESQ_LOCAL_CENTER_JETS_GAP = (
    "STEP33_A1_SUB0_SHAPESQ_LOCAL_CENTER_JETS18_PAYLOAD_GAP"
)
DERIVATIVE_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_TWO_SEGMENT_DERIVATIVE_ROWS_ORDER18_GAP"
)
TAYLOR_BRIDGE_GAP = (
    "STEP33_A1_SUB0_CENTERED_TAYLOR_DERIVATIVE_MAJORANT18_BRIDGE_GAP"
)
BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorRows.lean"
)
SMOKE_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorPayload.lean"
)
SIGNED_SOURCE_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0SignedSourcePayload.lean"
)
TWO_SEGMENT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean"
)
TAYLOR_BRIDGE_18_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant18.lean"
)
OMEGA_SHAPESQ_ORDER18_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ActiveActualRawProduct18Source.lean"
)
SHAPESQ_ORDER18_PAYLOAD_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAShapeSqOrder18Payload.lean"
)
LOCAL_CENTER_JETS_PAYLOAD_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaARawD17LocalCenterJets18Payload.lean"
)

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_"
    "two_segment_rows_audit.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_"
    "two_segment_rows_audit.md"
)

SUPPORT_SYMBOLS = {
    TAYLOR_BRIDGE_18_FILE: [
        "centeredTaylorDerivMajorant18",
        "centeredTaylorDerivMajorant18Range",
        "centeredTaylorDerivMajorant18_last",
        "iteratedDeriv_norm_le_centeredTaylorDerivMajorant18_last",
        "iteratedDeriv_norm_le_centeredTaylorDerivMajorant18",
    ],
    OMEGA_SHAPESQ_ORDER18_SOURCE_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18",
        "primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18",
    ],
    SHAPESQ_ORDER18_PAYLOAD_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18",
        "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18",
    ],
    LOCAL_CENTER_JETS_PAYLOAD_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter",
        "primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetLower",
        "primaryFiniteRow0Parent0Split100Sub0OmegaActualLocalJetUpper",
        "primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetLower",
        "primaryFiniteRow0Parent0Split100Sub0ShapeSqActualLocalJetUpper",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_localCenterJet_interval_generated"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_localCenterJet_interval_generated"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_derivative_twoSegment_interval"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_derivative_twoSegment_interval"
        ),
    ],
    TWO_SEGMENT_PAYLOAD_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_valid",
        "primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_valid",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_twoSegment_budget_not_spendable"
        ),
    ],
    ROWS_FILE: [
        "Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment"
        ),
    ],
    SMOKE_PAYLOAD_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_valid"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_rawPoly_segment0_valid"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_budget_not_spendable"
        ),
    ],
    SIGNED_SOURCE_PAYLOAD_FILE: [
        "Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsed_degree0_remainder_of_raw_poly_segment_family_cert"
        ),
    ],
}

REQUIRED_LOCAL_CENTER_JET_THEOREMS = [
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_localCenterJet18_twoSegment_interval"
        ),
        "purpose": (
            "proof-grade lower/upper rows for normalized OmegaActual center "
            "jets through j < 18 at local centers 1/40 and 3/40"
        ),
        "statement": """
theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_twoSegment_interval
    (i : Fin 2) (j : Fin 18) :
    let center : Real := if i.1 = 0 then (1/40 : Real) else (3/40 : Real)
    (omegaCenterJetLower i j : Real) <=
        iteratedDeriv j.1 step22OmegaArchWeight center /
          (Nat.factorial j.1 : Real)
    /\\
        iteratedDeriv j.1 step22OmegaArchWeight center /
          (Nat.factorial j.1 : Real)
      <= (omegaCenterJetUpper i j : Real)
""".strip(),
    },
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_localCenterJet18_twoSegment_interval"
        ),
        "purpose": (
            "proof-grade lower/upper rows for normalized ShapeSqActual center "
            "jets through j < 18 at local centers 1/40 and 3/40"
        ),
        "statement": """
theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_twoSegment_interval
    (i : Fin 2) (j : Fin 18) :
    let center : Real := if i.1 = 0 then (1/40 : Real) else (3/40 : Real)
    (shapeSqCenterJetLower i j : Real) <=
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSq center /
          (Nat.factorial j.1 : Real)
    /\\
        iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSq center /
          (Nat.factorial j.1 : Real)
      <= (shapeSqCenterJetUpper i j : Real)
""".strip(),
    },
]

REQUIRED_LOCAL_ROW_THEOREMS = [
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_derivative_twoSegment_interval"
        ),
        "purpose": (
            "uniform local lower/upper rows for OmegaActual derivatives "
            "on each of the two subsegments, derived from local center jets "
            "and centeredTaylorDerivMajorant18"
        ),
        "statement": """
theorem
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_interval
    (i : Fin 2) (k : Fin 19) :
    forall eta in Set.Icc (cellL i : Real) (cellU i : Real),
      (omegaLower i k : Real) <=
          iteratedDeriv k.1 step22OmegaArchWeight eta
      /\\
          iteratedDeriv k.1 step22OmegaArchWeight eta
        <= (omegaUpper i k : Real)
""".strip(),
    },
    {
        "name": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_derivative_twoSegment_interval"
        ),
        "purpose": (
            "uniform local lower/upper rows for ShapeSqActual derivatives "
            "on each of the two subsegments, derived from local center jets "
            "and centeredTaylorDerivMajorant18"
        ),
        "statement": """
theorem
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_interval
    (i : Fin 2) (k : Fin 19) :
    forall eta in Set.Icc (cellL i : Real) (cellU i : Real),
      (shapeSqLower i k : Real) <=
          iteratedDeriv k.1
            primaryFiniteRow0Parent0Split100Sub0ShapeSq eta
      /\\
          iteratedDeriv k.1
            primaryFiniteRow0Parent0Split100Sub0ShapeSq eta
        <= (shapeSqUpper i k : Real)
""".strip(),
    },
]

PAYLOAD_TARGET_THEOREMS = [
    "primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_valid",
    "primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_valid",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_twoSegment_family_valid"
    ),
]

BUDGET_FAIL_THEOREMS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_twoSegment_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_twoSegment_budget_not_spendable"
    ),
]


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


def all_present(lines: dict[str, dict[str, Any]]) -> bool:
    return all(entry["present"] for entry in lines.values())


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Raw-D17 Signed-Factor Two-Segment Rows Audit",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- shouldEmitTwoSegmentLeanPayload: `{ledger['shouldEmitTwoSegmentLeanPayload']}`",
        f"- twoSegmentPayloadExists: `{ledger['twoSegmentPayloadExists']}`",
        f"- proofGradeLocalRowsPresent: `{ledger['proofGradeLocalRowsPresent']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- nextFailureCodeIfRowsCloseButBudgetFails: `{ledger['nextFailureCodeIfRowsCloseButBudgetFails']}`",
        "",
        "## Segments",
        "",
    ]
    for segment in ledger["segments"]:
        lines.append(
            f"- `{segment['name']}`: cellL=`{segment['cellL']}`, cellU=`{segment['cellU']}`"
        )

    lines.extend(["", "## Missing Proof-Grade Row Theorems", ""])
    lines.extend(
        [
            "### Order-18 generic Taylor bridge",
            "",
            f"- status: `{ledger['order18TaylorBridgeStatus']}`",
            f"- failureCodeIfMissing: `{TAYLOR_BRIDGE_GAP}`",
            "",
            "### Uniform order-18 source rows",
            "",
            f"- status: `{ledger['order18UniformSourcesStatus']}`",
            "",
            "### Local center-jet payload interfaces",
            "",
        ]
    )
    for theorem in ledger["requiredLocalCenterJetTheorems"]:
        status = theorem["status"]
        lines.extend(
            [
                f"#### `{theorem['name']}`",
                "",
                f"- status: `{status}`",
                f"- purpose: {theorem['purpose']}",
                "",
                "```lean",
                theorem["statement"],
                "```",
                "",
            ]
        )

    lines.extend(["### Derived local derivative interval interfaces", ""])
    for theorem in ledger["requiredLocalRowTheorems"]:
        status = theorem["status"]
        lines.extend(
            [
                f"#### `{theorem['name']}`",
                "",
                f"- status: `{status}`",
                f"- purpose: {theorem['purpose']}",
                "",
                "```lean",
                theorem["statement"],
                "```",
                "",
            ]
        )

    lines.extend(["## Target Payload Theorems", ""])
    for theorem, info in ledger["payloadTargetTheorems"].items():
        lines.append(
            f"- `{theorem}`: present=`{info['present']}`, file=`{info['file']}`, line=`{info['line']}`"
        )

    lines.extend(["", "## Budget Fail Theorems", ""])
    for theorem, info in ledger["budgetFailTheorems"].items():
        lines.append(
            f"- `{theorem}`: present=`{info['present']}`, file=`{info['file']}`, line=`{info['line']}`"
        )

    lines.extend(["", "## Checked Supporting Surfaces", ""])
    for path, info in ledger["supportSurfaces"].items():
        lines.extend(
            [
                f"### `{path}`",
                "",
                f"- exists: `{info['exists']}`",
                f"- sha256: `{info['sha256']}`",
                f"- allSymbolsPresent: `{info['allSymbolsPresent']}`",
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
            "- This audit is not a proof of Step33A.1-A.",
            "- This audit is not a Lean payload and does not create a Lean payload.",
            "- The order-18 generic Taylor bridge is only an analytic transport layer.",
            "- Local center-jet payload rows remain separate proof objects.",
            "- The checked full-cell smoke segment remains non-spendable.",
            "- The global symmetric full-cell rows must not be reused as local segment rows.",
            "- A two-segment rows gap does not kill the direct whole-expression route.",
            "",
            "## Next Implementable Patch",
            "",
            (
                "Build proof-grade local center-jet rows through `j < 18` for "
                "`OmegaActual` and `ShapeSqActual` at centers `1/40` and "
                "`3/40`; reuse the checked full-cell order-18 source bounds; "
                "derive local derivative interval rows through `k = 18` with "
                "`centeredTaylorDerivMajorant18`; then emit the two raw-D17 "
                "signed-factor segment certs and the raw/poly family cert."
            ),
            "",
        ]
    )
    return "\n".join(lines)


def build_ledger() -> dict[str, Any]:
    support_surfaces: dict[str, Any] = {}
    for path, symbols in SUPPORT_SYMBOLS.items():
        lines = symbol_lines(path, symbols)
        support_surfaces[rel(path)] = {
            "exists": path.exists(),
            "sha256": sha256_file(path),
            "symbols": lines,
            "allSymbolsPresent": all_present(lines),
        }

    search_files = [
        TAYLOR_BRIDGE_18_FILE,
        LOCAL_CENTER_JETS_PAYLOAD_FILE,
        ROWS_FILE,
        SMOKE_PAYLOAD_FILE,
        SIGNED_SOURCE_PAYLOAD_FILE,
        TWO_SEGMENT_PAYLOAD_FILE,
    ]
    bridge_symbols = support_surfaces[rel(TAYLOR_BRIDGE_18_FILE)]["symbols"]
    bridge_present = all_present(bridge_symbols)
    order18_uniform_present = (
        all_present(support_surfaces[rel(OMEGA_SHAPESQ_ORDER18_SOURCE_FILE)]["symbols"])
        and all_present(support_surfaces[rel(SHAPESQ_ORDER18_PAYLOAD_FILE)]["symbols"])
    )

    center_jet_theorems = []
    center_jets_present = True
    for theorem in REQUIRED_LOCAL_CENTER_JET_THEOREMS:
        found = find_symbol(theorem["name"], search_files)
        if not found["present"]:
            center_jets_present = False
        center_jet_theorems.append(
            {
                **theorem,
                "present": found["present"],
                "file": found["file"],
                "line": found["line"],
                "status": "present" if found["present"] else "missing",
            }
        )

    row_theorems = []
    local_rows_present = True
    for theorem in REQUIRED_LOCAL_ROW_THEOREMS:
        found = find_symbol(theorem["name"], search_files)
        if not found["present"]:
            local_rows_present = False
        row_theorems.append(
            {
                **theorem,
                "present": found["present"],
                "file": found["file"],
                "line": found["line"],
                "status": "present" if found["present"] else "missing",
            }
        )

    payload_targets = {
        theorem: find_symbol(theorem, search_files) for theorem in PAYLOAD_TARGET_THEOREMS
    }
    payload_target_present = all(info["present"] for info in payload_targets.values())
    budget_fail_targets = {
        theorem: find_symbol(theorem, search_files) for theorem in BUDGET_FAIL_THEOREMS
    }
    budget_fail_present = all(
        info["present"] for info in budget_fail_targets.values()
    )

    if not bridge_present:
        proof_status = "fail_closed_order18_taylor_bridge_gap"
        current_gap = TAYLOR_BRIDGE_GAP
    elif not order18_uniform_present:
        proof_status = "fail_closed_order18_uniform_source_gap"
        current_gap = ROWS_GAP
    elif not center_jets_present:
        proof_status = "fail_closed_local_center_jet_rows_gap"
        current_gap = LOCAL_CENTER_JETS_GAP
    elif not local_rows_present:
        proof_status = "fail_closed_two_segment_derivative_rows_gap"
        current_gap = DERIVATIVE_ROWS_GAP
    elif budget_fail_present:
        proof_status = "fail_closed_two_segment_budget_constant_fail"
        current_gap = BUDGET_FAIL
    elif payload_target_present:
        proof_status = "two_segment_payload_valid_present"
        current_gap = None
    else:
        proof_status = "rows_present_payload_ready"
        current_gap = None

    return {
        "schema": SCHEMA,
        "route": ROUTE,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "proofStatus": proof_status,
        "segments": [
            {"name": "left", "cellL": "0", "cellU": "1/20"},
            {"name": "right", "cellL": "1/20", "cellU": "1/10"},
        ],
        "order18TaylorBridgePresent": bridge_present,
        "order18TaylorBridgeStatus": "present" if bridge_present else "missing",
        "order18UniformSourcesPresent": order18_uniform_present,
        "order18UniformSourcesStatus": (
            "present" if order18_uniform_present else "missing"
        ),
        "proofGradeLocalCenterJetsPresent": center_jets_present,
        "proofGradeLocalRowsPresent": local_rows_present,
        "twoSegmentPayloadFile": rel(TWO_SEGMENT_PAYLOAD_FILE),
        "twoSegmentPayloadExists": TWO_SEGMENT_PAYLOAD_FILE.exists(),
        "twoSegmentPayloadTheoremsPresent": payload_target_present,
        "twoSegmentBudgetFailPresent": budget_fail_present,
        "shouldEmitTwoSegmentLeanPayload": bridge_present
        and center_jets_present
        and local_rows_present
        and not TWO_SEGMENT_PAYLOAD_FILE.exists()
        and not budget_fail_present,
        "currentGap": current_gap,
        "firstFailureCode": current_gap,
        "legacyRowsGap": ROWS_GAP,
        "localCenterJetsGap": LOCAL_CENTER_JETS_GAP,
        "shapeSqLocalCenterJetsGap": SHAPESQ_LOCAL_CENTER_JETS_GAP,
        "derivativeRowsGap": DERIVATIVE_ROWS_GAP,
        "taylorBridgeGap": TAYLOR_BRIDGE_GAP,
        "nextFailureCodeIfRowsCloseButBudgetFails": BUDGET_FAIL,
        "requiredLocalCenterJetTheorems": center_jet_theorems,
        "requiredLocalRowTheorems": row_theorems,
        "payloadTargetTheorems": payload_targets,
        "budgetFailTheorems": budget_fail_targets,
        "supportSurfaces": support_surfaces,
        "doNotClaim": [
            "Step33A.1-A closure",
            "two-segment route failure",
            "direct whole-expression route failure",
            "spendability of global symmetric full-cell rows",
        ],
        "computerUseReview": {
            "used": True,
            "choice": "A",
            "meaning": (
                "Create the raw-D17 local center-jet order18 payload first; "
                "do not create TwoSegmentPayload.lean until those rows and "
                "the derived two-segment OmegaActual and ShapeSqActual "
                "derivative rows exist."
            ),
        },
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
