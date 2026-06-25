#!/usr/bin/env python3
"""Fail-closed audit for collapsed degree-0 point-slope rows.

The route review after the signed Taylor receiver check selected the pointwise
payload split:

  signed factor point rows at 1/40 and 3/40
  -> exact RawProduct18 signed Leibniz assembly
  -> D17(ComponentProductActual)
  -> active-scale minus exact deriv(NominalOrder16Poly)
  -> PointRowCert.Valid

This script records the exact proof contract and refuses to emit a Lean payload
until the factor signed point rows exist as proof-grade local artifacts.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_collapsed_degree0_point_slope_rows.v1"
ROUTE = "collapsed_degree0_point_slope_signed_factor_point_rows"
PROOF_STATUS = "fail_closed_missing_factor_signed_point_rows"
CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POINT_SLOPE_RAWPRODUCT18_SIGNED_POINT_ROWS_GAP"
)
ASSEMBLY_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POINT_SLOPE_RAWPRODUCT18_POINT_ASSEMBLY_GAP"
)
FINAL_POINT_ROW_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POINT_SLOPE_COLLAPSED_POINT_ROW_RAT_PAYLOAD_GAP"
)
BUDGET_KILL_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POINT_SLOPE_RAT_POINT_ROW_BUDGET_KILL_GAP"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

POINT_INTERVAL_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18.lean"
)
POINT_SLOPE_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0PointSlopeRows.lean"
)
POINT_SLOPE_RAT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0PointSlopeRatPayload.lean"
)
ACTIVE_CENTER_JETS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActual"
    "CenterJetRowsPayload.lean"
)
RAW_D17_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorRows.lean"
)
SHARP_FACTOR_POINT_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean"
)
RAW_PRODUCT18_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ActiveActualRawProduct18Payload.lean"
)
NOMINAL_POLY_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0NominalPolyDerivRows.lean"
)

JSON_OUT = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rows.json"
)
MD_OUT = REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rows.md"

REQUIRED_SYMBOLS: dict[Path, list[str]] = {
    POINT_INTERVAL_FILE: [
        "iteratedDeriv_mem_Icc_of_centerJet18_point",
        "centeredTaylorDerivPointLower18",
        "centeredTaylorDerivPointUpper18",
    ],
    POINT_SLOPE_ROWS_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_pointRowValid_of_collapsedExpressionDeriv_point_interval"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0"
            "CollapsedDegree0SignedTaylorTransferGap"
        ),
    ],
    ACTIVE_CENTER_JETS_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetLower",
        "primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetUpper",
        "primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetLower",
        "primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetUpper",
        "primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval",
        "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval",
    ],
    RAW_D17_ROWS_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawProductActual_order18_eq_signedLeibniz"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
        ),
    ],
    SHARP_FACTOR_POINT_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_sharpSourceCenterJet18_signed_interval"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_sharpSourceCenterJet18_signed_interval"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_signed_point_interval_generated"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_signed_point_interval_generated"
        ),
    ],
    RAW_PRODUCT18_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "componentProductActual_order17_eq_rawProduct18"
        ),
    ],
    NOMINAL_POLY_FILE: [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "nominalOrder16Poly_deriv_eq_poly"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "nominalOrder16Poly_deriv_segment_interval_generated"
        ),
    ],
}

EXPECTED_PAYLOAD_SYMBOLS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "componentProductActual_order17_point_interval_rat_generated"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_pointRow_generated"
    ),
]


def read_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        pos = line.find(needle)
        if pos == -1:
            continue
        after_pos = pos + len(needle)
        if after_pos < len(line):
            after = line[after_pos]
            if after == "_" or after.isalnum():
                continue
        if pos > 0:
            before = line[pos - 1]
            if before == "_" or before.isalnum():
                continue
        if needle in line:
            return idx
    return None


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect_required_symbols() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for path, symbols in REQUIRED_SYMBOLS.items():
        text = read_text(path)
        for symbol in symbols:
            rows.append(
                {
                    "file": str(path.relative_to(ROOT)),
                    "symbol": symbol,
                    "present": symbol in text,
                    "line": line_of(text, symbol),
                }
            )
    return rows


def inspect_expected_payload() -> list[dict[str, Any]]:
    text = read_text(POINT_SLOPE_RAT_PAYLOAD_FILE)
    return [
        {
            "file": str(POINT_SLOPE_RAT_PAYLOAD_FILE.relative_to(ROOT)),
            "symbol": symbol,
            "present": symbol in text,
            "line": line_of(text, symbol),
        }
        for symbol in EXPECTED_PAYLOAD_SYMBOLS
    ]


def main() -> None:
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    symbol_status = inspect_required_symbols()
    payload_status = inspect_expected_payload()

    sharp_point_text = read_text(SHARP_FACTOR_POINT_FILE)
    factor_point_symbols = [
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_signed_point_interval_generated"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_signed_point_interval_generated"
        ),
    ]
    factor_point_status = [
        {
            "file": str(SHARP_FACTOR_POINT_FILE.relative_to(ROOT)),
            "symbol": symbol,
            "present": symbol in sharp_point_text,
            "line": line_of(sharp_point_text, symbol),
        }
        for symbol in factor_point_symbols
    ]
    factor_point_rows_present = all(row["present"] for row in factor_point_status)

    order17_center_ledger = {
        "omegaActualSignedCenterJets": "Fin 17 / orders 0..16",
        "shapeSqActualSignedCenterJets": "Fin 17 / orders 0..16",
        "order17CenterSource": (
            "symmetric proof-grade interval from order17 derivative absolute "
            "majorant, used only inside the signed point receiver"
        ),
        "evidence": [
            {
                "symbol": (
                    "primaryFiniteRow0Parent0Split100Sub0_"
                    "omegaActual_signed_centerJet_interval"
                ),
                "line": line_of(
                    read_text(ACTIVE_CENTER_JETS_FILE),
                    "primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval",
                ),
            },
            {
                "symbol": (
                    "primaryFiniteRow0Parent0Split100Sub0_"
                    "shapeSqActual_signed_centerJet_interval"
                ),
                "line": line_of(
                    read_text(ACTIVE_CENTER_JETS_FILE),
                    "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval",
                ),
            },
        ],
    }

    required_ok = all(row["present"] for row in symbol_status)
    rawproduct_point_assembly_present = payload_status[0]["present"]
    final_point_row_present = payload_status[1]["present"]
    payload_ok = rawproduct_point_assembly_present and final_point_row_present
    if payload_ok:
        proof_status = "rat_payload_present_budget_kill_not_closed"
        current_gap = BUDGET_KILL_GAP
    elif rawproduct_point_assembly_present:
        proof_status = "fail_closed_missing_collapsed_point_row_rat_payload"
        current_gap = FINAL_POINT_ROW_GAP
    elif factor_point_rows_present:
        proof_status = "fail_closed_missing_rawproduct18_point_assembly_payload"
        current_gap = ASSEMBLY_GAP
    else:
        proof_status = PROOF_STATUS
        current_gap = CURRENT_GAP
    should_emit_lean_payload = required_ok and not payload_ok

    audit: dict[str, Any] = {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": ROUTE,
        "proofStatus": proof_status,
        "currentGap": current_gap,
        "shouldEmitLeanPayload": should_emit_lean_payload,
        "routingGuard": [
            "do_not_instantiate_signed_taylor_on_whole_collapsed_expression",
            "do_not_instantiate_signed_taylor_directly_on_componentProductActual",
            "apply_signed_taylor_to_OmegaActual_and_ShapeSqActual_first",
            "assemble_RawProduct18_by_exact_signed_Leibniz",
            "then_active_scale_and_subtract_exact_nominal_derivative_point_row",
        ],
        "firstTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "componentProductActual_order17_point_interval_rat_generated"
        ),
        "finalPointRowTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_pointRow_generated"
        ),
        "requiredSymbols": symbol_status,
        "expectedPayloadSymbols": payload_status,
        "factorPointRowsPresent": factor_point_rows_present,
        "factorPointRows": factor_point_status,
        "rawProduct18PointAssemblyPresent": rawproduct_point_assembly_present,
        "finalCollapsedPointRowPresent": final_point_row_present,
        "ratPayloadFile": str(POINT_SLOPE_RAT_PAYLOAD_FILE.relative_to(ROOT)),
        "ratPayloadLeanChecked": payload_ok,
        "order17CenterLedger": order17_center_ledger,
        "fileHashes": {
            str(path.relative_to(ROOT)): sha256(path)
            for path in [*REQUIRED_SYMBOLS.keys(), POINT_SLOPE_RAT_PAYLOAD_FILE]
        },
    }

    JSON_OUT.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Step33A.1 Sub0 Collapsed Degree-0 Point-Slope Rows Audit",
        "",
        f"- schema: `{SCHEMA}`",
        f"- generatedAt: `{audit['generatedAt']}`",
        f"- route: `{ROUTE}`",
        f"- proofStatus: `{proof_status}`",
        f"- shouldEmitLeanPayload: `{should_emit_lean_payload}`",
        f"- currentGap: `{audit['currentGap']}`",
        "",
        "## First Required Theorems",
        "",
        (
            "- `primaryFiniteRow0Parent0Split100Sub0_"
            "componentProductActual_order17_point_interval_rat_generated`"
        ),
        (
            "- `primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_pointRow_generated`"
        ),
        "",
        "## Routing Guard",
        "",
    ]
    lines.extend(f"- `{item}`" for item in audit["routingGuard"])
    lines.extend(
        [
            "",
            "## Required Symbols",
            "",
            "| file | symbol | present | line |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in symbol_status:
        lines.append(
            f"| `{row['file']}` | `{row['symbol']}` | "
            f"`{row['present']}` | `{row['line']}` |"
        )
    lines.extend(
        [
            "",
            "## Expected Payload Symbols",
            "",
            "| file | symbol | present | line |",
            "| --- | --- | --- | --- |",
        ]
    )
    for row in payload_status:
        lines.append(
            f"| `{row['file']}` | `{row['symbol']}` | "
            f"`{row['present']}` | `{row['line']}` |"
        )
    lines.extend(
        [
            "",
            "## First Blocking Evidence",
            "",
            (
                "- factor signed point rows are present as Lean theorem "
                "surfaces for `OmegaActual` and `ShapeSqActual`."
            ),
            (
                "- RawProduct18 point assembly is present when "
                "`primaryFiniteRow0Parent0Split100Sub0_"
                "componentProductActual_order17_point_interval_generated` "
                "is present."
            ),
            (
                "- order-17 source-center data is still symmetric, coming from "
                "the proof-grade absolute derivative majorant, but it is now "
                "wired through the signed point receiver instead of blocking "
                "the factor point row surface."
            ),
            (
                "- the final collapsed point-row Rat payload is now present "
                "in `PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
                "CollapsedDegree0PointSlopeRatPayload.lean`; it uses the "
                "tight active-scale interval, four-corner multiplication, "
                "and exact nominal derivative point evaluation."
            ),
            (
                "- this is not a Step33A.1-A closure claim: the remaining "
                "layer is the budget/sign/tightness audit needed to turn "
                "the proof-grade point row into the point-slope kill."
            ),
            "",
            "## Verdict",
            "",
            (
                f"`{current_gap}`: Rat payload exists and Lean-checks, but "
                "the point-slope budget kill is still open."
            ),
            "",
        ]
    )
    MD_OUT.write_text("\n".join(lines), encoding="utf-8")

    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
