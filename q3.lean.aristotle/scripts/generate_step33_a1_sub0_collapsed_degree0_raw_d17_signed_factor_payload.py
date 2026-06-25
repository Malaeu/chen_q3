#!/usr/bin/env python3
"""Ledger for the first collapsed degree-0 raw-D17 signed-factor payload.

The Lean payload is a proof-grade full-cell smoke segment for the
signed-factor receiver.  It proves that the receiver and raw/poly bridge are
wired correctly, and it also proves that this full-cell smoke segment is not
budget-spendable.  This script records those facts without claiming
Step33A.1-A closure.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_payload.v1"
ROUTE = "collapsed_degree0_raw_d17_signed_factor_payload"
PROOF_STATUS = "fail_closed_segment0_budget_not_spendable"
SEGMENT_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_CONSTANT_FAIL"
)
TWO_SEGMENT_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_ROWS_GAP"
)
TWO_SEGMENT_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL"
)
ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_ROWS_GAP"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean"
)
PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorPayload.lean"
)
JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_payload.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_payload.md"
)

ROWS_SYMBOLS = [
    "Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert",
    "theorem to_rawInterval",
    "theorem to_rawPolySegmentValid",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment"
    ),
]

PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0RawD17OmegaLower",
    "primaryFiniteRow0Parent0Split100Sub0RawD17OmegaUpper",
    "primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqLower",
    "primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqUpper",
    "primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermLower",
    "primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermUpper",
    "primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_segment0_valid"
    ),
    "primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawPolySegment0",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_rawPoly_segment0_valid"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_segment0_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_segment0_budget_not_spendable"
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


def symbol_lines(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
    text = read_text(path)
    lines = text.splitlines()
    out: dict[str, dict[str, Any]] = {}
    for symbol in symbols:
        found = False
        line_no = None
        for idx, line in enumerate(lines, start=1):
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
        "# Step33A.1-A Raw-D17 Signed-Factor Payload Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- leanPayloadWritten: `{ledger['leanPayloadWritten']}`",
        f"- payloadProofGrade: `{ledger['payloadProofGrade']}`",
        f"- rawD17SignedFactorSegment0Valid: `{ledger['rawD17SignedFactorSegment0Valid']}`",
        f"- rawPolySegment0Valid: `{ledger['rawPolySegment0Valid']}`",
        f"- segment0BudgetSpendable: `{ledger['segment0BudgetSpendable']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- selectedNextPatch: `{ledger['selectedNextPatch']}`",
        "",
        "## Next Patch",
        "",
        f"- script: `{ledger['nextPatchScript']}`",
        f"- leanFile: `{ledger['nextPatchLeanFile']}`",
        f"- segments: `{ledger['nextPatchSegments']}`",
        f"- rowsFailureCode: `{ledger['nextFailureCodeIfRowsMissing']}`",
        f"- budgetFailureCode: `{ledger['nextFailureCodeIfBudgetFalse']}`",
        "",
        "First required theorem names:",
        "",
    ]
    for theorem in ledger["nextPatchTheorems"]:
        lines.append(f"- `{theorem}`")
    lines.extend(
        [
            "",
        "## Meaning",
        "",
        "The checked Lean file gives one full-cell smoke payload for the",
        "raw-D17 signed-factor receiver and its same-segment raw/poly bridge.",
        "The exact budget theorem in the same file proves that this smoke",
        "segment is too wide and cannot be spent as the Step33A.1-A degree-0",
        "budget.",
        "",
        "This does not kill the direct route.  It only kills the full-cell",
        "absolute smoke payload as a spendable certificate.  The next live",
        "patch is the two-segment raw-D17 signed-factor payload selected by",
        "the Computer Use route review.",
        "",
        "## Files",
        "",
        f"- rowsFile: `{ledger['rowsFile']}`",
        f"- rowsFileSha256: `{ledger['rowsFileSha256']}`",
        f"- payloadFile: `{ledger['payloadFile']}`",
        f"- payloadFileSha256: `{ledger['payloadFileSha256']}`",
        "",
        "## Row Receiver Symbols",
        "",
    ]
    )
    for symbol, info in ledger["rowsSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", "## Payload Symbols", ""])
    for symbol, info in ledger["payloadSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- No Step33A.1-A closure is claimed.",
            "- No direct-route impossibility is claimed from this one smoke failure.",
            "- The old symmetric RawProduct18 budget class remains non-spendable.",
            "",
        ]
    )
    return "\n".join(lines)


def build_ledger() -> dict[str, Any]:
    rows_symbols = symbol_lines(ROWS_FILE, ROWS_SYMBOLS)
    payload_symbols = symbol_lines(PAYLOAD_FILE, PAYLOAD_SYMBOLS)
    rows_present = all_present(rows_symbols)
    payload_present = all_present(payload_symbols)
    segment_valid = payload_symbols[
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_valid"
        )
    ]["present"]
    raw_poly_valid = payload_symbols[
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_rawPoly_segment0_valid"
        )
    ]["present"]
    budget_not_spendable = payload_symbols[
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_budget_not_spendable"
        )
    ]["present"]

    first_failure = SEGMENT_BUDGET_FAIL if budget_not_spendable else ROWS_GAP
    current_gap = first_failure

    return {
        "schema": SCHEMA,
        "route": ROUTE,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "proofStatus": PROOF_STATUS if budget_not_spendable else "fail_closed_missing_payload_rows",
        "leanPayloadWritten": payload_present,
        "payloadProofGrade": payload_present,
        "rowsFile": rel(ROWS_FILE),
        "rowsFileSha256": sha256_file(ROWS_FILE),
        "rowsSymbols": rows_symbols,
        "rowsReceiverPresent": rows_present,
        "rowsReceiverLeanChecked": rows_present,
        "payloadFile": rel(PAYLOAD_FILE),
        "payloadFileSha256": sha256_file(PAYLOAD_FILE),
        "payloadSymbols": payload_symbols,
        "rawD17SignedFactorSegment0Valid": segment_valid,
        "rawPolySegment0Valid": raw_poly_valid,
        "segment0BudgetSpendable": False if budget_not_spendable else None,
        "segment0BudgetFailureTheorem": (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_budget_not_spendable"
        ),
        "currentGap": current_gap,
        "firstFailureCode": first_failure,
        "firstConcreteSubgap": first_failure,
        "selectedNextPatch": (
            "build_two_segment_raw_d17_signed_factor_payload"
            if budget_not_spendable
            else "write_raw_d17_signed_factor_segment0_payload"
        ),
        "nextPatchScript": (
            "scripts/generate_step33_a1_sub0_collapsed_degree0_"
            "raw_d17_signed_factor_segments.py"
        ),
        "nextPatchLeanFile": (
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
            "CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean"
        ),
        "nextPatchSegments": ["[0, 1/20]", "[1/20, 1/10]"],
        "nextPatchTheorems": [
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_left_valid"
            ),
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_right_valid"
            ),
            (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "rawD17_signedFactor_twoSegment_family_valid"
            ),
        ],
        "nextFailureCodeIfRowsMissing": TWO_SEGMENT_ROWS_GAP,
        "nextFailureCodeIfBudgetFalse": TWO_SEGMENT_BUDGET_FAIL,
        "doNotClaim": [
            "Step33A.1-A closure",
            "direct-route impossibility",
            "spendability of old symmetric RawProduct18 majorants",
        ],
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
