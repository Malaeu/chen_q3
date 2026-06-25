#!/usr/bin/env python3
"""Fail-closed audit for the collapsed degree-0 Rat point-row budget gate.

The Rat point-row payload is a checked proof object, but the follow-up budget
kill file was not Lean-validated in a bounded run.  This script records that
boundary explicitly and routes the live gate back to the direct whole
CollapsedExpression row source.  It intentionally does not claim a Lean kill or
Step33A.1-A closure.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_collapsed_degree0_point_slope_rat_audit.v1"
PROOF_STATUS = "fail_closed_rat_point_row_budget_kill_unvalidated"
CURRENT_GAP = "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP"
PREVIOUS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POINT_SLOPE_RAT_POINT_ROW_BUDGET_KILL_GAP"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

RAT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0PointSlopeRatPayload.lean"
)
RAT_BUDGET_FAIL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0PointSlopeRatBudgetFail.lean"
)
TWO_SEGMENT_KILL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SharpTwoSegmentBudgetKill.lean"
)
RAT_PAYLOAD_AUDIT = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rat_payload.json"
)
POINT_ROWS_AUDIT = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rows.json"
)
JSON_OUT = REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rat_audit.json"
MD_OUT = REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rat_audit.md"

REQUIRED_RAT_PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated",
    "primaryFiniteRow0Parent0Split100Sub0_activeScaled_componentProductActual_order17_point_interval_rat_generated",
    "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_localCenter_eq_rat",
    "primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated",
]

RELATED_KILL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_fail_rat",
    "primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_not_spendable",
]


def read_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        if needle in line:
            return idx
    return None


def symbol_rows(path: Path, symbols: list[str]) -> list[dict[str, Any]]:
    text = read_text(path)
    rel = str(path.relative_to(ROOT))
    return [
        {
            "symbol": symbol,
            "file": rel,
            "present": symbol in text,
            "line": line_of(text, symbol),
        }
        for symbol in symbols
    ]


def main() -> None:
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    payload_audit = read_json(RAT_PAYLOAD_AUDIT)
    point_rows_audit = read_json(POINT_ROWS_AUDIT)

    rat_payload_symbols = symbol_rows(RAT_PAYLOAD_FILE, REQUIRED_RAT_PAYLOAD_SYMBOLS)
    related_kill_symbols = symbol_rows(TWO_SEGMENT_KILL_FILE, RELATED_KILL_SYMBOLS)
    payload_present = all(row["present"] for row in rat_payload_symbols)
    related_kill_present = all(row["present"] for row in related_kill_symbols)

    audit: dict[str, Any] = {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "proofStatus": PROOF_STATUS,
        "proofGrade": False,
        "diagnosticGrade": True,
        "leanBudgetKillClaimAllowed": False,
        "step33A1AClosureClaimAllowed": False,
        "currentGap": CURRENT_GAP,
        "previousGap": PREVIOUS_GAP,
        "failureCode": CURRENT_GAP,
        "ratPayloadFile": str(RAT_PAYLOAD_FILE.relative_to(ROOT)),
        "ratPayloadPresent": payload_present,
        "ratPayloadLeanCheckedFromPreviousAudit": point_rows_audit.get(
            "ratPayloadLeanChecked"
        ),
        "ratPayloadAuditProofStatus": payload_audit.get("proofStatus"),
        "ratPayloadSymbols": rat_payload_symbols,
        "ratPayloadFileHash": sha256(RAT_PAYLOAD_FILE),
        "relatedTwoSegmentBudgetKillFile": str(TWO_SEGMENT_KILL_FILE.relative_to(ROOT)),
        "relatedTwoSegmentBudgetKillPresent": related_kill_present,
        "relatedTwoSegmentBudgetKillSymbols": related_kill_symbols,
        "relatedTwoSegmentBudgetKillFileHash": sha256(TWO_SEGMENT_KILL_FILE),
        "unvalidatedLeanBudgetFailFile": str(RAT_BUDGET_FAIL_FILE.relative_to(ROOT)),
        "unvalidatedLeanBudgetFailFileExists": RAT_BUDGET_FAIL_FILE.exists(),
        "unvalidatedLeanBudgetFailDisposition": "deleted_or_absent",
        "budgetGateRequiredComparisons": {
            "positive": [
                "0 <= primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointLowerRat i",
                "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat < primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointLowerRat i",
            ],
            "negative": [
                "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointUpperRat i <= 0",
                "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0AllowedDerivAbsRat < -primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointUpperRat i",
            ],
        },
        "boundary": (
            "The Rat point-row payload remains useful and checked, but the "
            "current session has no Lean-validated theorem that the Rat rows "
            "instantiate positive_row_budget_impossible or "
            "negative_row_budget_impossible.  This audit is a fail-closed "
            "diagnostic and must not be used as proof of a budget kill."
        ),
        "computerUseRouteReview": {
            "used": True,
            "decision": "CHOSEN: A",
            "artifact": str(Path("scripts") / Path(__file__).name),
            "outputs": [str(JSON_OUT.relative_to(ROOT)), str(MD_OUT.relative_to(ROOT))],
            "nextGenerator": (
                "scripts/generate_step33_a1_sub0_combined_order16_"
                "scaled_remainder_direct_payload.py"
            ),
            "failureCode": CURRENT_GAP,
            "notProofEvidence": True,
        },
        "nextPatch": (
            "Use the direct whole CollapsedExpression row-source generator.  "
            "Do not spend further factorwise point-row budgets as closure."
        ),
    }

    JSON_OUT.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Step33A.1 Sub0 Collapsed Degree-0 Rat Point-Row Audit",
        "",
        f"- schema: `{SCHEMA}`",
        f"- generatedAt: `{audit['generatedAt']}`",
        f"- proofStatus: `{PROOF_STATUS}`",
        "- proofGrade: `False`",
        "- diagnosticGrade: `True`",
        f"- currentGap: `{CURRENT_GAP}`",
        f"- previousGap: `{PREVIOUS_GAP}`",
        f"- unvalidatedLeanBudgetFailFileExists: `{audit['unvalidatedLeanBudgetFailFileExists']}`",
        "",
        "## Rat Payload Surfaces",
        "",
        "| symbol | present | line |",
        "| --- | --- | --- |",
    ]
    for row in rat_payload_symbols:
        lines.append(f"| `{row['symbol']}` | `{row['present']}` | `{row['line']}` |")
    lines.extend(
        [
            "",
            "## Related Lean-Checked Kill",
            "",
            "| symbol | present | line |",
            "| --- | --- | --- |",
        ]
    )
    for row in related_kill_symbols:
        lines.append(f"| `{row['symbol']}` | `{row['present']}` | `{row['line']}` |")
    lines.extend(
        [
            "",
            "## Budget Gate",
            "",
            "Positive-row kill requires both:",
            "",
            "- `0 <= collapsed point lower`",
            "- `AllowedDerivAbsRat < collapsed point lower`",
            "",
            "Negative-row kill requires both:",
            "",
            "- `collapsed point upper <= 0`",
            "- `AllowedDerivAbsRat < -collapsed point upper`",
            "",
            "No Lean-validated theorem for those comparisons is present in this audit.",
            "",
            "## Boundary",
            "",
            audit["boundary"],
            "",
            "## Next Patch",
            "",
            audit["nextPatch"],
            "",
        ]
    )
    MD_OUT.write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps(audit, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
