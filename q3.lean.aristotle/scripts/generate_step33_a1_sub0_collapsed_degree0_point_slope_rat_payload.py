#!/usr/bin/env python3
"""Audit the collapsed degree-0 point-slope Rat payload.

This script is intentionally fail-closed.  It does not generate Lean code and
does not claim Step33A.1-A closure.  It records whether the proof-grade Rat
point-row payload theorem surfaces are present, then names the next exact gate:
budget/sign/tightness, not another payload-emission step.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = "q3_psdpd_step33_a1_sub0_collapsed_degree0_point_slope_rat_payload.v1"
PROOF_STATUS = "rat_payload_present_budget_kill_not_closed"
CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POINT_SLOPE_RAT_POINT_ROW_BUDGET_KILL_GAP"
)
MISSING_PAYLOAD_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POINT_SLOPE_RAWPRODUCT18_POINT_RAT_MIRROR_GAP"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0PointSlopeRatPayload.lean"
)
JSON_OUT = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rat_payload.json"
)
MD_OUT = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_point_slope_rat_payload.md"
)

REQUIRED_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated",
    "primaryFiniteRow0Parent0Split100Sub0_activeScaled_componentProductActual_order17_point_interval_rat_generated",
    "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_localCenter_eq_rat",
    "primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated",
]


def read_text(path: Path) -> str:
    if not path.exists():
        return ""
    return path.read_text(encoding="utf-8")


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        if needle in line:
            return idx
    return None


def sha256(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    text = read_text(PAYLOAD_FILE)
    symbols: list[dict[str, Any]] = [
        {
            "symbol": symbol,
            "present": symbol in text,
            "line": line_of(text, symbol),
        }
        for symbol in REQUIRED_SYMBOLS
    ]
    payload_present = all(row["present"] for row in symbols)
    proof_status = PROOF_STATUS if payload_present else "fail_closed_missing_rat_payload"
    current_gap = CURRENT_GAP if payload_present else MISSING_PAYLOAD_GAP

    audit: dict[str, Any] = {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "payloadFile": str(PAYLOAD_FILE.relative_to(ROOT)),
        "payloadPresent": payload_present,
        "proofStatus": proof_status,
        "currentGap": current_gap,
        "requiredSymbols": symbols,
        "fileHash": sha256(PAYLOAD_FILE),
        "boundary": (
            "Rat payload presence is not Step33A.1-A closure; budget/sign "
            "kill must be proved separately."
        ),
        "nextPatch": (
            "Try positive_row_budget_impossible/negative_row_budget_impossible "
            "from the Rat PointRowCert.Valid; if exact sign or threshold fails, "
            "replace the coarse raw Rat row with a true point-specific "
            "RawProduct18 Rat mirror."
        ),
    }

    JSON_OUT.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Step33A.1 Sub0 Collapsed Degree-0 Point-Slope Rat Payload Audit",
        "",
        f"- schema: `{SCHEMA}`",
        f"- generatedAt: `{audit['generatedAt']}`",
        f"- payloadFile: `{audit['payloadFile']}`",
        f"- payloadPresent: `{payload_present}`",
        f"- proofStatus: `{proof_status}`",
        f"- currentGap: `{current_gap}`",
        "",
        "## Required Symbols",
        "",
        "| symbol | present | line |",
        "| --- | --- | --- |",
    ]
    for row in symbols:
        lines.append(
            f"| `{row['symbol']}` | `{row['present']}` | `{row['line']}` |"
        )
    lines.extend(
        [
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
