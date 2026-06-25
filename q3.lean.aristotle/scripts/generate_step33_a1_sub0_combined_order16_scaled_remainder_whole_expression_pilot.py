#!/usr/bin/env python3
"""Fail-closed source-data gate for the Step33A.1-A whole-expression pilot.

The intended pilot must evaluate the complete collapsed expression

    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression

as one object, preserving cancellation.  This script does not fake that pilot
when the repository lacks a complete coefficient/remainder source stream.  It
first audits the local proof/data surface and stops with a named source-data
gap unless the required whole-expression rows exist.
"""

from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_combined_order16_"
    "scaled_remainder_whole_expression_pilot.v1"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_"
    "whole_expression_pilot.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_"
    "whole_expression_pilot.md"
)

DIRECT_SOURCE_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ScaledRemainderDirectSourceBridge.lean"
)
NOMINAL_POLYNOMIAL_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "NominalPolynomialBridge.lean"
)
DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ScaledRemainderDirectCollapsedSourceIntervalCert.lean"
)
DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ScaledRemainderDirectCollapsedTaylorSource.lean"
)
DIRECT_HORNER_SOURCE_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ScaledRemainderDirectHornerSourceBridge.lean"
)
DIRECT_CONCRETE_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ScaledRemainderDirectConcretePayload.lean"
)
PAYLOAD_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)

TARGET_EXPRESSION = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
    "ScaledRemainderCollapsedExpression"
)
TARGET_RECEIVER = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainder_collapsed_segment_remainder"
)
SOURCE_INTERVAL_RECEIVER = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainder_"
    "collapsed_segment_remainder_of_source_interval"
)
DIRECT_HORNER_VALID = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainderDirectHorner_valid"
)
SOURCE_DATA_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "WHOLE_EXPRESSION_PILOT_SOURCE_DATA_GAP"
)
PARENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_ROW_SOURCE_GAP"
)

ACCEPTED_PILOT_VERDICTS = [
    "PASS_STABLE_MARGIN",
    "NEGATIVE_MARGIN",
    "UNSTABLE_MARGIN",
    "SEGMENT_EXPLOSION",
]


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return ""


def load_json(path: Path) -> dict[str, Any]:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return {}


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    text = read_text(path)
    return {symbol: symbol in text for symbol in symbols}


def targeted_symbol_present(symbol: str, paths: list[Path]) -> bool:
    return any(symbol in read_text(path) for path in paths)


def targeted_theorem_present(name: str, paths: list[Path]) -> bool:
    pattern = re.compile(r"\btheorem\s+" + re.escape(name) + r"(\s|:)")
    return any(pattern.search(read_text(path)) for path in paths)


def build_ledger() -> dict[str, Any]:
    payload_ledger = load_json(PAYLOAD_LEDGER)
    exact_source = (
        payload_ledger.get("directRowSourceImplementationReview", {})
        .get("exactCoefficientSource", {})
    )

    checked_support = {
        "directSourceBridge": {
            "file": rel(DIRECT_SOURCE_BRIDGE_FILE),
            "exists": DIRECT_SOURCE_BRIDGE_FILE.exists(),
            "symbols": file_contains(
                DIRECT_SOURCE_BRIDGE_FILE,
                [
                    TARGET_EXPRESSION,
                    "combinedOrder16ScaledRemainder_eq_collapsedExpression",
                    "combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval",
                ],
            ),
        },
        "nominalPolynomialBridge": {
            "file": rel(NOMINAL_POLYNOMIAL_BRIDGE_FILE),
            "exists": NOMINAL_POLYNOMIAL_BRIDGE_FILE.exists(),
            "symbols": file_contains(
                NOMINAL_POLYNOMIAL_BRIDGE_FILE,
                [
                    "primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff",
                    "combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly",
                ],
            ),
        },
        "collapsedSourceIntervalReceiver": {
            "file": rel(DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE),
            "exists": DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE.exists(),
            "symbols": file_contains(
                DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE,
                [
                    "Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert",
                    SOURCE_INTERVAL_RECEIVER,
                ],
            ),
        },
        "collapsedTaylorReceiver": {
            "file": rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE),
            "exists": DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE.exists(),
            "symbols": file_contains(
                DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE,
                [
                    "Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert",
                    "collapsed_segment_remainder_of_centerJet15_order16",
                ],
            ),
        },
        "directHornerSourceBridge": {
            "file": rel(DIRECT_HORNER_SOURCE_BRIDGE_FILE),
            "exists": DIRECT_HORNER_SOURCE_BRIDGE_FILE.exists(),
            "symbols": file_contains(
                DIRECT_HORNER_SOURCE_BRIDGE_FILE,
                [
                    "valid_of_collapsed_horner_rows",
                    "of_collapsed_horner_range",
                ],
            ),
        },
    }

    missing_artifacts = [
        {
            "id": "complete_collapsed_expression_coeff_stream",
            "required": (
                "proof-grade rational coefficients for the complete "
                "CollapsedExpression on each chosen segment"
            ),
            "currentEvidence": exact_source.get(
                "status",
                "missing_direct_payload_ledger_source_status",
            ),
            "present": exact_source.get("status")
            == "COMPLETE_COLLAPSED_EXPRESSION_STREAM_PRESENT",
        },
        {
            "id": "collapsed_segment_remainder_rows",
            "required": (
                "Lean-visible rows proving CollapsedExpression minus the "
                "generated rawOmegaATaylorPolynomial is bounded on every "
                "segment"
            ),
            "theorem": TARGET_RECEIVER,
            "present": targeted_theorem_present(
                TARGET_RECEIVER,
                [
                    DIRECT_CONCRETE_PAYLOAD_FILE,
                    DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE,
                    DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE,
                ],
            ),
        },
        {
            "id": "source_interval_generated_or_direct_horner_valid",
            "required": (
                "either a concrete source-interval generated theorem feeding "
                "the checked receiver, or a concrete DirectHorner valid theorem"
            ),
            "acceptedInterfaces": [
                SOURCE_INTERVAL_RECEIVER,
                DIRECT_HORNER_VALID,
            ],
            "present": targeted_theorem_present(
                DIRECT_HORNER_VALID, [DIRECT_CONCRETE_PAYLOAD_FILE]
            )
            or targeted_theorem_present(
                "nonzeroModel_interval_generated",
                [DIRECT_CONCRETE_PAYLOAD_FILE],
            ),
        },
        {
            "id": "direct_concrete_payload_file",
            "required": (
                "DirectConcretePayload.lean only after segment rows, Horner "
                "rows, exact cover, and budget rows exist"
            ),
            "file": rel(DIRECT_CONCRETE_PAYLOAD_FILE),
            "present": DIRECT_CONCRETE_PAYLOAD_FILE.exists(),
        },
    ]
    source_data_ready = all(item["present"] for item in missing_artifacts)

    if source_data_ready:
        status = "ready_to_run_numeric_pilot"
        phase2_result = "NOT_RUN_READY_TO_RUN"
        current_gap = PARENT_GAP
        next_patch = (
            "Run a cancellation-preserving interval/rational pilot over the "
            "complete collapsedExpression coefficient stream."
        )
    else:
        status = "source_data_gap"
        phase2_result = "NOT_RUN_SOURCE_DATA_GAP"
        current_gap = SOURCE_DATA_GAP
        next_patch = (
            "Produce the same-target collapsedExpression coefficient stream "
            "plus proof-grade source-interval or direct-Horner remainder rows; "
            "then rerun this pilot."
        )

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "Step33A.1-A direct whole-expression CollapsedExpression pilot",
        "status": status,
        "phase2ResultNow": phase2_result,
        "pilotVerdict": None,
        "acceptedPilotVerdicts": ACCEPTED_PILOT_VERDICTS,
        "proofGrade": False,
        "sourceDataReady": source_data_ready,
        "sourceDataStatus": status,
        "currentGap": current_gap,
        "parentGap": PARENT_GAP,
        "targetExpression": TARGET_EXPRESSION,
        "targetReceiver": TARGET_RECEIVER,
        "targetInterval": "Set.Icc (0 : Real) ((1 : Real) / 10)",
        "preserveCancellation": True,
        "checkedSupport": checked_support,
        "missingArtifacts": missing_artifacts,
        "payloadLedger": rel(PAYLOAD_LEDGER),
        "payloadLedgerExactCoefficientSource": exact_source,
        "noPilotComputationReason": (
            None
            if source_data_ready
            else "complete same-target coefficient/remainder source data is absent"
        ),
        "proofTruth": {
            "step33A1AClosed": False,
            "directConcretePayloadWritten": DIRECT_CONCRETE_PAYLOAD_FILE.exists(),
            "acceptedPilotVerdictProduced": False,
            "numericSamplingUsedAsProof": False,
            "leanFilesModified": False,
        },
        "nextCertificateInterface": {
            "preferred": "interval_or_rational_source_interval_rows",
            "receiver": SOURCE_INTERVAL_RECEIVER,
            "alternative": DIRECT_HORNER_VALID,
            "mustInclude": [
                "exact segment cover of Set.Icc 0 (1/10)",
                "same-target collapsedExpression coefficients",
                "proof-grade remainder rows per segment",
                "Horner lower/upper rows if using the Horner receiver",
                "final +/- BiasedResidualRemainderAbs budget rows",
            ],
        },
        "nextImplementablePatch": next_patch,
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Whole-Expression Pilot Source-Data Gate",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"status: `{ledger['status']}`",
        f"phase2ResultNow: `{ledger['phase2ResultNow']}`",
        f"pilotVerdict: `{ledger['pilotVerdict']}`",
        f"proofGrade: `{ledger['proofGrade']}`",
        f"sourceDataReady: `{ledger['sourceDataReady']}`",
        f"currentGap: `{ledger['currentGap']}`",
        "",
        "## Target",
        "",
        f"- expression: `{ledger['targetExpression']}`",
        f"- receiver: `{ledger['targetReceiver']}`",
        f"- interval: `{ledger['targetInterval']}`",
        f"- preserveCancellation: `{ledger['preserveCancellation']}`",
        "",
        "## Accepted Pilot Verdicts",
        "",
    ]
    for verdict in ledger["acceptedPilotVerdicts"]:
        lines.append(f"- `{verdict}`")
    lines.extend(
        [
            "",
            "This run produced none of those verdicts because the required "
            "whole-expression source data is not present.",
            "",
            "## Missing Artifacts",
            "",
        ]
    )
    for item in ledger["missingArtifacts"]:
        lines.extend(
            [
                f"### {item['id']}",
                "",
                f"- present: `{item['present']}`",
                f"- required: {item['required']}",
            ]
        )
        if "theorem" in item:
            lines.append(f"- theorem: `{item['theorem']}`")
        if "file" in item:
            lines.append(f"- file: `{item['file']}`")
        if "currentEvidence" in item:
            lines.append(f"- currentEvidence: `{item['currentEvidence']}`")
        if "acceptedInterfaces" in item:
            for interface in item["acceptedInterfaces"]:
                lines.append(f"- acceptedInterface: `{interface}`")
        lines.append("")

    lines.extend(
        [
            "## Checked Support",
            "",
        ]
    )
    for name, support in ledger["checkedSupport"].items():
        lines.extend(
            [
                f"### {name}",
                "",
                f"- file: `{support['file']}`",
                f"- exists: `{support['exists']}`",
            ]
        )
        for symbol, present in support["symbols"].items():
            lines.append(f"- `{symbol}`: `{present}`")
        lines.append("")

    source = ledger["payloadLedgerExactCoefficientSource"]
    lines.extend(
        [
            "## Payload Ledger Source Status",
            "",
            f"- payloadLedger: `{ledger['payloadLedger']}`",
            f"- exactCoefficientSource.status: `{source.get('status')}`",
        ]
    )
    for note in source.get("notes", []):
        lines.append(f"- note: {note}")

    lines.extend(
        [
            "",
            "## Next Certificate Interface",
            "",
            f"- preferred: `{ledger['nextCertificateInterface']['preferred']}`",
            f"- receiver: `{ledger['nextCertificateInterface']['receiver']}`",
            f"- alternative: `{ledger['nextCertificateInterface']['alternative']}`",
        ]
    )
    for req in ledger["nextCertificateInterface"]["mustInclude"]:
        lines.append(f"- mustInclude: {req}")

    lines.extend(
        [
            "",
            "## Proof Truth",
            "",
        ]
    )
    for key, value in ledger["proofTruth"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Next Patch",
            "",
            ledger["nextImplementablePatch"],
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    ledger = build_ledger()
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(
        f"{ledger['phase2ResultNow']} {ledger['currentGap']} "
        f"sourceDataReady={ledger['sourceDataReady']}"
    )


if __name__ == "__main__":
    main()
