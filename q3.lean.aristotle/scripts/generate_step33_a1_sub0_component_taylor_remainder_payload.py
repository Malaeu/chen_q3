#!/usr/bin/env python3
"""Fail-closed Step33A.1-A sub0 component Taylor remainder ledger.

This is deliberately not a Lean payload generator.  It inventories the exact
coefficient assembly, the available active-actual row machinery, and the
existing formal coarse P45 bridge.  The coarse bridge is not spendable for
Step33A.1-A because its symmetric error budget is killed by the local rational
budget check.  Therefore this generator stops unless sharper proof-grade signed
rows for

  RawIntegrandDerivClosedForm eta - P_45(AssembledRawDerivCoeff)(eta)

on the whole sub0 cell are present together with an exact budget comparison.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUESTS = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

OUT_JSON = REQUESTS / "step33_a1_sub0_component_taylor_remainder_payload.json"
OUT_MD = REQUESTS / "step33_a1_sub0_component_taylor_remainder_payload.md"

COMPONENT_RESIDUAL_JSON = (
    REQUESTS / "step33_a1_sub0_component_taylor_residual_payload.json"
)
EXACT_ASSEMBLY_JSON = (
    REQUESTS / "step33_a1_sub0_component_taylor_exact_assembly_certificate.json"
)
COMBINED_INTERVAL_JSON = (
    REQUESTS / "step33_a1_sub0_combined_cancellation_interval_certificate.json"
)

COEFF_PAYLOAD_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean"
)
ACTIVE_ACTUAL_ROWS_LEAN = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean"
)
SOURCE_NORMAL_FORM_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean"
)
SOURCE_INTERVAL_CERT_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean"
)
P45_BRIDGE_LEAN = PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean"
TIGHT_PRODUCT_SOURCE_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorTightProductSource.lean"
)
TIGHT_BUDGET_KILL_LEAN = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorTightBudgetKill.lean"
)

SCHEMA = "q3_psdpd_step33_a1_sub0_component_taylor_remainder_payload.v2"
STATUS = "fail_closed_component_taylor_remainder_coarse_source_budget_killed"
FIRST_FAILURE = "STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_BUDGET_CONSTANT_FAIL"
SHARPER_ROW_FAILURE = (
    "STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SHARPER_SIGNED_ROW_SOURCE_GAP"
)
BUDGET_FAILURE = "STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_BUDGET_CONSTANT_FAIL"

TARGET_LEAN_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorRemainderPayload.lean"
)
SOURCE_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_componentTaylor_remainder_source_generated"
)
TRANSPORT_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure_generated"
)
COARSE_SOURCE_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightAssembledSource"
)
COARSE_TRANSPORT_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_tight_enclosure"
)
COARSE_BUDGET_KILL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_tightProductAssemblyErrorBudget_width_fail"
)
COARSE_BUDGET_NAME = (
    "primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget"
)


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def find_symbol(path: Path, symbol: str) -> dict[str, Any]:
    if not path.exists():
        return {"file": rel(path), "symbol": symbol, "exists": False, "line": None}
    for idx, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if symbol in line:
            return {"file": rel(path), "symbol": symbol, "exists": True, "line": idx}
    return {"file": rel(path), "symbol": symbol, "exists": False, "line": None}


def value_at(data: dict[str, Any], path: list[str], default: Any = None) -> Any:
    cur: Any = data
    for key in path:
        if not isinstance(cur, dict) or key not in cur:
            return default
        cur = cur[key]
    return cur


def list_len(value: Any) -> int | None:
    return len(value) if isinstance(value, list) else None


def build_payload() -> dict[str, Any]:
    component = load_json(COMPONENT_RESIDUAL_JSON)
    assembly = load_json(EXACT_ASSEMBLY_JSON)
    combined = load_json(COMBINED_INTERVAL_JSON)

    assembled = value_at(assembly, ["generatorFields", "assembledRawDerivCoeff"], [])
    residual = value_at(assembly, ["generatorFields", "residualTaylorCoeff"], [])
    component_route = component.get("componentTaylorRemainderRouteReview", {})
    combined_status = combined.get("proofStatus", {})

    coefficient_assembly_ready = (
        assembly.get("schema")
        == "q3_psdpd_step33_a1_sub0_component_taylor_exact_assembly_certificate.v1"
        and list_len(assembled) == 46
        and list_len(residual) == 46
        and value_at(assembly, ["checks", "algebraicAssemblyCrosswalkPassed"]) is True
    )

    active_actual_rows_ready = all(
        combined_status.get(key) is True
        for key in [
            "activeActualCenterJetRowsFilePresent",
            "activeActualFactorIntervalReceiverPresent",
            "activeActualProductRowIntervalsPresent",
            "activeActualCenterRowIntervalFromFactorRowsPresent",
        ]
    )

    coarse_source_symbols = [
        find_symbol(P45_BRIDGE_LEAN, COARSE_SOURCE_THEOREM),
        find_symbol(P45_BRIDGE_LEAN, COARSE_TRANSPORT_THEOREM),
        find_symbol(TIGHT_PRODUCT_SOURCE_LEAN, COARSE_BUDGET_NAME),
        find_symbol(TIGHT_BUDGET_KILL_LEAN, COARSE_BUDGET_KILL_THEOREM),
    ]
    coarse_source_ready = all(symbol["exists"] for symbol in coarse_source_symbols[:3])
    coarse_budget_kill_ready = coarse_source_symbols[3]["exists"]

    exact_budget_ready = False
    signed_rows_ready = False
    proof_grade = coefficient_assembly_ready and signed_rows_ready and exact_budget_ready

    required_rows = [
        {
            "id": "R0_exact_degree45_assembly_coefficients",
            "status": "FORMAL_PAYLOAD_LIST_EQ_ONLY"
            if coefficient_assembly_ready
            else "GAP",
            "artifact": rel(COEFF_PAYLOAD_LEAN),
            "notes": (
                "Lean list equalities materialize AssembledRawDerivCoeff and "
                "ResidualTaylorCoeff, but they do not bound the analytic "
                "component remainder."
            ),
        },
        {
            "id": "R1_active_actual_center_row_intervals",
            "status": "FORMAL_INPUT_CANDIDATE" if active_actual_rows_ready else "GAP",
            "artifact": rel(ACTIVE_ACTUAL_ROWS_LEAN),
            "notes": (
                "Rows are only center-jet row intervals for the activeActual "
                "source-model layer in degrees 0..15 after model subtraction. "
                "They are not yet the whole-cell bound for ActualComponent - "
                "P45(AssembledRawDerivCoeff)."
            ),
        },
        {
            "id": "R2_direct_signed_component_remainder_rows",
            "status": "FORMAL_COARSE_SOURCE_PRESENT_BUDGET_KILLED"
            if coarse_source_ready and coarse_budget_kill_ready
            else "GAP",
            "artifact": rel(P45_BRIDGE_LEAN),
            "notes": (
                "A formal coarse P45 source exists for "
                "RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial "
                "45 (1/20) AssembledRawDerivCoeff eta on Set.Icc 0 (1/10), "
                f"bounded by {COARSE_BUDGET_NAME}.  The local budget-kill "
                "file proves this coarse symmetric budget is too wide, so "
                "sharper signed rows are still missing for closure."
            ),
        },
        {
            "id": "R3_componentPropagationRemainderAbs",
            "status": "FORMAL_COARSE_CANDIDATE_BUDGET_KILLED"
            if coarse_source_ready and coarse_budget_kill_ready
            else "GAP",
            "artifact": rel(P45_BRIDGE_LEAN),
            "notes": (
                f"The available candidate is {COARSE_BUDGET_NAME}; it is "
                "formal, but not spendable as the final component remainder "
                "budget because the exact budget comparison fails."
            ),
        },
        {
            "id": "R4_residualTaylorRemainderAbs",
            "status": "FORMAL_COARSE_CANDIDATE_BUDGET_KILLED"
            if coarse_source_ready and coarse_budget_kill_ready
            else "GAP",
            "artifact": rel(P45_BRIDGE_LEAN),
            "notes": (
                f"{COARSE_TRANSPORT_THEOREM} transports the coarse source into "
                "the residual derivative enclosure, but it carries the same "
                "budget-killed coarse constant."
            ),
        },
        {
            "id": "R5_exact_rational_budget_comparison",
            "status": "FORMAL_FAIL_COARSE_SOURCE"
            if coarse_budget_kill_ready
            else "GAP",
            "artifact": rel(TIGHT_BUDGET_KILL_LEAN),
            "notes": (
                f"{COARSE_BUDGET_KILL_THEOREM} proves the coarse source width "
                "exceeds the target interval width, so the first failure for "
                f"the current local source is {BUDGET_FAILURE}."
            ),
        },
    ]

    return {
        "schema": SCHEMA,
        "status": STATUS,
        "firstFailure": FIRST_FAILURE,
        "failureCodeIfBudgetFalse": BUDGET_FAILURE,
        "proofGrade": proof_grade,
        "leanPayloadWritten": False,
        "doNotWriteLeanPayloadYet": True,
        "advisoryRouteReview": {
            "source": component_route.get(
                "source", "Computer Use / Proshka route review 2026-06-23"
            ),
            "recommendedOption": component_route.get("recommendedOption", "B"),
            "advisoryOnly": True,
            "proofClaimAllowedNow": False,
        },
        "target": {
            "leanFile": TARGET_LEAN_FILE,
            "firstTheoremObject": SOURCE_THEOREM,
            "transportTheoremObject": TRANSPORT_THEOREM,
            "cell": "Set.Icc (0 : Real) ((1 : Real) / 10)",
            "center": "1/20",
            "assembledDegree": 45,
            "targetExpressionAscii": (
                "primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta "
                "- rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20) "
                "primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta"
            ),
            "requiredConclusion": (
                "|targetExpression eta| <= ComponentPropagationRemainderAbs, "
                "then transport to ResidualTaylorRemainderAbs"
            ),
        },
        "inputs": {
            "coefficientAssembly": {
                "path": rel(EXACT_ASSEMBLY_JSON),
                "schema": assembly.get("schema"),
                "status": assembly.get("status"),
                "firstFailure": assembly.get("firstFailure"),
                "assembledRawDerivCoeffLength": list_len(assembled),
                "residualTaylorCoeffLength": list_len(residual),
                "algebraicAssemblyCrosswalkPassed": value_at(
                    assembly, ["checks", "algebraicAssemblyCrosswalkPassed"]
                ),
                "componentTaylorProofsPresent": value_at(
                    assembly, ["checks", "componentTaylorProofsPresent"]
                ),
                "residualTaylorRemainderAbs": value_at(
                    assembly, ["generatorFields", "residualTaylorRemainderAbs"]
                ),
                "componentPropagationRemainderAbs": value_at(
                    assembly, ["generatorFields", "componentPropagationRemainderAbs"]
                ),
            },
            "componentResidualLedger": {
                "path": rel(COMPONENT_RESIDUAL_JSON),
                "schema": component.get("schema"),
                "status": component.get("status"),
                "firstFailure": component.get("firstFailure"),
                "componentTaylorRemainder": component.get("componentTaylorRemainder"),
            },
            "activeActualCandidate": {
                "path": rel(ACTIVE_ACTUAL_ROWS_LEAN),
                "proofStatusKeys": {
                    key: combined_status.get(key)
                    for key in [
                        "activeActualCenterJetRowsFilePresent",
                        "activeActualFactorIntervalReceiverPresent",
                        "activeActualProductRowIntervalsPresent",
                        "activeActualCenterRowIntervalFromFactorRowsPresent",
                        "sourceNormalFormActiveActualSourceIntervalValidPresent",
                        "sourceIntervalCertToResidualIntervalPresent",
                    ]
                },
                "limitation": (
                    "This is a source-model center-jet interval layer, not a "
                    "whole-cell degree-45 component Taylor remainder proof."
                ),
            },
            "coarseP45Source": {
                "path": rel(P45_BRIDGE_LEAN),
                "budgetSourcePath": rel(TIGHT_PRODUCT_SOURCE_LEAN),
                "budgetKillPath": rel(TIGHT_BUDGET_KILL_LEAN),
                "sourceTheorem": COARSE_SOURCE_THEOREM,
                "transportTheorem": COARSE_TRANSPORT_THEOREM,
                "budgetName": COARSE_BUDGET_NAME,
                "budgetKillTheorem": COARSE_BUDGET_KILL_THEOREM,
                "sourceReady": coarse_source_ready,
                "budgetKillReady": coarse_budget_kill_ready,
                "spendableForStep33A1A": False,
                "limitation": (
                    "This is a formal coarse P45 source and a formal negative "
                    "budget comparison.  It is alive as source evidence, but "
                    "not a closing Step33A.1-A certificate."
                ),
            },
        },
        "symbolInventory": {
            "coefficientPayload": [
                find_symbol(
                    COEFF_PAYLOAD_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeffPayload",
                ),
                find_symbol(
                    COEFF_PAYLOAD_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffPayload",
                ),
                find_symbol(
                    COEFF_PAYLOAD_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_payload_eq",
                ),
                find_symbol(
                    COEFF_PAYLOAD_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0_residualTaylorCoeff_payload_eq",
                ),
            ],
            "activeActualRows": [
                find_symbol(
                    ACTIVE_ACTUAL_ROWS_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower",
                ),
                find_symbol(
                    ACTIVE_ACTUAL_ROWS_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper",
                ),
                find_symbol(
                    ACTIVE_ACTUAL_ROWS_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows",
                ),
            ],
            "sourceNormalForm": [
                find_symbol(
                    SOURCE_NORMAL_FORM_LEAN,
                    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceIntervalValid_of_activeActual_interval",
                ),
                find_symbol(
                    SOURCE_INTERVAL_CERT_LEAN,
                    "theorem to_fullTaylor_residual_deriv_interval",
                ),
            ],
            "coarseP45Bridge": coarse_source_symbols,
            "missingGeneratedTarget": [
                find_symbol(COEFF_PAYLOAD_LEAN, SOURCE_THEOREM),
                find_symbol(ACTIVE_ACTUAL_ROWS_LEAN, SOURCE_THEOREM),
                find_symbol(P45_BRIDGE_LEAN, SOURCE_THEOREM),
                find_symbol(P45_BRIDGE_LEAN, TRANSPORT_THEOREM),
            ],
        },
        "requiredRows": required_rows,
        "whyExistingArtifactsAreNotEnough": [
            (
                "Exact coefficient assembly is algebraic and proof-checked as "
                "list equality, but it gives no analytic remainder bound."
            ),
            (
                "The activeActual rows are degree-0..15 source-model center-jet "
                "intervals after residual model subtraction; the requested "
                "component remainder is a whole-cell degree-45 error against "
                "AssembledRawDerivCoeff."
            ),
            (
                "The combined/source interval certificates route residual "
                "derivative intervals, but the current component ledger still "
                "has ComponentPropagationRemainderAbs and "
                "ResidualTaylorRemainderAbs set to null."
            ),
            (
                f"{COARSE_SOURCE_THEOREM} and {COARSE_TRANSPORT_THEOREM} give "
                "a formal coarse P45 source, but "
                f"{COARSE_BUDGET_KILL_THEOREM} proves the carried coarse "
                "budget is too wide for the target residual interval."
            ),
            (
                "No local file currently defines the generated sharper objects "
                f"{SOURCE_THEOREM} or {TRANSPORT_THEOREM}; those names remain "
                "reserved until sharper signed rows and their exact budget "
                "comparison pass."
            ),
        ],
        "nextImplementablePatch": {
            "action": "build_sharper_component_taylor_remainder_interval_generator",
            "description": (
                "Generate sharper rational/interval signed rows for the exact "
                "target expression, compute a smaller "
                "ComponentPropagationRemainderAbs plus "
                "ResidualTaylorRemainderAbs, and keep Lean output disabled "
                "until all rows and the exact rational budget comparison pass."
            ),
            "ifRowsMissing": SHARPER_ROW_FAILURE,
            "ifBudgetFalse": BUDGET_FAILURE,
        },
        "sourceHashes": {
            rel(COMPONENT_RESIDUAL_JSON): file_hash(COMPONENT_RESIDUAL_JSON),
            rel(EXACT_ASSEMBLY_JSON): file_hash(EXACT_ASSEMBLY_JSON),
            rel(COMBINED_INTERVAL_JSON): file_hash(COMBINED_INTERVAL_JSON),
            rel(COEFF_PAYLOAD_LEAN): file_hash(COEFF_PAYLOAD_LEAN),
            rel(ACTIVE_ACTUAL_ROWS_LEAN): file_hash(ACTIVE_ACTUAL_ROWS_LEAN),
            rel(P45_BRIDGE_LEAN): file_hash(P45_BRIDGE_LEAN),
            rel(TIGHT_PRODUCT_SOURCE_LEAN): file_hash(TIGHT_PRODUCT_SOURCE_LEAN),
            rel(TIGHT_BUDGET_KILL_LEAN): file_hash(TIGHT_BUDGET_KILL_LEAN),
        },
    }


def render_markdown(payload: dict[str, Any]) -> str:
    rows = payload["requiredRows"]
    lines = [
        "# Step33A.1-A sub0 component Taylor remainder payload",
        "",
        "## Status",
        "",
        f"- schema: `{payload['schema']}`",
        f"- status: `{payload['status']}`",
        f"- firstFailure: `{payload['firstFailure']}`",
        f"- proofGrade: `{payload['proofGrade']}`",
        f"- leanPayloadWritten: `{payload['leanPayloadWritten']}`",
        f"- target Lean file: `{payload['target']['leanFile']}`",
        f"- first theorem/object: `{payload['target']['firstTheoremObject']}`",
        f"- transport theorem/object: `{payload['target']['transportTheoremObject']}`",
        "",
        "## Target expression",
        "",
        "```text",
        payload["target"]["targetExpressionAscii"],
        "```",
        "",
        f"- cell: `{payload['target']['cell']}`",
        f"- center: `{payload['target']['center']}`",
        f"- assembledDegree: `{payload['target']['assembledDegree']}`",
        f"- required conclusion: `{payload['target']['requiredConclusion']}`",
        "",
        "## Available inputs",
        "",
        "### Coefficient assembly",
        "",
    ]

    coeff = payload["inputs"]["coefficientAssembly"]
    for key in [
        "path",
        "schema",
        "status",
        "firstFailure",
        "assembledRawDerivCoeffLength",
        "residualTaylorCoeffLength",
        "algebraicAssemblyCrosswalkPassed",
        "componentTaylorProofsPresent",
        "residualTaylorRemainderAbs",
        "componentPropagationRemainderAbs",
    ]:
        lines.append(f"- {key}: `{coeff.get(key)}`")

    lines.extend(["", "### Active-actual candidate", ""])
    active = payload["inputs"]["activeActualCandidate"]
    lines.append(f"- path: `{active['path']}`")
    for key, value in active["proofStatusKeys"].items():
        lines.append(f"- {key}: `{value}`")
    lines.append(f"- limitation: {active['limitation']}")

    lines.extend(["", "### Coarse P45 source", ""])
    coarse = payload["inputs"]["coarseP45Source"]
    for key in [
        "path",
        "budgetSourcePath",
        "budgetKillPath",
        "sourceTheorem",
        "transportTheorem",
        "budgetName",
        "budgetKillTheorem",
        "sourceReady",
        "budgetKillReady",
        "spendableForStep33A1A",
    ]:
        lines.append(f"- {key}: `{coarse.get(key)}`")
    lines.append(f"- limitation: {coarse['limitation']}")

    lines.extend(["", "## Required rows", ""])
    for row in rows:
        lines.extend(
            [
                f"### {row['id']}",
                "",
                f"- status: `{row['status']}`",
                f"- artifact: `{row['artifact']}`",
                f"- notes: {row['notes']}",
                "",
            ]
        )

    lines.extend(["## Why existing artifacts are not enough", ""])
    for item in payload["whyExistingArtifactsAreNotEnough"]:
        lines.append(f"- {item}")

    lines.extend(["", "## Symbol inventory", ""])
    for group, symbols in payload["symbolInventory"].items():
        lines.append(f"### {group}")
        lines.append("")
        for symbol in symbols:
            lines.append(
                "- `{symbol}`: exists=`{exists}`, file=`{file}`, line=`{line}`".format(
                    **symbol
                )
            )
        lines.append("")

    next_patch = payload["nextImplementablePatch"]
    lines.extend(
        [
            "## Next implementable patch",
            "",
            f"- action: `{next_patch['action']}`",
            f"- ifRowsMissing: `{next_patch['ifRowsMissing']}`",
            f"- ifBudgetFalse: `{next_patch['ifBudgetFalse']}`",
            f"- description: {next_patch['description']}",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    payload = build_payload()
    OUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    OUT_MD.write_text(render_markdown(payload), encoding="utf-8")
    print(f"wrote {rel(OUT_JSON)}")
    print(f"wrote {rel(OUT_MD)}")
    print(f"firstFailure={payload['firstFailure']}")


if __name__ == "__main__":
    main()
