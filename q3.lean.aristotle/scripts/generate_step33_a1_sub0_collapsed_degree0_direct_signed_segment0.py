#!/usr/bin/env python3
"""Fail-closed segment0 Taylor-model gate for the direct signed source.

The active Step33A.1-A route needs a proof-grade interval row for the already
subtracted signed expression

    ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)

on the first segment.  This generator records the exact object selected by the
Browser/Computer Use Proshka review and refuses to emit Lean unless the local
repository contains a whole-expression Taylor-model source:

    modelCoeff : Fin 29 -> Rat
    remainderAbs : Rat
    theorem bounding SignedSourceExpr - rawOmegaATaylorPolynomial 28 center coeff

No sampled rows, point rows, factorwise raw-D17 budget, or conditional Lean
payload is accepted here.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_collapsed_degree0_"
    "direct_signed_segment0_taylor_model_gate.v4"
)
ROUTE = "collapsed_degree0_direct_signed_segment0_taylor_model"
PROOF_STATUS = "fail_closed_missing_local_factor_taylor18_segment0_payload"
CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "LOCAL_FACTOR_TAYLOR18_SEGMENT0_PAYLOAD_GAP"
)
PREVIOUS_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "DIRECT_SIGNED_SEGMENT0_TAYLOR_MODEL_SOURCE_GAP"
)
PARENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POLY_DERIV_SIGNED_SOURCE_GAP"
)
BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "DIRECT_SIGNED_SEGMENT0_BUDGET_CONSTANT_FAIL"
)
UNIFORM_SEGMENT_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP"
)
LOCAL_FACTOR_TO_WHOLE_EXPR_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "LOCAL_FACTOR_JETS_TO_WHOLE_EXPRESSION_TAYLOR_MODEL_GAP"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

SIGNED_SOURCE_RECEIVER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0SignedSourcePayload.lean"
)
NOMINAL_POLY_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0NominalPolyDerivRows.lean"
)
RAW_D17_SHARP_LOCAL_JETS_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean"
)
ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellation"
    "ActiveActualCenterJetRowsPayload.lean"
)
COMPONENT_TAYLOR_COEFF_ASSEMBLY_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean"
)
CENTERED_TAYLOR_DERIV_MAJORANT18_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant18.lean"
)
CENTERED_TAYLOR_DERIV_POINT_INTERVAL18_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18.lean"
)
CENTERED_TAYLOR_DERIV_MODEL18_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeModel18.lean"
)
LOCAL_FACTOR_TAYLOR_MODEL_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0LocalFactorTaylorModelBridge.lean"
)
RAWPRODUCT18_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ActiveActualRawProduct18Source.lean"
)
RAW_D17_SIGNED_FACTOR_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorRows.lean"
)
RAW_D17_SIGNED_FACTOR_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0RawD17SignedFactorPayload.lean"
)
DIRECT_SOURCE_ROWS_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_collapsed_degree0_direct_signed_source_rows.json"
)
COMPONENT_EXACT_ASSEMBLY_CERT = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_exact_assembly_certificate.json"
)
COMPONENT_ASSEMBLY_STREAM_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_component_assembly_stream_ledger.json"
)
COMPONENT_TAYLOR_RESIDUAL_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
TARGET_LEAN_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "CollapsedDegree0DirectSignedSourceSegment0Payload.lean"
)

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_direct_signed_segment0_taylor_model.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_collapsed_degree0_direct_signed_segment0_taylor_model.md"
)

MODEL_REMAINDER_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "collapsedDegree0_signedSource_segment0_model_remainder_generated"
)
SEGMENT_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "collapsedDegree0_signedSource_segment0_interval_generated"
)
MODEL_COEFF_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0"
    "CollapsedDegree0Segment0ModelCoeff"
)
MODEL_REMAINDER_DEF = (
    "primaryFiniteRow0Parent0Split100Sub0"
    "CollapsedDegree0Segment0ModelRemainderAbs"
)

PROSHKA_REVIEW = {
    "used": True,
    "source": "in-app Browser/Computer Use Proshka route review",
    "status": "answered",
    "latestVisibleAnswerUsed": True,
    "nextPatch": (
        "direct segment-0 Taylor-model certificate for the complete "
        "already-subtracted signed expression"
    ),
    "firstScript": (
        "scripts/generate_step33_a1_sub0_collapsed_degree0_"
        "direct_signed_segment0.py"
    ),
    "firstLeanFile": (
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
        "CollapsedDegree0DirectSignedSourceSegment0Payload.lean"
    ),
    "firstGeneratedArtifact": (
        "ACTIVE/requests/step33_bootstrap/"
        "step33_a1_sub0_collapsed_degree0_direct_signed_segment0_"
        "taylor_model.json"
    ),
    "firstGenericLeanBridge": (
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeModel18.lean"
    ),
    "followupChoice": "C",
    "followupFirstFile": (
        "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
        "CollapsedDegree0LocalFactorTaylorModelBridge.lean"
    ),
    "modelRemainderTheorem": MODEL_REMAINDER_THEOREM,
    "segmentIntervalTheorem": SEGMENT_INTERVAL_THEOREM,
    "failureCode": CURRENT_GAP,
    "failureCodeIfNotProducibleNow": LOCAL_FACTOR_TO_WHOLE_EXPR_GAP,
    "budgetFailureCode": BUDGET_FAIL,
    "exactExistingTheoremsSeen": [
        "primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_sharp_interval_generated",
        "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_sharp_interval_generated",
        "iteratedDeriv_norm_le_centeredTaylorDerivMajorant18",
        "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz",
        "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18",
        "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly",
        "primaryFiniteRow0Parent0Split100Sub0_activeScale_mem_tightInterval",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_signedSource_segment0_remainder_of_localFactorTaylor18"
        ),
    ],
}

SUPPORT_SYMBOLS: dict[Path, list[str]] = {
    SIGNED_SOURCE_RECEIVER_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr",
        "Step33Sub0CollapsedDegree0SignedSourceSegmentCert",
        "Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert",
    ],
    NOMINAL_POLY_ROWS_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "nominalOrder16Poly_deriv_segment_interval_generated"
        ),
    ],
    RAW_D17_SHARP_LOCAL_JETS_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat",
        "primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_localCenterJet18_sharp_interval"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_localCenterJet18_sharp_interval"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "omegaActual_derivative_twoSegment_sharp_interval"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "shapeSqActual_derivative_twoSegment_sharp_interval"
        ),
        "primaryFiniteRow0Parent0Split100Sub0_omegaActual_order18_on_rawD17Segment_sharp",
        "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_on_rawD17Segment_sharp",
    ],
    ACTIVE_ACTUAL_CENTER_JET_ROWS_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows",
        "primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval",
        "primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval",
    ],
    COMPONENT_TAYLOR_COEFF_ASSEMBLY_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff",
        "primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff",
        "primaryFiniteRow0Parent0Split100Sub0OmegaShapeSqDerivProductCoeff",
    ],
    CENTERED_TAYLOR_DERIV_MAJORANT18_FILE: [
        "centeredTaylorDerivMajorant18",
        "iteratedDeriv_norm_le_centeredTaylorDerivMajorant18",
    ],
    CENTERED_TAYLOR_DERIV_POINT_INTERVAL18_FILE: [
        "centeredTaylorDerivPointLower18",
        "centeredTaylorDerivPointUpper18",
        "iteratedDeriv_mem_Icc_of_centerJet18_point_remainder",
    ],
    CENTERED_TAYLOR_DERIV_MODEL18_FILE: [
        "centeredTaylorDerivPolynomial18",
        "centeredTaylorDerivError18",
        "centeredTaylorDerivPolynomial18_abs_bound",
        "iteratedDeriv_sub_centeredTaylorDerivPolynomial18_norm_le",
    ],
    LOCAL_FACTOR_TAYLOR_MODEL_BRIDGE_FILE: [
        "Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert",
        "structure Valid",
        "to_rawD17SignedFactorSegmentValid",
        "to_rawPolySegmentValid",
        "to_signedSegmentValid",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_signedSource_segment0_remainder_of_localFactorTaylor18"
        ),
    ],
    RAWPRODUCT18_SOURCE_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_generated",
        "primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_generated",
    ],
    RAW_D17_SIGNED_FACTOR_ROWS_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawProductActual_order18_eq_signedLeibniz"
        ),
        "Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
        ),
    ],
    RAW_D17_SIGNED_FACTOR_PAYLOAD_FILE: [
        "primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0",
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_valid"
        ),
        (
            "primaryFiniteRow0Parent0Split100Sub0_"
            "rawD17_signedFactor_segment0_budget_not_spendable"
        ),
    ],
}

TARGET_SYMBOLS = [
    SEGMENT_INTERVAL_THEOREM,
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_directSignedSource_segment0_valid_generated"
    ),
]

SOURCE_MATERIAL_AUDIT = {
    "firstUnmetInput": "full_segment_family_cover_and_derivAbs_degree0_budget_rows",
    "usableSupport": [
        (
            "local signed factor center-jet intervals at 1/40 and 3/40, "
            "plus factor order18 bounds"
        ),
        (
            "signed Leibniz equality/receiver for raw-D17 factor segments"
        ),
        (
            "nominal polynomial derivative interval rows in the target "
            "subtraction"
        ),
        "signed-source segment-family receiver and final degree-0 bridge",
        (
            "Lean-checked local factor Taylor18 bridge from segment0 factor "
            "models into the signed-source segment receiver"
        ),
    ],
    "nowProofCargo": [
        (
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
            "CollapsedDegree0LocalFactorTaylorModelPayload.lean"
        ),
        (
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
            "CollapsedDegree0DirectSignedSourceSegment0Payload.lean"
        ),
        SEGMENT_INTERVAL_THEOREM,
    ],
    "notYetProofCargo": [
        "final segment-family cover, derivAbs budget, and degree-0 budget rows",
    ],
    "whyExistingRowsAreInsufficient": (
        "The segment0 interval row is Lean-checked.  It still covers only "
        "`[0, 1/20]` and does not provide the full segment-family cover, the "
        "global `derivAbs` containment, or the degree-0 budget row.  Point "
        "rows, factorwise intervals, and budget-killed raw-D17 payloads do "
        "not provide those missing rows."
    ),
}

REQUIRED_DATA = [
    {
        "id": "cell",
        "needed": "cellL=0, cellU=1/20, center=1/40, radius=1/40",
        "status": "specified",
    },
    {
        "id": "signed_center_jets",
        "needed": (
            "OmegaActual and ShapeSqActual signed center jets sufficient to "
            "assemble the complete D17 product row before interval widening"
        ),
        "status": "partial_support_only",
    },
    {
        "id": "uniform_order18_bounds",
        "needed": "uniform order18 bounds for the factors on segment0",
        "status": "support_present_but_not_whole_expression_source",
    },
    {
        "id": "signed_leibniz_assembly",
        "needed": (
            "exact signed Leibniz assembly for the product-derivative and "
            "remainder terms underlying activeScale * "
            "D17(ComponentProductActual) - deriv(NominalOrder16Poly)"
        ),
        "status": "checked_for_segment0",
        "failureCode": None,
    },
    {
        "id": "whole_expression_model",
        "needed": (
            "concrete LocalFactorTaylor18Segment0Cert rows producing the "
            "same-segment signed-source interval"
        ),
        "status": "checked_for_segment0_via_local_factor_taylor18_payload",
        "failureCode": None,
    },
    {
        "id": "whole_expression_remainder",
        "needed": (
            "derived segment0 sourceLower/sourceUpper plus final derivAbs and "
            "degree-0 budget rows"
        ),
        "status": "blocked_until_uniform_family_and_budget_rows_exist",
        "failureCode": UNIFORM_SEGMENT_ROWS_GAP,
    },
    {
        "id": "horner_interval",
        "needed": "Horner stageLower/stageUpper, modelLower/modelUpper",
        "status": "blocked_until_model_exists",
    },
    {
        "id": "final_source_interval",
        "needed": "final sourceLower/sourceUpper for SignedSourceExpr",
        "status": "blocked_until_model_exists",
    },
]

DO_NOT_USE = [
    "independent Omega/ShapeSq final intervals",
    "raw-D17 factorwise budget",
    "RawProduct18 symmetric majorant",
    "activeActual-alone norm budget",
    "P45 / zero-model budgets",
    "sampled or floating-point rows",
    "point rows as uniform segment rows",
    "manual row-by-row Lean replay",
    "conditional Payload.lean fields",
]


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected JSON object root")
    return data


def sha256_file(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def line_of(text: str, needle: str) -> int | None:
    for idx, line in enumerate(text.splitlines(), start=1):
        if needle in line:
            return idx
    return None


def symbol_audit(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
    text = read_text(path)
    return {
        symbol: {"present": symbol in text, "line": line_of(text, symbol)}
        for symbol in symbols
    }


def all_present(audit: dict[str, dict[str, Any]]) -> bool:
    return all(row["present"] for row in audit.values())


def nested_get(data: dict[str, Any], path: list[str]) -> Any:
    current: Any = data
    for key in path:
        if not isinstance(current, dict):
            return None
        current = current.get(key)
    return current


def field_summary(value: Any) -> dict[str, Any]:
    if isinstance(value, list):
        return {
            "present": True,
            "kind": "list",
            "length": len(value),
        }
    return {
        "present": value is not None,
        "kind": type(value).__name__ if value is not None else "missing",
        "value": value,
    }


def build_component_assembly_audit() -> dict[str, Any]:
    exact = load_json(COMPONENT_EXACT_ASSEMBLY_CERT)
    stream = load_json(COMPONENT_ASSEMBLY_STREAM_LEDGER)
    residual = load_json(COMPONENT_TAYLOR_RESIDUAL_PAYLOAD)
    exact_fields = nested_get(exact, ["generatorFields"]) or {}
    residual_fields = nested_get(residual, ["generatorFields"]) or {}
    formula = nested_get(stream, ["componentAssemblyFormula"]) or {}
    proof_status = nested_get(residual, ["proofStatus"]) or {}
    return {
        "verdict": "support_present_but_not_segment0_whole_expression_source",
        "segment0Target": {
            "cellL": "0",
            "cellU": "1/20",
            "center": "1/40",
            "radius": "1/40",
        },
        "componentAssemblyFormula": {
            "center": formula.get("center"),
            "statementAscii": formula.get("statementAscii"),
            "residualTaylorCoeffFormula": formula.get("residualTaylorCoeffFormula"),
        },
        "centerCrosswalkStatus": (
            "missing: available component assembly is centered at 1/20; "
            "the active segment0 target is centered at 1/40"
        ),
        "exactAssemblyCertificate": {
            "path": rel(COMPONENT_EXACT_ASSEMBLY_CERT),
            "exists": COMPONENT_EXACT_ASSEMBLY_CERT.exists(),
            "schema": exact.get("schema"),
            "status": exact.get("status"),
            "firstFailure": exact.get("firstFailure"),
            "proofGrade": exact.get("proofGrade"),
            "checks": exact.get("checks"),
            "assembledRawDerivCoeff": field_summary(
                exact_fields.get("assembledRawDerivCoeff")
            ),
            "residualTaylorCoeff": field_summary(
                exact_fields.get("residualTaylorCoeff")
            ),
            "componentPropagationRemainderAbs": field_summary(
                exact_fields.get("componentPropagationRemainderAbs")
            ),
            "residualTaylorRemainderAbs": field_summary(
                exact_fields.get("residualTaylorRemainderAbs")
            ),
        },
        "componentResidualPayload": {
            "path": rel(COMPONENT_TAYLOR_RESIDUAL_PAYLOAD),
            "exists": COMPONENT_TAYLOR_RESIDUAL_PAYLOAD.exists(),
            "schema": residual.get("schema"),
            "status": residual.get("status"),
            "firstFailure": residual.get("firstFailure"),
            "proofStatusSubset": {
                "componentTaylorProofsPresent": proof_status.get(
                    "componentTaylorProofsPresent"
                ),
                "exactCoefficientAssemblyPassed": proof_status.get(
                    "exactCoefficientAssemblyPassed"
                ),
                "finalBudgetPassed": proof_status.get("finalBudgetPassed"),
                "outLeanWritten": proof_status.get("outLeanWritten"),
                "shapeSqDerivCenterCoeffRowsClosedCount": proof_status.get(
                    "shapeSqDerivCenterCoeffRowsClosedCount"
                ),
                "shapeSqDerivCenterCoeffRowsRequiredCount": proof_status.get(
                    "shapeSqDerivCenterCoeffRowsRequiredCount"
                ),
            },
            "modelDerivCoeff": field_summary(residual_fields.get("modelDerivCoeff")),
            "modelDerivCoeffPaddedToAssembledDegree": field_summary(
                residual_fields.get("modelDerivCoeffPaddedToAssembledDegree")
            ),
        },
        "streamLedger": {
            "path": rel(COMPONENT_ASSEMBLY_STREAM_LEDGER),
            "exists": COMPONENT_ASSEMBLY_STREAM_LEDGER.exists(),
            "schema": stream.get("schema"),
            "status": stream.get("status"),
            "firstFailure": stream.get("firstFailure"),
        },
        "whyNotProofCargo": (
            "These artifacts are useful coefficient/support evidence, but they "
            "do not provide a same-center segment0 theorem for the complete "
            "already-subtracted expression with modelCoeff, remainderAbs, "
            "Horner bounds, and sourceLower/sourceUpper."
        ),
        "failureCodeIfUsedAsClosure": LOCAL_FACTOR_TO_WHOLE_EXPR_GAP,
    }


def build_ledger() -> dict[str, Any]:
    source_rows_ledger = load_json(DIRECT_SOURCE_ROWS_LEDGER)
    support: dict[str, Any] = {}
    for path, symbols in SUPPORT_SYMBOLS.items():
        audit = symbol_audit(path, symbols)
        support[rel(path)] = {
            "exists": path.exists(),
            "sha256": sha256_file(path),
            "allSymbolsPresent": all_present(audit),
            "symbols": audit,
        }

    target_audit = symbol_audit(TARGET_LEAN_FILE, TARGET_SYMBOLS)
    target_payload_present = all_present(target_audit)
    proof_status = (
        "segment0_interval_checked_missing_family_budget"
        if target_payload_present
        else PROOF_STATUS
    )
    current_gap = UNIFORM_SEGMENT_ROWS_GAP if target_payload_present else CURRENT_GAP
    should_emit_lean_payload = False

    return {
        "schema": SCHEMA,
        "route": ROUTE,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "proofGrade": False,
        "proofStatus": proof_status,
        "currentGap": current_gap,
        "parentGap": PARENT_GAP,
        "previousSourceGap": PREVIOUS_SOURCE_GAP,
        "firstFailureCode": current_gap,
        "budgetFailureCode": BUDGET_FAIL,
        "computerUseRouteReview": PROSHKA_REVIEW,
        "upstreamDirectSourceRowsLedger": rel(DIRECT_SOURCE_ROWS_LEDGER),
        "upstreamDirectSourceRowsProofStatus": source_rows_ledger.get(
            "proofStatus"
        ),
        "upstreamDirectSourceRowsGap": source_rows_ledger.get("currentGap"),
        "targetLeanFile": rel(TARGET_LEAN_FILE),
        "targetLeanFileExists": TARGET_LEAN_FILE.exists(),
        "targetSymbols": target_audit,
        "targetPayloadPresent": target_payload_present,
        "shouldEmitLeanPayload": should_emit_lean_payload,
        "segment0Convention": {
            "cellL": "0",
            "cellU": "1/20",
            "center": "1/40",
            "radius": "1/40",
            "polynomialDegree": 28,
            "expression": (
                "primaryFiniteRow0Parent0Split100Sub0"
                "CollapsedDegree0SignedSourceExpr"
            ),
        },
        "sourceMaterialAudit": SOURCE_MATERIAL_AUDIT,
        "componentAssemblyAudit": build_component_assembly_audit(),
        "requiredData": REQUIRED_DATA,
        "supportSurfaces": support,
        "doNotUse": DO_NOT_USE,
        "stopRule": (
            "Stop and report CURRENT_GAP if the generator cannot produce a "
            "Lean-checkable whole-expression remainder theorem from local "
            "signed jets and order18 bounds.  Do not emit Payload.lean with "
            "a conditional field."
        ),
        "nextProofProducingPatch": (
            "Generate/prove the remaining direct signed-source segment rows "
            "for the full cell, then prove exact derivAbs and degree-0 "
            "budget rows.  The segment0 interval theorem is checked."
        ),
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Direct Signed Segment0 Taylor-Model Gate",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- parentGap: `{ledger['parentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- budgetFailureCode: `{ledger['budgetFailureCode']}`",
        f"- targetLeanFile: `{ledger['targetLeanFile']}`",
        f"- targetLeanFileExists: `{ledger['targetLeanFileExists']}`",
        f"- targetPayloadPresent: `{ledger['targetPayloadPresent']}`",
        f"- shouldEmitLeanPayload: `{ledger['shouldEmitLeanPayload']}`",
        "",
        "## Browser / Computer Use Route Review",
        "",
        f"- status: `{ledger['computerUseRouteReview']['status']}`",
        f"- nextPatch: {ledger['computerUseRouteReview']['nextPatch']}",
        f"- firstScript: `{ledger['computerUseRouteReview']['firstScript']}`",
        f"- firstLeanFile: `{ledger['computerUseRouteReview']['firstLeanFile']}`",
        f"- firstGeneratedArtifact: `{ledger['computerUseRouteReview']['firstGeneratedArtifact']}`",
        f"- firstGenericLeanBridge: `{ledger['computerUseRouteReview']['firstGenericLeanBridge']}`",
        f"- followupChoice: `{ledger['computerUseRouteReview']['followupChoice']}`",
        f"- followupFirstFile: `{ledger['computerUseRouteReview']['followupFirstFile']}`",
        f"- modelRemainderTheorem: `{ledger['computerUseRouteReview']['modelRemainderTheorem']}`",
        f"- segmentIntervalTheorem: `{ledger['computerUseRouteReview']['segmentIntervalTheorem']}`",
        f"- failureCodeIfNotProducibleNow: `{ledger['computerUseRouteReview']['failureCodeIfNotProducibleNow']}`",
        "",
        "Exact existing theorem names observed in the Browser answer:",
        "",
    ]
    for item in ledger["computerUseRouteReview"]["exactExistingTheoremsSeen"]:
        lines.append(f"- `{item}`")
    lines.extend(
        [
        "",
        "## Segment0 Convention",
        "",
        ]
    )
    for key, value in ledger["segment0Convention"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Source Material Audit",
            "",
            f"- firstUnmetInput: `{ledger['sourceMaterialAudit']['firstUnmetInput']}`",
            "",
            "Usable support:",
            "",
        ]
    )
    for item in ledger["sourceMaterialAudit"]["usableSupport"]:
        lines.append(f"- {item}")
    lines.extend(["", "Now proof cargo:", ""])
    for item in ledger["sourceMaterialAudit"].get("nowProofCargo", []):
        lines.append(f"- `{item}`")
    lines.extend(["", "Not yet proof cargo:", ""])
    for item in ledger["sourceMaterialAudit"]["notYetProofCargo"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "Why insufficient:",
            "",
            ledger["sourceMaterialAudit"]["whyExistingRowsAreInsufficient"],
            "",
        ]
    )
    component_audit = ledger["componentAssemblyAudit"]
    lines.extend(
        [
            "",
            "## Component Assembly Audit",
            "",
            f"- verdict: `{component_audit['verdict']}`",
            f"- segment0TargetCenter: `{component_audit['segment0Target']['center']}`",
            f"- segment0TargetRadius: `{component_audit['segment0Target']['radius']}`",
            f"- componentAssemblyCenter: `{component_audit['componentAssemblyFormula']['center']}`",
            f"- centerCrosswalkStatus: {component_audit['centerCrosswalkStatus']}",
            f"- exactAssemblyStatus: `{component_audit['exactAssemblyCertificate']['status']}`",
            f"- exactAssemblyFirstFailure: `{component_audit['exactAssemblyCertificate']['firstFailure']}`",
            f"- residualPayloadStatus: `{component_audit['componentResidualPayload']['status']}`",
            f"- residualPayloadFirstFailure: `{component_audit['componentResidualPayload']['firstFailure']}`",
            f"- streamLedgerStatus: `{component_audit['streamLedger']['status']}`",
            f"- failureCodeIfUsedAsClosure: `{component_audit['failureCodeIfUsedAsClosure']}`",
            "",
            "Field summary:",
            "",
        ]
    )
    for key in [
        "assembledRawDerivCoeff",
        "residualTaylorCoeff",
        "componentPropagationRemainderAbs",
        "residualTaylorRemainderAbs",
    ]:
        info = component_audit["exactAssemblyCertificate"][key]
        lines.append(
            f"- exactAssembly.{key}: present=`{info['present']}`, "
            f"kind=`{info['kind']}`, length=`{info.get('length')}`"
        )
    for key in ["modelDerivCoeff", "modelDerivCoeffPaddedToAssembledDegree"]:
        info = component_audit["componentResidualPayload"][key]
        lines.append(
            f"- residualPayload.{key}: present=`{info['present']}`, "
            f"kind=`{info['kind']}`, length=`{info.get('length')}`"
        )
    lines.extend(["", component_audit["whyNotProofCargo"], ""])
    lines.extend(["", "## Target Symbols", ""])
    for symbol, info in ledger["targetSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )
    lines.extend(["", "## Required Exact Data", ""])
    for item in ledger["requiredData"]:
        lines.extend(
            [
                f"### {item['id']}",
                "",
                f"- needed: {item['needed']}",
                f"- status: `{item['status']}`",
            ]
        )
        if "failureCode" in item:
            lines.append(f"- failureCode: `{item['failureCode']}`")
        lines.append("")
    lines.extend(["## Support Surfaces", ""])
    for path, info in ledger["supportSurfaces"].items():
        lines.extend(
            [
                f"### `{path}`",
                "",
                f"- exists: `{info['exists']}`",
                f"- allSymbolsPresent: `{info['allSymbolsPresent']}`",
                f"- sha256: `{info['sha256']}`",
                "",
            ]
        )
        for symbol, symbol_info in info["symbols"].items():
            lines.append(
                f"- `{symbol}`: present=`{symbol_info['present']}`, "
                f"line=`{symbol_info['line']}`"
            )
        lines.append("")
    lines.extend(["## Do Not Use", ""])
    for item in ledger["doNotUse"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Stop Rule",
            "",
            ledger["stopRule"],
            "",
            "## Next Proof-Producing Patch",
            "",
            ledger["nextProofProducingPatch"],
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    ledger = build_ledger()
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    print(ledger["proofStatus"])
    print(ledger["currentGap"])
    print(ledger["firstFailureCode"])
    print(f"wrote {rel(JSON_OUT)}")
    print(f"wrote {rel(MD_OUT)}")


if __name__ == "__main__":
    main()
