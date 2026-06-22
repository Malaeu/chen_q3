#!/usr/bin/env python3
"""Fail-closed component assembly coefficient-stream ledger.

This generator records the first proof-moving patch selected by the
browser/Proshka review after the tight ShapeSqDeriv audit:

    assembledRawDerivCoeff =
      scale * (cauchy(omegaPrimeCoeff, shapeSqCoeff)
        + cauchy(omegaCoeff, shapeSqDerivCoeff))

    residualTaylorCoeff =
      assembledRawDerivCoeff - zeroExtend15(ResidualDerivmodelCoeff)

It deliberately emits no Lean.  It fails closed until the repository contains
a checked component assembly/crosswalk theorem tying the component coefficient
stream to the active RawTaylorCoeffCert residual convention.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUESTS = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

LANDING_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAHRawLanding.lean"
COMPONENT_ASSEMBLY_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean"
)
CHUNK_CHECKER_FILE = PROOFS / "PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean"
ENDPOINT_SUPPORT_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean"
)
COMPONENT_PAYLOAD_JSON = (
    REQUESTS / "step33_a1_sub0_component_taylor_residual_payload.json"
)
TIGHT_PAYLOAD_JSON = REQUESTS / "step33_a1_sub0_shapesq_deriv_tight_payload.json"
OUTPUT_JSON = REQUESTS / "step33_a1_sub0_component_assembly_stream_ledger.json"
OUTPUT_MD = REQUESTS / "step33_a1_sub0_component_assembly_stream_ledger.md"

SCHEMA = "q3_psdpd_step33_a1_sub0_component_assembly_stream_ledger.v1"
STATUS = "fail_closed_raw_product_coeff_source_gap_after_parameterized_crosswalk"
STATUS_AFTER_CAUCHY = "fail_closed_raw_product_coeff_source_gap_after_cauchy_bridge"
STATUS_AFTER_NOMINAL_OBJECTS = (
    "fail_closed_nominal_object_coeffs_present_scale_source_bridge_gap"
)
STATUS_AFTER_SOURCE_INTERVALS = (
    "fail_closed_nominal_source_intervals_checked_product_error_budget_gap"
)
STATUS_AFTER_PRODUCT_ERROR_BRIDGE = (
    "fail_closed_product_error_bridge_checked_concrete_budget_gap"
)
STATUS_AFTER_NOMINAL_SCALE_ABS_BOUND = (
    "fail_closed_product_error_bridge_and_nominal_scale_abs_checked_"
    "product_component_witness_gap"
)
STATUS_AFTER_PRODUCT_COMPONENT_BRIDGE = (
    "fail_closed_product_component_bridge_checked_factor_witness_gap"
)
STATUS_AFTER_PRODUCT_FACTOR_INTERFACE = (
    "fail_closed_product_factor_interface_checked_nominal_error_witness_gap"
)
STATUS_AFTER_FACTOR_ERROR_WITNESSES = (
    "fail_closed_factor_error_witnesses_checked_nominal_abs_budget_gap"
)
FIRST_FAILURE = "STEP33_A1_SUB0_COMPONENT_TAYLOR_ACTIVE_MODEL_COEFF_MISMATCH"
RAW_ASSEMBLY_GAP = "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP"
SCALE_SOURCE_BRIDGE_GAP = (
    "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_SCALE_SOURCE_BRIDGE_GAP"
)
PRODUCT_ERROR_BUDGET_GAP = (
    "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_PRODUCT_ERROR_BUDGET_GAP"
)
CONCRETE_PRODUCT_ERROR_BUDGET_GAP = (
    "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_CONCRETE_PRODUCT_ERROR_BUDGET_GAP"
)
PRODUCT_COMPONENT_WITNESS_GAP = (
    "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_PRODUCT_COMPONENT_WITNESS_GAP"
)
PRODUCT_FACTOR_WITNESS_GAP = (
    "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_PRODUCT_FACTOR_WITNESS_GAP"
)
PRODUCT_FACTOR_ERROR_NOMINAL_ABS_WITNESS_GAP = (
    "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_FACTOR_ERROR_AND_NOMINAL_ABS_WITNESS_GAP"
)
NOMINAL_FACTOR_ABS_BUDGET_GAP = (
    "STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_NOMINAL_FACTOR_ABS_BUDGET_GAP"
)
ZERO_EXTENSION_GAP = (
    "STEP33_A1_SUB0_P45_PADDED_EQ_ACTIVE_P15_POLYNOMIAL_CROSSWALK_GAP"
)
CAUCHY_PRODUCT_GAP = "STEP33_A1_SUB0_COMPONENT_TAYLOR_CAUCHY_PRODUCT_CROSSWALK_GAP"
TIGHT_ROUTE_GAP = (
    "STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP"
)

RAW_INTEGRAND_DERIV = "primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm"
RESIDUAL_MODEL = "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff"
RAW_TAYLOR_CERT = "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert"
POLY_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel"
)
RESIDUAL_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm"
)
RAW_OMEGA_TAYLOR_POLY = "rawOmegaATaylorPolynomial"
INTEGRATED_TAYLOR_COEFF = "integratedTaylorCoeff"
SHAPESQ_INTEGRATED_RECEIVER = "shapeSqTaylor_bound_of_shapeSqDerivTaylor_bound"
SHAPESQ_DERIV_CERT = "ShapeSqDerivTaylorIntervalCert"

TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "componentTaylor_residualCoeff_crosswalk"
)
SAME_DEGREE_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled"
)
PARAMETERIZED_FULL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "componentTaylor_residualCoeff_crosswalk_of_assembled"
)
ZERO_EXTENSION_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_padded_residualDerivmodel_poly_eq"
)
SUB_COEFF_LEMMA = "rawOmegaATaylorPolynomial_sub_coeff"
CAUCHY_PRODUCT_THEOREM = "rawOmegaATaylorPolynomial_mul_coeff"
CAUCHY_COEFF_DEF = "rawOmegaTaylorCauchyCoeff"
ASSEMBLED_COEFF = "primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff"
RESIDUAL_COEFF = "primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff"
RESIDUAL_COEFF_OF = "primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf"
NOMINAL_SCALE_COEFF = "primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff"
NOMINAL_SCALE_LOWER = "primaryFiniteRow0Parent0Split100Sub0TightScaleLower"
NOMINAL_SCALE_UPPER = "primaryFiniteRow0Parent0Split100Sub0TightScaleUpper"
NOMINAL_SCALE_ABS_BOUND = (
    "primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound"
)
NOMINAL_SCALE_ERROR_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs"
)
NOMINAL_SCALE_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_nominalScale_mem_tightInterval"
)
NOMINAL_SCALE_ABS_BOUND_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_bound"
)
NOMINAL_SCALE_ERROR_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_nominalScale_abs_error_of_active_interval"
)
NOMINAL_OMEGA_ANCHOR_COEFF = (
    "primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff"
)
NOMINAL_OMEGA_ANCHOR_LOWER = (
    "primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower"
)
NOMINAL_OMEGA_ANCHOR_UPPER = (
    "primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper"
)
NOMINAL_OMEGA_ANCHOR_ERROR_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs"
)
NOMINAL_OMEGA_ANCHOR_ERROR_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_nominalOmegaAnchor_abs_error_of_active_interval"
)
NOMINAL_SOURCE_INTERVAL_BRIDGE = (
    "primaryFiniteRow0Parent0Split100Sub0_nominal_source_interval_bridge"
)
PRODUCT_ERROR_BUDGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_product_error_budget_bridge"
)
PRODUCT_SUMMAND_ABS_BRIDGE = (
    "primaryFiniteRow0Parent0Split100Sub0_product_summand_abs_bridge"
)
PRODUCT_SUMMAND_ERROR_BRIDGE = (
    "primaryFiniteRow0Parent0Split100Sub0_product_summand_error_bridge"
)
PRODUCT_COMPONENT_WITNESS_BRIDGE = (
    "primaryFiniteRow0Parent0Split100Sub0_product_component_witness_bridge"
)
NOMINAL_FACTOR_ABS_RADIUS_BUDGET = (
    "primaryFiniteRow0Parent0Split100Sub0_nominal_factor_abs_of_coeff_radius_budget"
)
FACTOR_ABS_FROM_ERROR_AND_NOMINAL_ABS = (
    "primaryFiniteRow0Parent0Split100Sub0_factor_abs_from_error_and_nominal_abs"
)
PRODUCT_COMPONENT_FACTOR_WITNESS_BRIDGE = (
    "primaryFiniteRow0Parent0Split100Sub0_product_component_factor_witness_bridge"
)
OMEGA_PRIME_FACTOR_ERROR = (
    "primaryFiniteRow0Parent0Split100Sub0_omegaPrime_factor_error"
)
OMEGA_FACTOR_ERROR = "primaryFiniteRow0Parent0Split100Sub0_omega_factor_error"
SHAPESQ_FACTOR_ERROR = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSq_factor_error"
)
SHAPESQ_DERIV_FACTOR_ERROR = (
    "primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_factor_error"
)
OMEGA_PRIME_PUBLIC_BOUND = (
    "omegaPrimeGeneratedRemainderCert_bound_public"
)
OMEGA_PRIME_SHAPESQ_PRODUCT_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_omegaPrime_shapeSq_product_crosswalk"
)
OMEGA_SHAPESQ_DERIV_PRODUCT_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_omega_shapeSqDeriv_product_crosswalk"
)
PADDED_RESIDUAL_MODEL = (
    "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded"
)
ASSEMBLED_DEGREE = "primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree"


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8") if path.exists() else ""


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def symbol_pattern(symbol: str) -> re.Pattern[str]:
    return re.compile(rf"(?<![A-Za-z0-9_]){re.escape(symbol)}(?![A-Za-z0-9_])")


def line_of(text: str, needle: str) -> int | None:
    pattern = symbol_pattern(needle)
    for idx, line in enumerate(text.splitlines(), start=1):
        if pattern.search(line):
            return idx
    return None


def source_symbols(path: Path, text: str, symbols: list[str]) -> dict[str, Any]:
    return {
        "path": str(path.relative_to(ROOT)),
        "exists": path.exists(),
        "symbols": {
            symbol: {
                "found": symbol_pattern(symbol).search(text) is not None,
                "line": line_of(text, symbol),
            }
            for symbol in symbols
        },
    }


def nested_get(data: dict[str, Any] | None, path: list[str], default: Any = None) -> Any:
    cur: Any = data
    for key in path:
        if not isinstance(cur, dict) or key not in cur:
            return default
        cur = cur[key]
    return cur


def proof_status(component: dict[str, Any] | None, key: str) -> Any:
    return nested_get(component, ["proofStatus", key])


def has_checked_full_crosswalk(assembly_text: str) -> bool:
    return symbol_pattern(TARGET_THEOREM).search(assembly_text) is not None


def has_checked_same_degree_crosswalk(assembly_text: str) -> bool:
    return (
        symbol_pattern(SAME_DEGREE_THEOREM).search(assembly_text) is not None
        and symbol_pattern(SUB_COEFF_LEMMA).search(assembly_text) is not None
    )


def has_checked_parameterized_full_crosswalk(assembly_text: str) -> bool:
    return (
        symbol_pattern(PARAMETERIZED_FULL_THEOREM).search(assembly_text) is not None
        and symbol_pattern(SAME_DEGREE_THEOREM).search(assembly_text) is not None
        and symbol_pattern(ZERO_EXTENSION_THEOREM).search(assembly_text) is not None
    )


def has_checked_zero_extension_bridge(assembly_text: str) -> bool:
    return symbol_pattern(ZERO_EXTENSION_THEOREM).search(assembly_text) is not None


def has_checked_cauchy_product_bridge(assembly_text: str) -> bool:
    return (
        symbol_pattern(CAUCHY_PRODUCT_THEOREM).search(assembly_text) is not None
        and symbol_pattern(CAUCHY_COEFF_DEF).search(assembly_text) is not None
    )


def has_checked_nominal_source_interval_bridge(assembly_text: str) -> bool:
    required = [
        NOMINAL_SCALE_LOWER,
        NOMINAL_SCALE_UPPER,
        NOMINAL_SCALE_ERROR_ABS,
        NOMINAL_SCALE_INTERVAL_THEOREM,
        NOMINAL_SCALE_ERROR_THEOREM,
        NOMINAL_OMEGA_ANCHOR_LOWER,
        NOMINAL_OMEGA_ANCHOR_UPPER,
        NOMINAL_OMEGA_ANCHOR_ERROR_ABS,
        NOMINAL_OMEGA_ANCHOR_ERROR_THEOREM,
        NOMINAL_SOURCE_INTERVAL_BRIDGE,
    ]
    return all(
        symbol_pattern(symbol).search(assembly_text) is not None
        for symbol in required
    )


def has_checked_product_error_budget_bridge(assembly_text: str) -> bool:
    return (
        symbol_pattern(PRODUCT_ERROR_BUDGET_THEOREM).search(assembly_text)
        is not None
    )


def has_checked_nominal_scale_abs_bound(assembly_text: str) -> bool:
    required = [
        NOMINAL_SCALE_ABS_BOUND,
        NOMINAL_SCALE_ABS_BOUND_THEOREM,
    ]
    return all(
        symbol_pattern(symbol).search(assembly_text) is not None
        for symbol in required
    )


def has_checked_product_component_witness_bridge(assembly_text: str) -> bool:
    required = [
        PRODUCT_SUMMAND_ABS_BRIDGE,
        PRODUCT_SUMMAND_ERROR_BRIDGE,
        PRODUCT_COMPONENT_WITNESS_BRIDGE,
    ]
    return all(
        symbol_pattern(symbol).search(assembly_text) is not None
        for symbol in required
    )


def has_checked_product_factor_witness_interface(assembly_text: str) -> bool:
    required = [
        NOMINAL_FACTOR_ABS_RADIUS_BUDGET,
        FACTOR_ABS_FROM_ERROR_AND_NOMINAL_ABS,
        PRODUCT_COMPONENT_FACTOR_WITNESS_BRIDGE,
    ]
    return all(
        symbol_pattern(symbol).search(assembly_text) is not None
        for symbol in required
    )


def has_checked_factor_error_witnesses(
    assembly_text: str, endpoint_support_text: str
) -> bool:
    required_assembly = [
        OMEGA_PRIME_FACTOR_ERROR,
        OMEGA_FACTOR_ERROR,
        SHAPESQ_FACTOR_ERROR,
        SHAPESQ_DERIV_FACTOR_ERROR,
    ]
    return (
        symbol_pattern(OMEGA_PRIME_PUBLIC_BOUND).search(endpoint_support_text)
        is not None
        and all(
            symbol_pattern(symbol).search(assembly_text) is not None
            for symbol in required_assembly
        )
    )


def component_field_state(component: dict[str, Any] | None) -> dict[str, Any]:
    generator_fields = component.get("generatorFields", {}) if component else {}
    component_status = component.get("componentTaylorStatus", {}) if component else {}
    proof = component.get("proofStatus", {}) if component else {}
    return {
        "payloadExists": component is not None,
        "payloadSchema": component.get("schema") if component else None,
        "payloadStatus": component.get("status") if component else None,
        "payloadFirstFailure": component.get("firstFailure") if component else None,
        "componentTaylorAssemblyLeanWritten": component_status.get(
            "assemblyLeanWritten"
        ),
        "componentTaylorOverallProofSafe": component_status.get("overallProofSafe"),
        "exactCoefficientAssemblyPassed": proof.get("exactCoefficientAssemblyPassed"),
        "componentTaylorProofsPresent": proof.get("componentTaylorProofsPresent"),
        "omegaDerivTaylorProofPresent": proof.get("omegaDerivTaylorProofPresent"),
        "omegaTaylorIntegratedPolyDerivCrosswalkProofPresent": proof.get(
            "omegaTaylorIntegratedPolyDerivCrosswalkProofPresent"
        ),
        "omegaTaylorCenterAnchorPayloadPresent": proof.get(
            "omegaTaylorCenterAnchorPayloadPresent"
        ),
        "shapeSqDerivCenterCoeffRowsClosedCount": proof.get(
            "shapeSqDerivCenterCoeffRowsClosedCount"
        ),
        "shapeSqDerivCenterCoeffRowsRequiredCount": proof.get(
            "shapeSqDerivCenterCoeffRowsRequiredCount"
        ),
        "shapeSqDerivOrder16UniformBoundPresent": proof.get(
            "shapeSqDerivOrder16UniformBoundPresent"
        ),
        "assembledRawDerivCoeffPresent": generator_fields.get(
            "assembledRawDerivCoeff"
        )
        is not None,
        "residualTaylorCoeffPresent": generator_fields.get("residualTaylorCoeff")
        is not None,
        "residualTaylorRemainderAbsPresent": generator_fields.get(
            "residualTaylorRemainderAbs"
        )
        is not None,
    }


def build_report() -> dict[str, Any]:
    landing_text = read_text(LANDING_FILE)
    assembly_text = read_text(COMPONENT_ASSEMBLY_FILE)
    checker_text = read_text(CHUNK_CHECKER_FILE)
    endpoint_support_text = read_text(ENDPOINT_SUPPORT_FILE)
    component = load_json(COMPONENT_PAYLOAD_JSON)
    tight = load_json(TIGHT_PAYLOAD_JSON)

    checked_full_crosswalk = has_checked_full_crosswalk(assembly_text)
    checked_same_degree_crosswalk = has_checked_same_degree_crosswalk(assembly_text)
    checked_parameterized_full_crosswalk = has_checked_parameterized_full_crosswalk(
        assembly_text
    )
    checked_zero_extension_bridge = has_checked_zero_extension_bridge(assembly_text)
    checked_cauchy_product_bridge = has_checked_cauchy_product_bridge(assembly_text)
    fields = component_field_state(component)
    nominal_object_bridge_present = bool(
        checked_full_crosswalk
        and symbol_pattern(ASSEMBLED_COEFF).search(assembly_text)
        and symbol_pattern(RESIDUAL_COEFF).search(assembly_text)
        and symbol_pattern(NOMINAL_SCALE_COEFF).search(assembly_text)
        and symbol_pattern(NOMINAL_OMEGA_ANCHOR_COEFF).search(assembly_text)
    )
    nominal_source_interval_bridge_present = bool(
        nominal_object_bridge_present
        and has_checked_nominal_source_interval_bridge(assembly_text)
    )
    product_error_budget_bridge_present = bool(
        nominal_source_interval_bridge_present
        and has_checked_product_error_budget_bridge(assembly_text)
    )
    nominal_scale_abs_bound_present = bool(
        product_error_budget_bridge_present
        and has_checked_nominal_scale_abs_bound(assembly_text)
    )
    product_component_witness_bridge_present = bool(
        nominal_scale_abs_bound_present
        and has_checked_product_component_witness_bridge(assembly_text)
    )
    product_factor_witness_interface_present = bool(
        product_component_witness_bridge_present
        and has_checked_product_factor_witness_interface(assembly_text)
    )
    factor_error_witnesses_present = bool(
        product_factor_witness_interface_present
        and has_checked_factor_error_witnesses(
            assembly_text, endpoint_support_text
        )
    )
    fields.update(
        {
            "assembledRawDerivCoeffLeanPresent": symbol_pattern(
                ASSEMBLED_COEFF
            ).search(assembly_text)
            is not None,
            "residualTaylorCoeffLeanPresent": symbol_pattern(
                RESIDUAL_COEFF
            ).search(assembly_text)
            is not None,
            "nominalScaleCoeffLeanPresent": symbol_pattern(
                NOMINAL_SCALE_COEFF
            ).search(assembly_text)
            is not None,
            "nominalOmegaAnchorCoeffLeanPresent": symbol_pattern(
                NOMINAL_OMEGA_ANCHOR_COEFF
            ).search(assembly_text)
            is not None,
            "targetObjectCrosswalkLeanPresent": checked_full_crosswalk,
            "nominalObjectBridgePresent": nominal_object_bridge_present,
            "nominalSourceIntervalBridgePresent": (
                nominal_source_interval_bridge_present
            ),
            "productErrorBudgetBridgePresent": product_error_budget_bridge_present,
            "nominalScaleAbsBoundPresent": nominal_scale_abs_bound_present,
            "productComponentWitnessBridgePresent": (
                product_component_witness_bridge_present
            ),
            "productFactorWitnessInterfacePresent": (
                product_factor_witness_interface_present
            ),
            "factorErrorWitnessesPresent": factor_error_witnesses_present,
        }
    )
    guard_passes = bool(
        checked_full_crosswalk
        and fields["assembledRawDerivCoeffPresent"]
        and fields["residualTaylorCoeffPresent"]
        and fields["exactCoefficientAssemblyPassed"]
    )

    return {
        "schema": SCHEMA,
        "status": (
            "candidate_ready_for_lean_validation"
            if guard_passes
            else STATUS_AFTER_FACTOR_ERROR_WITNESSES
            if factor_error_witnesses_present
            else STATUS_AFTER_PRODUCT_FACTOR_INTERFACE
            if product_factor_witness_interface_present
            else STATUS_AFTER_PRODUCT_COMPONENT_BRIDGE
            if product_component_witness_bridge_present
            else STATUS_AFTER_NOMINAL_SCALE_ABS_BOUND
            if nominal_scale_abs_bound_present
            else STATUS_AFTER_PRODUCT_ERROR_BRIDGE
            if product_error_budget_bridge_present
            else STATUS_AFTER_SOURCE_INTERVALS
            if nominal_source_interval_bridge_present
            else STATUS_AFTER_NOMINAL_OBJECTS
            if nominal_object_bridge_present
            else STATUS_AFTER_CAUCHY
            if checked_cauchy_product_bridge
            else STATUS
        ),
        "firstFailure": (
            None
            if guard_passes
            else NOMINAL_FACTOR_ABS_BUDGET_GAP
            if factor_error_witnesses_present
            else PRODUCT_FACTOR_ERROR_NOMINAL_ABS_WITNESS_GAP
            if product_factor_witness_interface_present
            else PRODUCT_FACTOR_WITNESS_GAP
            if product_component_witness_bridge_present
            else PRODUCT_COMPONENT_WITNESS_GAP
            if nominal_scale_abs_bound_present
            else CONCRETE_PRODUCT_ERROR_BUDGET_GAP
            if product_error_budget_bridge_present
            else PRODUCT_ERROR_BUDGET_GAP
            if nominal_source_interval_bridge_present
            else SCALE_SOURCE_BRIDGE_GAP
            if nominal_object_bridge_present
            else RAW_ASSEMBLY_GAP
        ),
        "localAssemblyGap": (
            None
            if guard_passes
            else NOMINAL_FACTOR_ABS_BUDGET_GAP
            if factor_error_witnesses_present
            else PRODUCT_FACTOR_ERROR_NOMINAL_ABS_WITNESS_GAP
            if product_factor_witness_interface_present
            else PRODUCT_FACTOR_WITNESS_GAP
            if product_component_witness_bridge_present
            else PRODUCT_COMPONENT_WITNESS_GAP
            if nominal_scale_abs_bound_present
            else CONCRETE_PRODUCT_ERROR_BUDGET_GAP
            if product_error_budget_bridge_present
            else PRODUCT_ERROR_BUDGET_GAP
            if nominal_source_interval_bridge_present
            else SCALE_SOURCE_BRIDGE_GAP
            if nominal_object_bridge_present
            else RAW_ASSEMBLY_GAP
        ),
        "routeLevelGap": TIGHT_ROUTE_GAP,
        "zeroExtensionBridgeGap": None if checked_zero_extension_bridge else ZERO_EXTENSION_GAP,
        "proofBoundary": (
            "A Lean-checked parameterized active-model crosswalk exists, "
            "including the same-degree subtraction bridge and degree-45/"
            "degree-15 zero-extension bridge.  The generic Cauchy product "
            "coefficient bridge is checked if recorded in the guard below. "
            "Named nominal coefficient objects are checked if recorded in the "
            "guard below.  Source interval replacements for the nominal scale "
            "and nominal omega anchor are checked if recorded in the guard "
            "below.  They still do not prove the active raw closed form until "
            "their losses are propagated through the product assembly budget. "
            "The generic product-error budget bridge is checked if recorded "
            "in the guard below, but concrete generated coefficient/remainder "
            "arithmetic remains separate.  The nominal-scale absolute bound is "
            "checked if recorded in the guard below; product-summand error "
            "and absolute witnesses remain separate.  The factor-to-product "
            "component witness bridge is checked if recorded in the guard "
            "below; concrete factor witnesses remain separate.  The factor "
            "absolute-value interface is checked if recorded in the guard "
            "below.  Concrete factor-error witnesses are checked if recorded "
            "in the guard below; nominal factor absolute budgets and final "
            "arithmetic comparisons remain separate. "
            "Step33A.1-A is not closed."
        ),
        "browserProshkaDecision": {
            "chosen": "A_component_assembly_coefficient_stream_ledger_first",
            "firstPatchOrTheorem": TARGET_THEOREM,
            "failureCodeIfFails": FIRST_FAILURE,
            "whySmallest": (
                "Rows 2..15 can prove bounds for the correct function but "
                "still feed the wrong polynomial payload unless the component "
                "coefficient stream is first fixed in the active "
                "RawTaylorCoeffCert residual convention."
            ),
            "doNot": [
                "do not unfold all Fin 46 coefficients with norm_num/ring_nf",
                "do not generate ShapeSqDeriv rows 2..15 before the crosswalk",
                "do not declare arbitrary ShapeSqDerivTightCoeff objects",
                "do not move to the direct residual interval theorem",
                "do not add a new receiver",
                "do not set componentTaylorProofsPresent=true without Lean check",
            ],
        },
        "browserProshkaFollowupDecision": {
            "chosen": "A_cauchy_product_crosswalk_first",
            "firstPatchOrTheorem": CAUCHY_PRODUCT_THEOREM,
            "coefficientDefinition": CAUCHY_COEFF_DEF,
            "failureCodeIfFails": CAUCHY_PRODUCT_GAP,
            "mismatchCodeAfterProductBridge": FIRST_FAILURE,
            "whySmallest": (
                "Fix the exact degree/factorial/center/Cauchy normalization "
                "before generating more rows; otherwise bounds can target the "
                "right function but the wrong polynomial payload."
            ),
            "doNot": [
                "do not set exactCoefficientAssemblyPassed=true",
                "do not treat rational scaleCenter as exact ((3/10)/Real.pi)",
                "do not treat NominalScaleCoeff as the active closed-form scale",
                "do not hardcode assembledDegree=45 as the real product degree; "
                "15-by-16 products give degree 31 before zero-padding",
                "do not generate tight rows before exact coefficient-ledger comparison",
                "do not unfold 46-term sums with ring_nf/norm_num",
            ],
        },
        "targetTheoremContract": {
            "name": TARGET_THEOREM,
            "file": "Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean",
            "status": (
                "OBJECT_THEOREM_LEAN_CHECKED_FACTOR_ERROR_WITNESSES_CHECKED_NOMINAL_ABS_BUDGET_OPEN"
                if factor_error_witnesses_present
                else
                "OBJECT_THEOREM_LEAN_CHECKED_PRODUCT_FACTOR_INTERFACE_CHECKED_NOMINAL_ERROR_WITNESS_OPEN"
                if product_factor_witness_interface_present
                else
                "OBJECT_THEOREM_LEAN_CHECKED_PRODUCT_COMPONENT_BRIDGE_CHECKED_FACTOR_WITNESS_OPEN"
                if product_component_witness_bridge_present
                else
                "OBJECT_THEOREM_LEAN_CHECKED_PRODUCT_ERROR_BRIDGE_CHECKED_CONCRETE_BUDGET_OPEN"
                if product_error_budget_bridge_present
                else
                "OBJECT_THEOREM_LEAN_CHECKED_SOURCE_INTERVALS_CHECKED_PRODUCT_ERROR_OPEN"
                if nominal_source_interval_bridge_present
                else
                "OBJECT_THEOREM_LEAN_CHECKED_NOMINAL_NOT_PROOF_GRADE"
                if nominal_object_bridge_present
                else "OBJECT_THEOREM_NOT_WRITTEN_PARAMETERIZED_FULL_LEAN_CHECKED"
                if checked_parameterized_full_crosswalk
                else "FULL_NOT_WRITTEN_PARTIAL_SAME_DEGREE_LEAN_CHECKED"
                if checked_same_degree_crosswalk
                else "NOT_WRITTEN"
            ),
            "statementAscii": (
                "rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) "
                "AssembledRawDerivCoeff eta - rawOmegaATaylorPolynomial 15 "
                "(1/20) ResidualDerivmodelCoeff eta = rawOmegaATaylorPolynomial "
                "AssembledRawDerivDegree (1/20) ResidualTaylorCoeff eta"
            ),
            "partialSameDegreeTheorem": SAME_DEGREE_THEOREM,
            "zeroExtensionTheorem": ZERO_EXTENSION_THEOREM,
            "parameterizedFullTheorem": PARAMETERIZED_FULL_THEOREM,
            "partialSameDegreeStatementAscii": (
                "rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) "
                "assembled eta - rawOmegaATaylorPolynomial AssembledRawDerivDegree "
                "(1/20) ResidualDerivmodelCoeffPadded eta = "
                "rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) "
                "(ResidualTaylorCoeffOf assembled) eta"
            ),
            "partialSameDegreeFailureCodeIfNotEnough": ZERO_EXTENSION_GAP,
            "coeffDefinitionsRequired": [
                ASSEMBLED_DEGREE,
                ASSEMBLED_COEFF,
                RESIDUAL_COEFF,
            ],
        },
        "componentAssemblyFormula": {
            "scale": "((3 : Real) / 10) / Real.pi",
            "rawClosedForm": (
                "scale * (omegaPrime * shapeSq + omega * shapeSqDeriv)"
            ),
            "assembledRawDerivCoeffFormula": (
                "scale * (cauchy(omegaPrimeCoeff, shapeSqCoeff) + "
                "cauchy(omegaCoeff, shapeSqDerivCoeff))"
            ),
            "residualTaylorCoeffFormula": (
                "assembledRawDerivCoeff - "
                "zeroExtend15(ResidualDerivmodelCoeff)"
            ),
            "center": "1/20",
            "componentDegree": 15,
            "assembledDegree": 45,
            "normalizationWarning": (
                "Do not identify a ShapeSqDeriv coefficient stream with the "
                "active residual coefficient stream. It feeds through the "
                "product assembly with omega and omegaPrime first."
            ),
        },
        "sourceFiles": {
            "landing": source_symbols(
                LANDING_FILE,
                landing_text,
                [
                    RAW_INTEGRAND_DERIV,
                    RAW_TAYLOR_CERT,
                    RESIDUAL_MODEL,
                    POLY_CROSSWALK,
                    RESIDUAL_CROSSWALK,
                    TARGET_THEOREM,
                    ASSEMBLED_COEFF,
                    RESIDUAL_COEFF,
                ],
            ),
            "componentAssembly": source_symbols(
                COMPONENT_ASSEMBLY_FILE,
                assembly_text,
                [
                    ASSEMBLED_DEGREE,
                    PADDED_RESIDUAL_MODEL,
                    ZERO_EXTENSION_THEOREM,
                    RESIDUAL_COEFF_OF,
                    SUB_COEFF_LEMMA,
                    CAUCHY_COEFF_DEF,
                    CAUCHY_PRODUCT_THEOREM,
                    OMEGA_PRIME_SHAPESQ_PRODUCT_THEOREM,
                    OMEGA_SHAPESQ_DERIV_PRODUCT_THEOREM,
                    SAME_DEGREE_THEOREM,
                    PARAMETERIZED_FULL_THEOREM,
                    TARGET_THEOREM,
                    ASSEMBLED_COEFF,
                    RESIDUAL_COEFF,
                    NOMINAL_SCALE_COEFF,
                    NOMINAL_SCALE_LOWER,
                    NOMINAL_SCALE_UPPER,
                    NOMINAL_SCALE_ABS_BOUND,
                    NOMINAL_SCALE_ERROR_ABS,
                    NOMINAL_SCALE_INTERVAL_THEOREM,
                    NOMINAL_SCALE_ABS_BOUND_THEOREM,
                    NOMINAL_SCALE_ERROR_THEOREM,
                    NOMINAL_OMEGA_ANCHOR_COEFF,
                    NOMINAL_OMEGA_ANCHOR_LOWER,
                    NOMINAL_OMEGA_ANCHOR_UPPER,
                    NOMINAL_OMEGA_ANCHOR_ERROR_ABS,
                    NOMINAL_OMEGA_ANCHOR_ERROR_THEOREM,
                    NOMINAL_SOURCE_INTERVAL_BRIDGE,
                    PRODUCT_ERROR_BUDGET_THEOREM,
                    PRODUCT_SUMMAND_ABS_BRIDGE,
                    PRODUCT_SUMMAND_ERROR_BRIDGE,
                    PRODUCT_COMPONENT_WITNESS_BRIDGE,
                    NOMINAL_FACTOR_ABS_RADIUS_BUDGET,
                    FACTOR_ABS_FROM_ERROR_AND_NOMINAL_ABS,
                    PRODUCT_COMPONENT_FACTOR_WITNESS_BRIDGE,
                    OMEGA_PRIME_FACTOR_ERROR,
                    OMEGA_FACTOR_ERROR,
                    SHAPESQ_FACTOR_ERROR,
                    SHAPESQ_DERIV_FACTOR_ERROR,
                ],
            ),
            "endpointHighOrderSupport": source_symbols(
                ENDPOINT_SUPPORT_FILE,
                endpoint_support_text,
                [
                    OMEGA_PRIME_PUBLIC_BOUND,
                ],
            ),
            "chunkTaylorChecker": source_symbols(
                CHUNK_CHECKER_FILE,
                checker_text,
                [
                    RAW_OMEGA_TAYLOR_POLY,
                    INTEGRATED_TAYLOR_COEFF,
                    SHAPESQ_INTEGRATED_RECEIVER,
                    SHAPESQ_DERIV_CERT,
                ],
            ),
            "componentPayload": {
                "path": str(COMPONENT_PAYLOAD_JSON.relative_to(ROOT)),
                "exists": COMPONENT_PAYLOAD_JSON.exists(),
                "schema": component.get("schema") if component else None,
                "status": component.get("status") if component else None,
                "firstFailure": component.get("firstFailure") if component else None,
            },
            "tightPayload": {
                "path": str(TIGHT_PAYLOAD_JSON.relative_to(ROOT)),
                "exists": TIGHT_PAYLOAD_JSON.exists(),
                "schema": tight.get("schema") if tight else None,
                "status": tight.get("status") if tight else None,
                "firstFailure": tight.get("firstFailure") if tight else None,
            },
        },
        "currentComponentFieldState": fields,
        "guard": {
            "checkedFullCrosswalkTheoremPresent": checked_full_crosswalk,
            "checkedSameDegreeCrosswalkTheoremPresent": checked_same_degree_crosswalk,
            "checkedParameterizedActiveModelCrosswalkTheoremPresent": (
                checked_parameterized_full_crosswalk
            ),
            "paddedDegree45EqualsActiveDegree15BridgePresent": (
                checked_zero_extension_bridge
            ),
            "checkedCauchyProductBridgePresent": checked_cauchy_product_bridge,
            "checkedNominalObjectBridgePresent": nominal_object_bridge_present,
            "checkedNominalSourceIntervalBridgePresent": (
                nominal_source_interval_bridge_present
            ),
            "checkedProductErrorBudgetBridgePresent": (
                product_error_budget_bridge_present
            ),
            "checkedNominalScaleAbsBoundPresent": (
                nominal_scale_abs_bound_present
            ),
            "checkedProductComponentWitnessBridgePresent": (
                product_component_witness_bridge_present
            ),
            "checkedProductFactorWitnessInterfacePresent": (
                product_factor_witness_interface_present
            ),
            "checkedFactorErrorWitnessesPresent": (
                factor_error_witnesses_present
            ),
            "paddedDegree45EqualsActiveDegree15BridgeGap": (
                None if checked_zero_extension_bridge else ZERO_EXTENSION_GAP
            ),
            "assembledRawDerivCoeffGeneratorFieldPresent": fields[
                "assembledRawDerivCoeffPresent"
            ],
            "residualTaylorCoeffGeneratorFieldPresent": fields[
                "residualTaylorCoeffPresent"
            ],
            "assembledRawDerivCoeffLeanPresent": fields[
                "assembledRawDerivCoeffLeanPresent"
            ],
            "residualTaylorCoeffLeanPresent": fields[
                "residualTaylorCoeffLeanPresent"
            ],
            "exactCoefficientAssemblyPassed": fields[
                "exactCoefficientAssemblyPassed"
            ],
            "guardPasses": guard_passes,
        },
        "decision": {
            "canGenerateRows2To15Now": False,
            "canUseParameterizedLeanCrosswalkNow": checked_parameterized_full_crosswalk,
            "canEmitObjectLevelCrosswalkNow": nominal_object_bridge_present,
            "nextFailureIfCauchyBridgeMissing": (
                None if checked_cauchy_product_bridge else CAUCHY_PRODUCT_GAP
            ),
            "nextPatch": (
                "Generate or import concrete same-normalization nominal "
                "polynomial absolute budgets for omegaPrime, shapeSq, omega, "
                "and shapeSqDeriv, then prove the product abs/error budget "
                "comparisons and the final scale/product budget comparison.  "
                "Only after that may generator exact-assembly fields be "
                "reconsidered."
                if factor_error_witnesses_present
                else
                "Generate or import concrete same-normalization factor error "
                "bounds and nominal polynomial absolute budgets for "
                "omegaPrime, shapeSq, omega, and shapeSqDeriv, then prove the "
                "product abs/error budget comparisons and the final "
                "scale/product budget comparison.  Only after that may "
                "generator exact-assembly fields be reconsidered."
                if product_factor_witness_interface_present
                else
                "Generate or import the concrete same-normalization arithmetic "
                "budget consumed by the product-component witness bridge: "
                "factor-level error bounds for omegaPrime, shapeSq, omega, and "
                "shapeSqDeriv; factor absolute bounds including nominal "
                "right-factor bounds; product abs/error budget comparisons; "
                "and the final scale/product budget comparison.  Only after "
                "that may generator exact-assembly fields be reconsidered."
                if product_component_witness_bridge_present
                else "Prove the factor-to-product component witness bridge "
                "that turns factor-level error/absolute bounds into the "
                "product-summand inputs consumed by the generic "
                "product-error budget bridge."
                if nominal_scale_abs_bound_present
                else "Add the concrete nominal-scale absolute bound consumed by "
                "the product-error bridge, then generate/import the remaining "
                "product-summand error and absolute witnesses."
                if product_error_budget_bridge_present
                else "Propagate the checked scale and omega-anchor interval losses "
                "through omegaPrime*shapeSq + omega*shapeSqDeriv and prove the "
                "same-normalization product-error budget before setting any "
                "generator exact-assembly fields."
                if nominal_source_interval_bridge_present
                else "Prove the same-normalization scale/source bridge: replace the "
                "nominal scale and nominal omega anchor by proof-grade interval "
                "or exact sources that connect the component product stream to "
                "the active raw closed-form derivative coefficient budget."
                if nominal_object_bridge_present
                else (
                    "Build proof-grade exact rational assembledRawDerivCoeff and "
                    "ResidualTaylorCoeff objects from the component product stream, "
                    "using rawOmegaTaylorCauchyCoeff for omegaPrime*shapeSq and "
                    "omega*shapeSqDeriv.  Do not spend this bridge as an active "
                    "raw closed-form proof until the scale and component coefficient "
                    "sources are checked in the same normalization."
                )
                if checked_cauchy_product_bridge
                else (
                    "Prove the generic Cauchy product bridge "
                    "rawOmegaATaylorPolynomial_mul_coeff and define the nominal "
                    "Cauchy coefficient stream.  Only after that build proof-grade "
                    "exact rational assembledRawDerivCoeff and ResidualTaylorCoeff "
                    "objects from the component product stream."
                )
            ),
            "downstreamAfterThisCloses": [
                "generate proof-grade ShapeSqDeriv rows 2..15 and order16",
                "prove primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid",
                "assemble raw derivative residual interval payload",
                "prove the final direct residual interval theorem",
            ],
        },
    }


def render_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = [
        "# Step33A.1-A Sub0 Component Assembly Stream Ledger",
        "",
        f"Schema: `{report['schema']}`",
        "",
        f"Status: `{report['status']}`",
        "",
        f"First failure: `{report['firstFailure']}`",
        "",
        f"Local assembly gap: `{report['localAssemblyGap']}`",
        "",
        f"Route-level gap: `{report['routeLevelGap']}`",
        "",
        f"Zero-extension bridge gap: `{report['zeroExtensionBridgeGap']}`",
        "",
        f"Boundary: {report['proofBoundary']}",
        "",
        "## Browser/Proshka Decision",
        "",
    ]
    decision = report["browserProshkaDecision"]
    lines.append(f"- chosen: `{decision['chosen']}`")
    lines.append(f"- first patch/theorem: `{decision['firstPatchOrTheorem']}`")
    lines.append(f"- failure code if fails: `{decision['failureCodeIfFails']}`")
    lines.append(f"- why smallest: {decision['whySmallest']}")
    lines.append("")
    lines.append("Do not:")
    for item in decision["doNot"]:
        lines.append(f"- {item}")

    followup = report["browserProshkaFollowupDecision"]
    lines.extend(
        [
            "",
            "## Browser/Proshka Follow-up Decision",
            "",
            f"- chosen: `{followup['chosen']}`",
            f"- first patch/theorem: `{followup['firstPatchOrTheorem']}`",
            f"- coefficient definition: `{followup['coefficientDefinition']}`",
            f"- failure code if fails: `{followup['failureCodeIfFails']}`",
            f"- mismatch code after product bridge: `{followup['mismatchCodeAfterProductBridge']}`",
            f"- why smallest: {followup['whySmallest']}",
            "",
            "Do not:",
        ]
    )
    for item in followup["doNot"]:
        lines.append(f"- {item}")

    target = report["targetTheoremContract"]
    lines.extend(
        [
            "",
            "## Target Theorem Contract",
            "",
            f"- name: `{target['name']}`",
            f"- file: `{target['file']}`",
            f"- status: `{target['status']}`",
            "",
            "```text",
            target["statementAscii"],
            "```",
            "",
            "Partial Lean-checked same-degree theorem:",
            "",
            f"- name: `{target['partialSameDegreeTheorem']}`",
            f"- failure code if not enough: `{target['partialSameDegreeFailureCodeIfNotEnough']}`",
            f"- zero-extension theorem: `{target['zeroExtensionTheorem']}`",
            f"- parameterized full theorem: `{target['parameterizedFullTheorem']}`",
            "",
            "```text",
            target["partialSameDegreeStatementAscii"],
            "```",
            "",
            "Required coefficient definitions:",
        ]
    )
    for name in target["coeffDefinitionsRequired"]:
        lines.append(f"- `{name}`")

    formula = report["componentAssemblyFormula"]
    lines.extend(
        [
            "",
            "## Assembly Formula",
            "",
            f"- scale: `{formula['scale']}`",
            f"- raw closed form: `{formula['rawClosedForm']}`",
            f"- assembled raw derivative coeff: `{formula['assembledRawDerivCoeffFormula']}`",
            f"- residual Taylor coeff: `{formula['residualTaylorCoeffFormula']}`",
            f"- center: `{formula['center']}`",
            f"- component degree: `{formula['componentDegree']}`",
            f"- assembled degree: `{formula['assembledDegree']}`",
            f"- warning: {formula['normalizationWarning']}",
            "",
            "## Source Files",
            "",
        ]
    )
    for source_name, source in report["sourceFiles"].items():
        lines.append(f"### {source_name}")
        lines.append("")
        lines.append(f"- path: `{source['path']}`")
        lines.append(f"- exists: `{source['exists']}`")
        if "symbols" in source:
            for sym, info in source["symbols"].items():
                lines.append(
                    f"- `{sym}`: found=`{info['found']}`, line=`{info['line']}`"
                )
        else:
            for key in ["schema", "status", "firstFailure"]:
                lines.append(f"- {key}: `{source[key]}`")
        lines.append("")

    lines.extend(["## Current Component Field State", ""])
    for key, value in report["currentComponentFieldState"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Guard", ""])
    for key, value in report["guard"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(["", "## Decision", ""])
    final_decision = report["decision"]
    lines.append(
        f"- can generate rows 2..15 now: `{final_decision['canGenerateRows2To15Now']}`"
    )
    lines.append(
        "- can use parameterized Lean crosswalk now: "
        f"`{final_decision['canUseParameterizedLeanCrosswalkNow']}`"
    )
    lines.append(
        "- can emit object-level crosswalk now: "
        f"`{final_decision['canEmitObjectLevelCrosswalkNow']}`"
    )
    lines.append(
        "- next failure if Cauchy bridge missing: "
        f"`{final_decision['nextFailureIfCauchyBridgeMissing']}`"
    )
    lines.append(f"- next patch: {final_decision['nextPatch']}")
    lines.append("")
    lines.append("Downstream after this closes:")
    for item in final_decision["downstreamAfterThisCloses"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    report = build_report()
    OUTPUT_JSON.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    OUTPUT_MD.write_text(render_markdown(report), encoding="utf-8")
    print(
        "status={status} first_failure={failure}".format(
            status=report["status"],
            failure=report["firstFailure"],
        )
    )


if __name__ == "__main__":
    main()
