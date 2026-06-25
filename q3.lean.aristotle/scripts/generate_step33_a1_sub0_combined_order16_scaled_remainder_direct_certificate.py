#!/usr/bin/env python3
"""Fail-closed preflight for the direct scaled-remainder certificate.

This is the generator named by the Step33A.1-A post-budget-kill route review.
It is proof-producing only when proof-grade whole-expression interval rows are
present.  In the current repository state those rows are missing, so the script
emits a precise certificate preflight ledger and refuses to write the Lean
payload.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_combined_order16_"
    "scaled_remainder_direct_certificate.v16"
)

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "Q3" / "Proofs"
REQUEST_DIR = ROOT / "ACTIVE" / "requests" / "step33_bootstrap"

DIRECT_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean"
)
ZERO_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderZeroModelPayload.lean"
)
NONZERO_MODEL_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean"
)
BIASED_LOCAL_MODEL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualLocalModelSegmentCert.lean"
)
BIASED_SOURCE_HORNER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerCert.lean"
)
BIASED_SOURCE_HORNER_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload.lean"
)
DIRECT_HORNER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean"
)
DIRECT_HORNER_SMOKE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean"
)
DIRECT_SOURCE_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean"
)
DIRECT_HORNER_SOURCE_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean"
)
DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedTaylorSource.lean"
)
DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedSourceIntervalCert.lean"
)
DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedLowDegreeSource.lean"
)
DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0DerivativeShift.lean"
)
DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0CenterAudit.lean"
)
DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean"
)
DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean"
)
DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0"
    "RawD17SharpTwoSegmentBudgetKill.lean"
)
NOMINAL_POLYNOMIAL_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean"
)
ACTIVE_ACTUAL_REMAINDER_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRemainderBridge.lean"
)
ACTIVE_ACTUAL_HORNER_SEGMENT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean"
)
ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean"
)
ACTIVE_ACTUAL_DEGREE0_AUDIT_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0CenterBudgetAudit.lean"
)
BIASED_INTERVAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval.lean"
)
FACTOR_BUDGET_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean"
)

LEAN_OUT = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean"
)
JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.md"
)

PAYLOAD_LEDGER = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)
BIASED_SOURCE_HORNER_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_biased_residual_source_horner_cert.json"
)
BIASED_LOCAL_MODEL_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_biased_residual_local_model_segments.json"
)
COMPONENT_TAYLOR_RESIDUAL_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
SHAPESQ_DERIV_TIGHT_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_shapesq_deriv_tight_payload.json"
)
ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER = (
    REQUEST_DIR / "step33_a1_sub0_active_actual_horner_row_source.json"
)
WHOLE_EXPRESSION_PILOT_SCRIPT = (
    ROOT
    / "scripts"
    / "generate_step33_a1_sub0_combined_order16_scaled_remainder_whole_expression_pilot.py"
)
WHOLE_EXPRESSION_PILOT_JSON = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_whole_expression_pilot.json"
)
WHOLE_EXPRESSION_PILOT_MD = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_whole_expression_pilot.md"
)

TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_interval_generated"
)
TARGET_SOURCE_PROP_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_sourceProp_generated"
)
TARGET_EXPRESSION = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16"
    "ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0"
    "CombinedOrder16NonzeroModelPoly eta"
)
TARGET_BUDGET = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16Biased"
    "ResidualRemainderAbs"
)
FIRST_PROOF_PRODUCING_GENERATOR = (
    "scripts/generate_step33_a1_sub0_combined_order16_"
    "scaled_remainder_direct_certificate.py"
)
DIRECT_ROW_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_ROW_SOURCE_GAP"
)
DIRECT_HORNER_LEDGER_INTERFACE_MISMATCH = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_HORNER_LEDGER_INTERFACE_MISMATCH"
)
DIRECT_HORNER_RECEIVER_VALIDATION_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_HORNER_RECEIVER_VALIDATION_GAP"
)
INTERVAL_CERT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "NONZERO_MODEL_INTERVAL_CERT_GAP"
)
FACTOR_BUDGET_KILL = (
    "STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_"
    "ORDER16_BUDGET_CONSTANT_FAIL"
)
COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP"
)
COMPUTER_USE_REVIEW_URL = (
    "https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/"
    "c/6a32cac5-cc54-83eb-b010-097faa30ac6b"
)
DIRECT_HORNER_DATA_OBJECT = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
    "ScaledRemainderDirectHornerData"
)
DIRECT_HORNER_VALID_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainderDirectHorner_valid"
)
COLLAPSED_SEGMENT_REMAINDER_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainder_collapsed_segment_remainder"
)
COLLAPSED_TAYLOR_RECEIVER_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainder_"
    "collapsed_segment_remainder_of_centerJet15_order16"
)
COLLAPSED_TAYLOR_RECEIVER_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_TAYLOR_RECEIVER_GAP"
)
COLLAPSED_CENTER_JETS_ORDER16_ROW_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_CENTER_JETS_"
    "ORDER16_ROW_SOURCE_GAP"
)
COLLAPSED_SOURCE_INTERVAL_CERT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_SOURCE_"
    "INTERVAL_CERT_GAP"
)
COLLAPSED_SOURCE_INTERVAL_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_SOURCE_"
    "INTERVAL_ROWS_GAP"
)
COLLAPSED_DEGREE0_D17_SIGNED_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "D17_SIGNED_SOURCE_GAP"
)
COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "POLY_DERIV_SIGNED_SOURCE_GAP"
)
COLLAPSED_DEGREE0_RAW_D17_LOCAL_INTERVAL_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_LOCAL_INTERVAL_ROWS_GAP"
)
COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SIGNED_FACTOR_ROWS_GAP"
)
COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "RAW_D17_SHARP_TWO_SEGMENT_BUDGET_CONSTANT_FAIL"
)
COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_"
    "BUDGET_CONSTANT_FAIL"
)
ACTIVE_ACTUAL_SEGMENT_REMAINDER_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_SOURCE_GAP"
)
ACTIVE_ACTUAL_HORNER_SEGMENT_RECEIVER_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_SEGMENT_RECEIVER_GAP"
)
ACTIVE_ACTUAL_HORNER_FAMILY_ALIGNMENT_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_ALIGNMENT_GAP"
)
ACTIVE_ACTUAL_SEGMENT_REMAINDER_ROW_SOURCE_GAP = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP"
)
ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_FAIL = (
    "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_"
    "DIRECT_BUDGET_CONSTANT_FAIL_FOR_PAYLOAD"
)
WHOLE_EXPRESSION_PILOT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "WHOLE_EXPRESSION_PILOT_GAP"
)
WHOLE_EXPRESSION_PILOT_SOURCE_DATA_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "WHOLE_EXPRESSION_PILOT_SOURCE_DATA_GAP"
)
ACTIVE_ACTUAL_SEGMENT_REMAINDER_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "activeActual_order16_segment_remainder"
)
ACTIVE_ACTUAL_HORNER_SEGMENT_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "activeActual_order16_segment_remainder_of_horner_cert"
)
ACTIVE_ACTUAL_COLLAPSED_HORNER_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "collapsed_segment_remainder_of_activeActualHorner"
)
ACTIVE_ACTUAL_HORNER_FAMILY_VALID_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "directHornerFamily_valid_of_activeActualHornerFamily"
)
ACTIVE_ACTUAL_HORNER_FAMILY_PAYLOAD_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "directPayloadTarget_of_activeActualHornerFamily"
)
ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_KILL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "activeActual_degree0_directPayloadBudget_fail_rat"
)

DIRECT_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval",
]
ZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual",
]
NONZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat",
]
BIASED_LOCAL_MODEL_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert",
    "theorem to_residualSourceProp",
    "theorem to_order16DirectIntervalValid",
]
BIASED_SOURCE_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert",
    "theorem to_residualSourceProp",
    "theorem to_order16DirectIntervalValid",
]
BIASED_DIRECT_ADAPTER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs",
    "primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound",
]
DIRECT_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert",
    "def poly",
    "def toDirectSegment",
    "structure Valid",
    "theorem directInterval",
    "theorem to_directSegmentValid",
    "def hornerTail",
    "theorem hornerTail_zero_eq_poly",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert",
    "theorem polyRange",
    "theorem of_horner_range",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert",
    "def toDirectFamily",
    "theorem to_directFamilyValid",
    "theorem to_directPayloadTarget",
    "theorem to_nonzeroModelSourceProp",
]
DIRECT_HORNER_SMOKE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp",
]
DIRECT_SOURCE_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_canonicalSourceProp_of_collapsed_interval",
]
DIRECT_HORNER_SOURCE_BRIDGE_SYMBOLS = [
    "theorem of_collapsed_horner_range",
    "theorem valid_of_collapsed_horner_rows",
]
DIRECT_COLLAPSED_TAYLOR_SOURCE_SYMBOLS = [
    COLLAPSED_TAYLOR_RECEIVER_THEOREM,
    "Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert",
    "def toDirectHornerSegment",
    "theorem remainder_bound",
    "theorem to_directHorner_valid",
]
DIRECT_COLLAPSED_SOURCE_INTERVAL_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert",
    "structure Valid",
    "theorem centerJet",
    "theorem order16",
    "theorem to_collapsedTaylorValid",
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsedTaylorValid_of_source_interval"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsed_segment_remainder_of_source_interval"
    ),
]

DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff",
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsed_degree0_remainder"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsed_degree0_remainder_of_deriv_bound"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsed_degree0_remainder_of_signedD17_source"
    ),
    COLLAPSED_DEGREE0_D17_SIGNED_SOURCE_GAP,
]

DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_differentiableAt",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedExpression_deriv_eq_activeActualD17_sub_nominalOrder16PolyDeriv"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsed_degree0_remainder_of_polyDeriv_signedD17_source"
    ),
    COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP,
]

DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0",
    "primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs",
    "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_center",
    "primaryFiniteRow0Parent0Split100Sub0_directCollapsed_degree0_hCenter_generated",
    (
        "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
        "collapsed_degree0_remainder_of_center_and_polyDeriv_source"
    ),
]

DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr",
    "primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget",
    "Step33Sub0CollapsedDegree0SignedSourceCert",
    "structure Valid",
    "theorem valid_of_signed_interval_and_budget",
    "theorem to_hSignedD17PolyDeriv",
    "theorem to_collapsed_degree0_remainder",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_hSignedD17PolyDeriv_of_signed_interval"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_signed_interval_and_budget"
    ),
    "Step33Sub0CollapsedDegree0SignedSourceSegmentCert",
    "Step33Sub0CollapsedDegree0RawPolySegmentCert where",
    "def toSignedSegmentCert",
    "namespace Step33Sub0CollapsedDegree0RawPolySegmentCert",
    "theorem valid_of_raw_poly_intervals",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_signedSegmentValid_of_raw_poly_intervals"
    ),
    "Step33Sub0CollapsedDegree0SignedSourceSegmentCover",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_signed_segment_cover_and_budget"
    ),
    "Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert",
    "Step33Sub0CollapsedDegree0RawPolySegmentCover",
    "Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert",
    "theorem to_signedSegmentFamilyValid",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_raw_poly_segment_family_cert"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_degree0_remainder_of_signed_segment_family_cert"
    ),
    "primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_source_cert",
]

DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm",
    "Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert",
    "def termCornerRows",
    "def toRawPolySegmentCert",
    "namespace Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert",
    "theorem to_termRows",
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

DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_SYMBOLS = [
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_sharp_twoSegment_budget_fail_rat"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "rawD17_signedFactor_sharp_twoSegment_budget_not_spendable"
    ),
]

NOMINAL_POLYNOMIAL_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff",
    "primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly",
    "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_eq",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly"
    ),
]
ACTIVE_ACTUAL_REMAINDER_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsedCoeffOf_poly_eq_activePoly_sub_nominal"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_segment_remainder_of_activeActual"
    ),
]
ACTIVE_ACTUAL_HORNER_SEGMENT_SYMBOLS = [
    "Step33Sub0ActiveActualOrder16HornerSegmentCert",
    "structure Valid",
    "theorem to_activeActual_order16_segment_remainder",
    "theorem to_collapsed_segment_remainder",
    ACTIVE_ACTUAL_HORNER_SEGMENT_THEOREM,
    ACTIVE_ACTUAL_COLLAPSED_HORNER_THEOREM,
]
ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_SYMBOLS = [
    "Step33Sub0ActiveActualOrder16HornerDirectSegmentCert",
    "Step33Sub0ActiveActualOrder16HornerDirectRangeCert",
    "Step33Sub0ActiveActualOrder16HornerFamilyCert",
    "theorem to_directHornerFamilyValid",
    ACTIVE_ACTUAL_HORNER_FAMILY_VALID_THEOREM,
    ACTIVE_ACTUAL_HORNER_FAMILY_PAYLOAD_THEOREM,
    "primaryFiniteRow0Parent0Split100Sub0_nonzeroModelSourceProp_of_activeActualHornerFamily",
]
DIRECT_CONCRETE_PAYLOAD_SYMBOLS = [
    DIRECT_HORNER_DATA_OBJECT,
    DIRECT_HORNER_VALID_THEOREM,
    TARGET_THEOREM,
    TARGET_SOURCE_PROP_THEOREM,
]
FACTOR_BUDGET_KILL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail",
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
        raise ValueError(f"{path}: expected object root")
    return data


def symbol_lines(path: Path, symbols: list[str]) -> dict[str, dict[str, Any]]:
    text = read_text(path)
    lines = text.splitlines()
    out: dict[str, dict[str, Any]] = {}
    for symbol in symbols:
        line_no = next(
            (index for index, line in enumerate(lines, start=1) if symbol in line),
            None,
        )
        out[symbol] = {"present": line_no is not None, "line": line_no}
    return out


def all_present(items: dict[str, dict[str, Any]]) -> bool:
    return all(bool(item["present"]) for item in items.values())


def ledger_bool(data: dict[str, Any], key: str) -> bool:
    return bool(data.get(key))


def compact_ledger(path: Path, keys: list[str]) -> dict[str, Any]:
    data = load_json(path)
    out: dict[str, Any] = {"path": rel(path), "exists": bool(data)}
    for key in keys:
        out[key] = data.get(key)
    return out


def build_whole_expression_pilot_contract() -> dict[str, Any]:
    script_exists = WHOLE_EXPRESSION_PILOT_SCRIPT.exists()
    pilot_output = load_json(WHOLE_EXPRESSION_PILOT_JSON)
    output_loaded = bool(pilot_output)
    phase2_result = (
        pilot_output.get("phase2ResultNow")
        if output_loaded
        else (
            "NOT_RUN_MISSING_PILOT_SCRIPT"
            if not script_exists
            else "NOT_RUN_READY_TO_RUN"
        )
    )
    first_failure = (
        pilot_output.get("currentGap")
        if output_loaded
        else (
            WHOLE_EXPRESSION_PILOT_GAP
            if not script_exists
            else DIRECT_ROW_SOURCE_GAP
        )
    )
    status = (
        pilot_output.get("status")
        if output_loaded
        else ("ready_to_run" if script_exists else "missing_pilot_script")
    )
    return {
        "phase": "Phase2_Cheap_Whole_Expression_Pilot",
        "status": status,
        "proofGrade": bool(pilot_output.get("proofGrade", False)),
        "pilotScript": rel(WHOLE_EXPRESSION_PILOT_SCRIPT),
        "pilotScriptExists": script_exists,
        "pilotOutputJson": rel(WHOLE_EXPRESSION_PILOT_JSON),
        "pilotOutputMarkdown": rel(WHOLE_EXPRESSION_PILOT_MD),
        "pilotOutputLoaded": output_loaded,
        "pilotVerdict": pilot_output.get("pilotVerdict"),
        "sourceDataReady": pilot_output.get("sourceDataReady"),
        "sourceDataStatus": pilot_output.get("sourceDataStatus"),
        "blockingMissingArtifacts": [
            item
            for item in pilot_output.get("missingArtifacts", [])
            if not item.get("present", False)
        ],
        "commandWhenImplemented": (
            "python3 scripts/generate_step33_a1_sub0_combined_order16_"
            "scaled_remainder_whole_expression_pilot.py"
        ),
        "mustEvaluateExpression": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderCollapsedExpression"
        ),
        "mustFeedReceiverTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
        "receiverField": (
            "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert."
            "Valid.directRemainder"
        ),
        "targetInterval": "Set.Icc (0 : Real) ((1 : Real) / 10)",
        "preserveCancellation": True,
        "requiredRows": [
            "same-target collapsedExpression coefficient stream",
            "proof-grade collapsedExpression segment remainder rows",
            "Horner stage lower/upper rows",
            "exact segment cover of Set.Icc 0 (1/10)",
            "final lower/upper budget rows against BiasedResidualRemainderAbs",
        ],
        "acceptedPilotVerdicts": [
            "PASS_STABLE_MARGIN",
            "NEGATIVE_MARGIN",
            "UNSTABLE_MARGIN",
            "SEGMENT_EXPLOSION",
        ],
        "phase2ResultNow": phase2_result,
        "firstFailureCode": first_failure,
        "decisionRule": (
            "If the pilot is not PASS_STABLE_MARGIN, stop subdividing this "
            "row class and record NEGATIVE_MARGIN, UNSTABLE_MARGIN, or "
            "SEGMENT_EXPLOSION as the route decision."
        ),
        "doNotUse": [
            "factorwise raw-D17 budget spending",
            "separate activeActual and nominal budgets",
            "sampled rows as proof",
            "DirectConcretePayload.lean before all required rows pass",
        ],
        "nextImplementablePatch": (
            pilot_output.get("nextImplementablePatch")
            if output_loaded
            else (
                "Implement the missing high-precision whole-expression pilot "
                "script so it reports exactly PASS_STABLE_MARGIN, "
                "NEGATIVE_MARGIN, UNSTABLE_MARGIN, or SEGMENT_EXPLOSION before "
                "any payload emission."
            )
        ),
    }


def nested_get(data: dict[str, Any], path: list[str], default: Any = None) -> Any:
    current: Any = data
    for key in path:
        if not isinstance(current, dict) or key not in current:
            return default
        current = current[key]
    return current


def build_upstream_row_source_audit(
    component_ledger: dict[str, Any],
    shapesq_tight_ledger: dict[str, Any],
) -> dict[str, Any]:
    component_first_failure = component_ledger.get("firstFailure")
    shapesq_first_failure = shapesq_tight_ledger.get("firstFailure")
    upstream_first_failure = (
        component_first_failure
        or shapesq_first_failure
        or DIRECT_ROW_SOURCE_GAP
    )
    component_gap_is_active = (
        component_first_failure == COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
        or shapesq_first_failure == COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
    )

    return {
        "purpose": (
            "Refine the direct row-source gap to the nearest local proof-source "
            "obstruction without claiming the final scaled-remainder interval."
        ),
        "directFailureCode": DIRECT_ROW_SOURCE_GAP,
        "firstConcreteUpstreamFailureCode": upstream_first_failure,
        "componentTaylorRemainderGapActive": component_gap_is_active,
        "componentTaylorResidualLedger": {
            "path": rel(COMPONENT_TAYLOR_RESIDUAL_LEDGER),
            "exists": bool(component_ledger),
            "schema": component_ledger.get("schema"),
            "status": component_ledger.get("status"),
            "firstFailure": component_first_failure,
            "routeReviewRecommendedOption": nested_get(
                component_ledger,
                ["componentTaylorRemainderRouteReview", "recommendedOption"],
            ),
            "failureCodeIfRowsMissing": nested_get(
                component_ledger,
                ["componentTaylorRemainderRouteReview", "failureCodeIfRowsMissing"],
            ),
            "failureCodeIfBudgetFalse": nested_get(
                component_ledger,
                ["componentTaylorRemainderRouteReview", "failureCodeIfBudgetFalse"],
            ),
            "firstTheoremObject": nested_get(
                component_ledger,
                ["componentTaylorRemainderRouteReview", "firstTheoremObject"],
            ),
            "shapeSqDerivTightValid": nested_get(
                component_ledger,
                ["existingLeanInputs", "shapeSqDerivTightValid"],
            ),
            "shapeSqDerivTightTaylorSource": nested_get(
                component_ledger,
                ["existingLeanInputs", "shapeSqDerivTightTaylorSource"],
            ),
            "componentPropagationRemainderAbs": nested_get(
                component_ledger,
                ["generatorFields", "componentPropagationRemainderAbs"],
            ),
            "residualTaylorRemainderAbs": nested_get(
                component_ledger,
                ["generatorFields", "residualTaylorRemainderAbs"],
            ),
        },
        "shapeSqDerivTightLedger": {
            "path": rel(SHAPESQ_DERIV_TIGHT_LEDGER),
            "exists": bool(shapesq_tight_ledger),
            "status": shapesq_tight_ledger.get("status"),
            "firstFailure": shapesq_first_failure,
            "nextPatch": nested_get(shapesq_tight_ledger, ["decision", "nextPatch"]),
            "guardPasses": nested_get(
                shapesq_tight_ledger, ["sameCoefficientGuard", "guardPasses"]
            ),
            "tightCoeffObjectsPresentInLean": nested_get(
                shapesq_tight_ledger,
                ["sameCoefficientGuard", "tightCoeffObjectsPresentInLean"],
            ),
            "tightTaylorSourceTheoremPresentInLean": nested_get(
                shapesq_tight_ledger,
                ["sameCoefficientGuard", "tightTaylorSourceTheoremPresentInLean"],
            ),
            "tightValidTheoremPresentInLean": nested_get(
                shapesq_tight_ledger,
                ["sameCoefficientGuard", "tightValidTheoremPresentInLean"],
            ),
        },
        "verdict": (
            "ShapeSqDeriv tight same-coefficient support is checked but "
            "nonfinal.  The component Taylor remainder gap is a recorded "
            "upstream obstruction, but the Computer Use route-fork review "
            "selects the direct whole-expression row stream as the active "
            "next patch, so componentTaylorRemainder is not an obligatory "
            "intermediate layer."
            if component_gap_is_active
            else "No more specific upstream row-source gap was found in the local ledgers."
        ),
        "proofGradeForDirectCertificate": False,
        "spendableForTargetTheorem": False,
        "doNotUseAsClosure": [
            "ShapeSqDeriv tight payload alone",
            "old rows0..11 product assembly budget",
            "stale ShapeSqDeriv rows gap",
        ],
        "nextImplementablePatch": (
            "Build the direct whole-expression rational/interval Horner row "
            "stream for the checked collapsedExpression target."
        ),
    }


def build_ledger() -> dict[str, Any]:
    payload_ledger = load_json(PAYLOAD_LEDGER)
    source_horner_ledger = load_json(BIASED_SOURCE_HORNER_LEDGER)
    local_model_ledger = load_json(BIASED_LOCAL_MODEL_LEDGER)
    component_taylor_ledger = load_json(COMPONENT_TAYLOR_RESIDUAL_LEDGER)
    shapesq_tight_ledger = load_json(SHAPESQ_DERIV_TIGHT_LEDGER)
    active_actual_horner_row_source_ledger = load_json(
        ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER
    )

    direct_payload_symbols = symbol_lines(DIRECT_PAYLOAD_FILE, DIRECT_PAYLOAD_SYMBOLS)
    zero_model_symbols = symbol_lines(ZERO_MODEL_FILE, ZERO_MODEL_SYMBOLS)
    nonzero_model_symbols = symbol_lines(NONZERO_MODEL_FILE, NONZERO_MODEL_SYMBOLS)
    local_model_symbols = symbol_lines(
        BIASED_LOCAL_MODEL_FILE, BIASED_LOCAL_MODEL_SYMBOLS
    )
    source_horner_symbols = symbol_lines(
        BIASED_SOURCE_HORNER_FILE, BIASED_SOURCE_HORNER_SYMBOLS
    )
    biased_adapter_symbols = symbol_lines(
        BIASED_SOURCE_HORNER_PAYLOAD_FILE, BIASED_DIRECT_ADAPTER_SYMBOLS
    )
    direct_horner_symbols = symbol_lines(DIRECT_HORNER_FILE, DIRECT_HORNER_SYMBOLS)
    direct_horner_smoke_symbols = symbol_lines(
        DIRECT_HORNER_SMOKE_FILE, DIRECT_HORNER_SMOKE_SYMBOLS
    )
    direct_source_bridge_symbols = symbol_lines(
        DIRECT_SOURCE_BRIDGE_FILE, DIRECT_SOURCE_BRIDGE_SYMBOLS
    )
    direct_horner_source_bridge_symbols = symbol_lines(
        DIRECT_HORNER_SOURCE_BRIDGE_FILE, DIRECT_HORNER_SOURCE_BRIDGE_SYMBOLS
    )
    direct_collapsed_taylor_source_symbols = symbol_lines(
        DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE, DIRECT_COLLAPSED_TAYLOR_SOURCE_SYMBOLS
    )
    direct_collapsed_source_interval_symbols = symbol_lines(
        DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE,
        DIRECT_COLLAPSED_SOURCE_INTERVAL_SYMBOLS,
    )
    direct_collapsed_low_degree_source_symbols = symbol_lines(
        DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE,
        DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_SYMBOLS,
    )
    direct_collapsed_degree0_derivative_shift_symbols = symbol_lines(
        DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE,
        DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_SYMBOLS,
    )
    direct_collapsed_degree0_center_audit_symbols = symbol_lines(
        DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE,
        DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_SYMBOLS,
    )
    direct_collapsed_degree0_signed_source_symbols = symbol_lines(
        DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE,
        DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_SYMBOLS,
    )
    direct_collapsed_degree0_raw_d17_signed_factor_rows_symbols = symbol_lines(
        DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE,
        DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_SYMBOLS,
    )
    direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_symbols = (
        symbol_lines(
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_FILE,
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_SYMBOLS,
        )
    )
    nominal_polynomial_bridge_symbols = symbol_lines(
        NOMINAL_POLYNOMIAL_BRIDGE_FILE, NOMINAL_POLYNOMIAL_BRIDGE_SYMBOLS
    )
    active_actual_remainder_bridge_symbols = symbol_lines(
        ACTIVE_ACTUAL_REMAINDER_BRIDGE_FILE,
        ACTIVE_ACTUAL_REMAINDER_BRIDGE_SYMBOLS,
    )
    active_actual_horner_segment_symbols = symbol_lines(
        ACTIVE_ACTUAL_HORNER_SEGMENT_FILE,
        ACTIVE_ACTUAL_HORNER_SEGMENT_SYMBOLS,
    )
    active_actual_horner_family_bridge_symbols = symbol_lines(
        ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE,
        ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_SYMBOLS,
    )
    direct_concrete_payload_symbols = symbol_lines(
        LEAN_OUT, DIRECT_CONCRETE_PAYLOAD_SYMBOLS
    )
    factor_budget_symbols = symbol_lines(FACTOR_BUDGET_FILE, FACTOR_BUDGET_KILL_SYMBOLS)
    direct_horner_receiver_present = all_present(direct_horner_symbols)
    direct_horner_smoke_present = all_present(direct_horner_smoke_symbols)
    direct_source_bridge_present = all_present(direct_source_bridge_symbols)
    direct_horner_source_bridge_present = all_present(
        direct_horner_source_bridge_symbols
    )
    direct_collapsed_taylor_source_present = all_present(
        direct_collapsed_taylor_source_symbols
    )
    direct_collapsed_source_interval_present = all_present(
        direct_collapsed_source_interval_symbols
    )
    direct_collapsed_low_degree_source_present = all_present(
        direct_collapsed_low_degree_source_symbols
    )
    direct_collapsed_degree0_derivative_shift_present = all_present(
        direct_collapsed_degree0_derivative_shift_symbols
    )
    direct_collapsed_degree0_center_audit_present = all_present(
        direct_collapsed_degree0_center_audit_symbols
    )
    direct_collapsed_degree0_signed_source_present = all_present(
        direct_collapsed_degree0_signed_source_symbols
    )
    direct_collapsed_degree0_raw_d17_signed_factor_rows_present = all_present(
        direct_collapsed_degree0_raw_d17_signed_factor_rows_symbols
    )
    direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present = (
        all_present(
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_symbols
        )
    )
    nominal_polynomial_bridge_present = all_present(
        nominal_polynomial_bridge_symbols
    )
    active_actual_remainder_bridge_present = all_present(
        active_actual_remainder_bridge_symbols
    )
    active_actual_horner_segment_receiver_present = all_present(
        active_actual_horner_segment_symbols
    )
    active_actual_horner_family_bridge_present = all_present(
        active_actual_horner_family_bridge_symbols
    )
    direct_concrete_payload_present = all_present(direct_concrete_payload_symbols)
    direct_horner_receiver_lean_checked = direct_horner_receiver_present
    direct_horner_smoke_lean_checked = direct_horner_smoke_present
    direct_source_bridge_lean_checked = direct_source_bridge_present
    direct_horner_source_bridge_lean_checked = direct_horner_source_bridge_present
    direct_collapsed_taylor_source_lean_checked = (
        direct_collapsed_taylor_source_present
    )
    direct_collapsed_source_interval_lean_checked = (
        direct_collapsed_source_interval_present
    )
    direct_collapsed_low_degree_source_lean_checked = (
        direct_collapsed_low_degree_source_present
    )
    direct_collapsed_degree0_derivative_shift_lean_checked = (
        direct_collapsed_degree0_derivative_shift_present
    )
    direct_collapsed_degree0_center_audit_lean_checked = (
        direct_collapsed_degree0_center_audit_present
    )
    direct_collapsed_degree0_signed_source_lean_checked = (
        direct_collapsed_degree0_signed_source_present
    )
    direct_collapsed_degree0_raw_d17_signed_factor_rows_lean_checked = (
        direct_collapsed_degree0_raw_d17_signed_factor_rows_present
    )
    direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_lean_checked = (
        direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present
    )
    nominal_polynomial_bridge_lean_checked = nominal_polynomial_bridge_present
    active_actual_remainder_bridge_lean_checked = (
        active_actual_remainder_bridge_present
    )
    active_actual_horner_segment_receiver_lean_checked = (
        active_actual_horner_segment_receiver_present
    )
    active_actual_horner_family_bridge_lean_checked = (
        active_actual_horner_family_bridge_present
    )

    receiver_ready = (
        all_present(direct_payload_symbols)
        and all_present(zero_model_symbols)
        and all_present(nonzero_model_symbols)
    )
    immediate_failure_code = (
        DIRECT_HORNER_RECEIVER_VALIDATION_GAP
        if direct_horner_smoke_present and not direct_horner_smoke_lean_checked
        else DIRECT_ROW_SOURCE_GAP
    )
    upstream_row_source_audit = build_upstream_row_source_audit(
        component_taylor_ledger,
        shapesq_tight_ledger,
    )
    upstream_failure_code = DIRECT_ROW_SOURCE_GAP
    direct_collapsed_taylor_row_failure = (
        DIRECT_ROW_SOURCE_GAP
        if direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present
        else COLLAPSED_DEGREE0_RAW_D17_LOCAL_INTERVAL_ROWS_GAP
        if direct_collapsed_degree0_derivative_shift_present
        else COLLAPSED_DEGREE0_D17_SIGNED_SOURCE_GAP
        if direct_collapsed_low_degree_source_present
        else COLLAPSED_SOURCE_INTERVAL_ROWS_GAP
        if direct_collapsed_source_interval_present
        else COLLAPSED_SOURCE_INTERVAL_CERT_GAP
        if direct_collapsed_taylor_source_present
        else COLLAPSED_TAYLOR_RECEIVER_GAP
    )
    direct_collapsed_degree0_raw_d17_first_concrete_gap = (
        COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_FAIL
        if direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present
        else COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_GAP
        if direct_collapsed_degree0_raw_d17_signed_factor_rows_present
        else COLLAPSED_DEGREE0_RAW_D17_LOCAL_INTERVAL_ROWS_GAP
        if direct_collapsed_degree0_derivative_shift_present
        else direct_collapsed_taylor_row_failure
    )
    upstream_failure_code = (
        direct_collapsed_degree0_raw_d17_first_concrete_gap
        if direct_collapsed_degree0_derivative_shift_present
        else direct_collapsed_taylor_row_failure
    )
    payload_first_object = nested_get(
        payload_ledger,
        ["directWholeExpressionRowReview", "firstObject"],
    )
    payload_valid_theorem = nested_get(
        payload_ledger,
        ["directHornerRowRouteReview", "validTheorem"],
    )
    payload_horner_interface_matches = (
        payload_first_object == DIRECT_HORNER_DATA_OBJECT
        and payload_valid_theorem == DIRECT_HORNER_VALID_THEOREM
    )

    proof_rows_present = (
        ledger_bool(payload_ledger, "directNonzeroModelIntervalRowsLeanChecked")
        or ledger_bool(source_horner_ledger, "sourceRemainderBoundLeanChecked")
        or ledger_bool(local_model_ledger, "sourceRowsLeanChecked")
        or ledger_bool(
            active_actual_horner_row_source_ledger,
            "allPayloadObligationsPassed",
        )
        or direct_concrete_payload_present
    )
    lean_payload_allowed = receiver_ready and proof_rows_present

    implementation_modes = [
        {
            "mode": "single_full_cell_interval",
            "target": TARGET_THEOREM,
            "status": (
                "blocked_missing_whole_expression_rows"
                if not ledger_bool(
                    payload_ledger, "directNonzeroModelIntervalRowsLeanChecked"
                )
                else "candidate_rows_present"
            ),
            "finalTheoremTarget": True,
        },
        {
            "mode": "segmented_direct_family",
            "target": "Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert.Valid",
            "status": (
                "receiver_ready_rows_missing" if receiver_ready else "receiver_missing"
            ),
            "finalTheoremTarget": True,
        },
        {
            "mode": "direct_horner_family",
            "target": "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert.Valid",
            "status": (
                "receiver_lean_checked_rows_missing"
                if direct_horner_receiver_present and direct_horner_receiver_lean_checked
                else "receiver_present_validation_pending_rows_missing"
                if direct_horner_receiver_present
                else "receiver_missing"
            ),
            "finalTheoremTarget": True,
            "useOnlyAsInternalTechnique": True,
            "leanValidation": "direct_lean_pass",
            "lakeEnvLeanValidation": "not_completed_entrypoint_timeout",
        },
        {
            "mode": "direct_collapsed_expression_source_bridge",
            "target": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_eq_collapsedExpression"
            ),
            "status": (
                "source_bridge_lean_checked"
                if direct_source_bridge_present
                else "source_bridge_missing"
            ),
            "finalTheoremTarget": False,
            "useOnlyAsBridgeBeforeRows": True,
            "leanValidation": "direct_lean_pass"
            if direct_source_bridge_lean_checked
            else "not_checked",
        },
        {
            "mode": "direct_collapsed_horner_source_bridge",
            "target": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert."
                "Valid.of_collapsed_horner_range"
            ),
            "familyTarget": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert."
                "valid_of_collapsed_horner_rows"
            ),
            "status": (
                "collapsed_horner_source_bridge_lean_checked"
                if direct_horner_source_bridge_present
                else "collapsed_horner_source_bridge_missing"
            ),
            "finalTheoremTarget": False,
            "useOnlyAsBridgeBeforeRows": True,
            "leanValidation": "direct_lean_pass"
            if direct_horner_source_bridge_lean_checked
            else "not_checked",
        },
        {
            "mode": "direct_collapsed_taylor_receiver",
            "target": COLLAPSED_TAYLOR_RECEIVER_THEOREM,
            "file": rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE),
            "status": (
                "collapsed_taylor_receiver_lean_checked_source_interval_cert_ready"
                if direct_collapsed_taylor_source_present
                else "collapsed_taylor_receiver_missing"
            ),
            "finalTheoremTarget": False,
            "useOnlyAsReceiverBeforeRows": True,
            "failureCode": direct_collapsed_taylor_row_failure,
        },
        {
            "mode": "direct_collapsed_source_interval_adapter",
            "target": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsedTaylorValid_of_source_interval"
            ),
            "file": rel(DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE),
            "status": (
                "collapsed_source_interval_adapter_lean_checked_rows_missing"
                if direct_collapsed_source_interval_present
                else "collapsed_source_interval_adapter_missing"
            ),
            "finalTheoremTarget": False,
            "useOnlyAsReceiverBeforeRows": True,
            "failureCode": direct_collapsed_taylor_row_failure,
        },
        {
            "mode": "nominal_polynomial_bridge",
            "target": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16CollapsedExpression_eq_activeActual_sub_"
                "nominalOrder16Poly"
            ),
            "status": (
                "nominal_polynomial_bridge_lean_checked"
                if nominal_polynomial_bridge_present
                else "nominal_polynomial_bridge_missing"
            ),
            "finalTheoremTarget": False,
            "useOnlyAsCoefficientCrosswalkBeforeRows": True,
            "leanValidation": "direct_lean_pass"
            if nominal_polynomial_bridge_lean_checked
            else "not_checked",
        },
        {
            "mode": "active_actual_remainder_bridge",
            "target": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsed_segment_remainder_of_activeActual"
            ),
            "coefficientTarget": (
                "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
                "CollapsedCoeffOf"
            ),
            "status": (
                "active_actual_remainder_bridge_lean_checked"
                if active_actual_remainder_bridge_present
                else "active_actual_remainder_bridge_missing"
            ),
            "finalTheoremTarget": False,
            "useOnlyAsBridgeBeforeRows": True,
            "leanValidation": "direct_lean_pass"
            if active_actual_remainder_bridge_lean_checked
            else "not_checked",
            "nextMissingTheorem": ACTIVE_ACTUAL_SEGMENT_REMAINDER_THEOREM,
            "failureCodeIfRowsMissing": ACTIVE_ACTUAL_SEGMENT_REMAINDER_SOURCE_GAP,
        },
        {
            "mode": "direct_horner_receiver_smoke",
            "target": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainderDirectHorner_receiver_smoke"
            ),
            "status": (
                "smoke_lean_checked"
                if direct_horner_smoke_present and direct_horner_smoke_lean_checked
                else "smoke_present_validation_not_completed"
                if direct_horner_smoke_present
                else "smoke_missing"
            ),
            "finalTheoremTarget": False,
            "useOnlyAsGateBeforeRows": True,
            "leanValidation": "direct_lean_pass",
            "lakeEnvLeanValidation": "not_completed_entrypoint_timeout",
            "failureCodeIfFails": DIRECT_HORNER_RECEIVER_VALIDATION_GAP,
        },
        {
            "mode": "local_model_segments",
            "target": (
                "Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert.Valid"
            ),
            "status": local_model_ledger.get(
                "currentGap",
                "ledger_missing_or_not_generated",
            ),
            "finalTheoremTarget": False,
            "useOnlyAsInternalTechnique": True,
        },
        {
            "mode": "source_horner_segments",
            "target": "Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert.Valid",
            "status": source_horner_ledger.get(
                "currentGap",
                "ledger_missing_or_not_generated",
            ),
            "finalTheoremTarget": False,
            "useOnlyAsInternalTechnique": True,
        },
    ]

    required_rows = [
        {
            "id": "C0_target_normalization",
            "status": "checked_surface_present" if receiver_ready else "missing",
            "proofObject": (
                "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual"
            ),
        },
        {
            "id": "C1_segment_cover",
            "status": "missing_if_segmented_mode",
            "proofObject": "cover of Set.Icc 0 (1/10)",
        },
        {
            "id": "C1b_collapsed_source_bridge",
            "status": (
                "checked_surface_present"
                if direct_source_bridge_present
                else "missing"
            ),
            "proofObject": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_eq_collapsedExpression"
            ),
            "proofGradeRowsPresent": False,
        },
        {
            "id": "C1c_collapsed_horner_receiver_bridge",
            "status": (
                "checked_surface_present"
                if direct_horner_source_bridge_present
                else "missing"
            ),
            "proofObject": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert."
                "Valid.of_collapsed_horner_range"
            ),
            "familyProofObject": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert."
                "valid_of_collapsed_horner_rows"
            ),
            "proofGradeRowsPresent": False,
            "meaning": (
                "Future row data may prove a collapsedExpression remainder "
                "and transport it into the directRemainder field."
            ),
        },
        {
            "id": "C1d_nominal_polynomial_bridge",
            "status": (
                "checked_surface_present"
                if nominal_polynomial_bridge_present
                else "missing"
            ),
            "proofObject": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16CollapsedExpression_eq_activeActual_sub_"
                "nominalOrder16Poly"
            ),
            "proofGradeRowsPresent": False,
            "meaning": (
                "The rational nominal order-16 polynomial is available as a "
                "partial coefficient crosswalk, but it is not a complete "
                "collapsedExpression coefficient stream and is not a budget."
            ),
        },
        {
            "id": "C1e_active_actual_remainder_adapter",
            "status": (
                "checked_surface_present"
                if active_actual_remainder_bridge_present
                else "missing"
            ),
            "proofObject": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsed_segment_remainder_of_activeActual"
            ),
            "proofGradeRowsPresent": False,
            "meaning": (
                "A future scaled-active-actual segment remainder row can be "
                "transported to the collapsed-expression remainder row by "
                "subtracting nominalOrder16Poly inside one coefficient stream."
            ),
            "nextMissingTheorem": ACTIVE_ACTUAL_SEGMENT_REMAINDER_THEOREM,
            "failureCodeIfRowsMissing": ACTIVE_ACTUAL_SEGMENT_REMAINDER_SOURCE_GAP,
        },
        {
            "id": "C2_collapsed_segment_remainder_rows",
            "status": (
                "missing_collapsed_segment_remainder_rows_component_taylor_gap_recorded_non_obligatory"
                if upstream_failure_code == COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
                else "missing"
            ),
            "proofObject": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "firstLeanDataObject": DIRECT_HORNER_DATA_OBJECT,
            "firstLeanValidityTheorem": DIRECT_HORNER_VALID_THEOREM,
            "failureCode": DIRECT_ROW_SOURCE_GAP,
            "upstreamFailureCode": upstream_failure_code,
        },
        {
            "id": "C3_horner_or_local_model_rows",
            "status": (
                "direct_horner_smoke_lean_checked_rows_missing"
                if direct_horner_smoke_present and direct_horner_smoke_lean_checked
                else "direct_horner_smoke_present_validation_not_completed_rows_missing"
                if direct_horner_smoke_present
                else "direct_horner_receiver_present_rows_missing_validation_pending"
                if direct_horner_receiver_present
                else "missing_optional_internal_technique"
            ),
            "proofObject": "per-segment rational model and Horner stage bounds",
            "preRowGate": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainderDirectHorner_receiver_smoke"
            ),
            "collapsedPreRowGate": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert."
                "Valid.of_collapsed_horner_range"
            ),
            "failureCode": DIRECT_HORNER_RECEIVER_VALIDATION_GAP,
        },
        {
            "id": "C4_analytic_remainder_rows",
            "status": (
                "missing_collapsed_segment_remainder_rows_component_taylor_gap_recorded_non_obligatory"
                if upstream_failure_code == COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
                else "missing"
            ),
            "proofObject": (
                "proof-grade collapsedExpression segment remainder bound, not "
                "sampled/probe rows"
            ),
            "upstreamFailureCode": upstream_failure_code,
        },
        {
            "id": "C5_budget_rows",
            "status": "missing",
            "proofObject": f"lower/upper rows against {TARGET_BUDGET}",
        },
        {
            "id": "C6_unconditional_lean_payload",
            "status": "blocked_until_C2_to_C5",
            "proofObject": rel(LEAN_OUT),
        },
    ]
    whole_expression_pilot_contract = build_whole_expression_pilot_contract()

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "direct_whole_expression_scaled_remainder_certificate",
        "proofStatus": (
            "lean_payload_generation_blocked_missing_collapsed_segment_rows"
            if not lean_payload_allowed
            else "ready_to_emit_lean_payload"
        ),
        "proofGrade": False,
        "leanPayloadWritten": False,
        "leanPayloadAllowed": lean_payload_allowed,
        "receiverReady": receiver_ready,
        "targetLeanFile": rel(LEAN_OUT),
        "targetTheorem": TARGET_THEOREM,
        "targetSourcePropTheorem": TARGET_SOURCE_PROP_THEOREM,
        "targetExpression": TARGET_EXPRESSION,
        "targetBudget": TARGET_BUDGET,
        "nominalPolynomialBridgeFile": rel(NOMINAL_POLYNOMIAL_BRIDGE_FILE),
        "activeActualRemainderBridgeFile": rel(ACTIVE_ACTUAL_REMAINDER_BRIDGE_FILE),
        "activeActualHornerSegmentFile": rel(ACTIVE_ACTUAL_HORNER_SEGMENT_FILE),
        "activeActualHornerFamilyBridgeFile": rel(
            ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE
        ),
        "directCollapsedTaylorSourceFile": rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE),
        "directCollapsedSourceIntervalFile": rel(
            DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE
        ),
        "directCollapsedLowDegreeSourceFile": rel(
            DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE
        ),
        "directCollapsedDegree0DerivativeShiftFile": rel(
            DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE
        ),
        "directCollapsedDegree0CenterAuditFile": rel(
            DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE
        ),
        "directCollapsedDegree0SignedSourceFile": rel(
            DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsFile": rel(
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE
        ),
        "activeActualHornerRowSourceLedgerFile": rel(
            ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER
        ),
        "activeActualDegree0AuditFile": rel(ACTIVE_ACTUAL_DEGREE0_AUDIT_FILE),
        "activeActualDegree0DirectBudgetKillTheorem": (
            ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_KILL_THEOREM
        ),
        "activeActualDegree0DirectBudgetFailureCode": (
            ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_FAIL
        ),
        "nominalPolynomialBridgeSymbols": nominal_polynomial_bridge_symbols,
        "activeActualRemainderBridgeSymbols": (
            active_actual_remainder_bridge_symbols
        ),
        "activeActualHornerSegmentSymbols": active_actual_horner_segment_symbols,
        "activeActualHornerFamilyBridgeSymbols": (
            active_actual_horner_family_bridge_symbols
        ),
        "directCollapsedTaylorSourceSymbols": (
            direct_collapsed_taylor_source_symbols
        ),
        "directCollapsedSourceIntervalSymbols": (
            direct_collapsed_source_interval_symbols
        ),
        "directCollapsedLowDegreeSourceSymbols": (
            direct_collapsed_low_degree_source_symbols
        ),
        "directCollapsedDegree0DerivativeShiftSymbols": (
            direct_collapsed_degree0_derivative_shift_symbols
        ),
        "directCollapsedDegree0CenterAuditSymbols": (
            direct_collapsed_degree0_center_audit_symbols
        ),
        "directCollapsedDegree0SignedSourceSymbols": (
            direct_collapsed_degree0_signed_source_symbols
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsSymbols": (
            direct_collapsed_degree0_raw_d17_signed_factor_rows_symbols
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillSymbols": (
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_symbols
        ),
        "nominalPolynomialBridgePresent": nominal_polynomial_bridge_present,
        "nominalPolynomialBridgeLeanChecked": nominal_polynomial_bridge_lean_checked,
        "directCollapsedTaylorSourcePresent": direct_collapsed_taylor_source_present,
        "directCollapsedTaylorSourceLeanChecked": (
            direct_collapsed_taylor_source_lean_checked
        ),
        "directCollapsedSourceIntervalPresent": (
            direct_collapsed_source_interval_present
        ),
        "directCollapsedSourceIntervalLeanChecked": (
            direct_collapsed_source_interval_lean_checked
        ),
        "directCollapsedLowDegreeSourcePresent": (
            direct_collapsed_low_degree_source_present
        ),
        "directCollapsedLowDegreeSourceLeanChecked": (
            direct_collapsed_low_degree_source_lean_checked
        ),
        "directCollapsedDegree0DerivativeShiftPresent": (
            direct_collapsed_degree0_derivative_shift_present
        ),
        "directCollapsedDegree0DerivativeShiftLeanChecked": (
            direct_collapsed_degree0_derivative_shift_lean_checked
        ),
        "directCollapsedDegree0CenterAuditPresent": (
            direct_collapsed_degree0_center_audit_present
        ),
        "directCollapsedDegree0CenterAuditLeanChecked": (
            direct_collapsed_degree0_center_audit_lean_checked
        ),
        "directCollapsedDegree0SignedSourcePresent": (
            direct_collapsed_degree0_signed_source_present
        ),
        "directCollapsedDegree0SignedSourceLeanChecked": (
            direct_collapsed_degree0_signed_source_lean_checked
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsPresent": (
            direct_collapsed_degree0_raw_d17_signed_factor_rows_present
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsLeanChecked": (
            direct_collapsed_degree0_raw_d17_signed_factor_rows_lean_checked
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillFile": rel(
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_FILE
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillPresent": (
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillLeanChecked": (
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_lean_checked
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetFailureCode": (
            COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_FAIL
        ),
        "activeActualRemainderBridgePresent": (
            active_actual_remainder_bridge_present
        ),
        "activeActualRemainderBridgeLeanChecked": (
            active_actual_remainder_bridge_lean_checked
        ),
        "activeActualHornerSegmentReceiverPresent": (
            active_actual_horner_segment_receiver_present
        ),
        "activeActualHornerSegmentReceiverLeanChecked": (
            active_actual_horner_segment_receiver_lean_checked
        ),
        "activeActualHornerFamilyBridgePresent": (
            active_actual_horner_family_bridge_present
        ),
        "activeActualHornerFamilyBridgeLeanChecked": (
            active_actual_horner_family_bridge_lean_checked
        ),
        "activeActualHornerRowSourceLedger": compact_ledger(
            ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER,
            [
                "schema",
                "proofStatus",
                "proofGrade",
                "proofSafeClosedFields",
                "currentGap",
                "firstFailureCode",
                "outLeanWritten",
                "leanValidationStatus",
                "allPayloadObligationsPassed",
            ],
        ),
        "currentGap": direct_collapsed_taylor_row_failure,
        "firstFailureCode": (
            direct_collapsed_taylor_row_failure
            if payload_horner_interface_matches
            else DIRECT_HORNER_LEDGER_INTERFACE_MISMATCH
        ),
        "parentDirectRowFailureCode": DIRECT_ROW_SOURCE_GAP,
        "legacyImmediateFailureCode": immediate_failure_code,
        "firstRowFailureCode": direct_collapsed_taylor_row_failure,
        "directCollapsedTaylorRowFailureCode": direct_collapsed_taylor_row_failure,
        "directCollapsedLowDegreeFailureCode": (
            direct_collapsed_degree0_raw_d17_first_concrete_gap
            if direct_collapsed_degree0_derivative_shift_present
            else COLLAPSED_DEGREE0_D17_SIGNED_SOURCE_GAP
        ),
        "directCollapsedDegree0RawD17FirstConcreteGap": (
            direct_collapsed_degree0_raw_d17_first_concrete_gap
        ),
        "directCollapsedLowDegreeBudgetFailureCode": (
            COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL
        ),
        "firstConcreteUpstreamFailureCode": upstream_failure_code,
        "payloadLedgerInterface": {
            "path": rel(PAYLOAD_LEDGER),
            "schema": payload_ledger.get("schema"),
            "expectedDataObject": payload_first_object,
            "expectedValidityTheorem": payload_valid_theorem,
            "certificateDataObject": DIRECT_HORNER_DATA_OBJECT,
            "certificateValidityTheorem": DIRECT_HORNER_VALID_THEOREM,
            "matchesCertificate": payload_horner_interface_matches,
            "failureCodeIfMismatch": DIRECT_HORNER_LEDGER_INTERFACE_MISMATCH,
        },
        "postBudgetKillFailureCode": FACTOR_BUDGET_KILL,
        "proshkaDecision": (
            "CHOSEN: A after the activeActual degree-0 budget failure: keep "
            "CollapsedExpression as one direct object and do not emit "
            "DirectConcretePayload.lean until the collapsed segment remainder "
            "theorem, Horner rows, segment cover, and final budget rows exist"
        ),
        "latestComputerUseRowReview": {
            "used": True,
            "url": COMPUTER_USE_REVIEW_URL,
            "recommendedOption": "A_direct_collapsed_expression_after_degree0_kill",
            "decision": (
                "The activeActual degree-0 row source is Lean-checked but "
                "budget-killed for the direct payload.  Keep the direct "
                "certificate fail-closed and build one proof-grade "
                "collapsedExpression segment remainder theorem for "
                "ComponentSource - NonzeroModelPoly."
            ),
            "routeForkFollowup": {
                "used": True,
                "recommendedOption": "A_direct_whole_expression_rows",
                "decision": (
                    "Use the direct whole-expression collapsedExpression row "
                    "source.  ActiveActual/nominal pieces may be internal "
                    "coefficient construction only, not separately spendable "
                    "budgets."
                ),
                "whyNoDirectConcretePayloadYet": (
                    "The proof-grade collapsed segment remainder theorem, "
                    "Horner rows, segment cover, and final +/- budget rows "
                    "are still missing."
                ),
                "whyNotB": (
                    "Separate activeActual and nominal bounds resurrect the "
                    "killed triangle-loss route."
                ),
                "whyNotD": (
                    "The direct route is still alive; the missing object is "
                    "exactly named by the collapsed segment theorem."
                ),
            },
            "firstFileToEdit": FIRST_PROOF_PRODUCING_GENERATOR,
            "firstFileToCreate": rel(LEAN_OUT),
            "secondFileCreated": "none_until_rows_pass",
            "firstLeanDataObject": DIRECT_HORNER_DATA_OBJECT,
            "familyBridgeDataObject": DIRECT_HORNER_DATA_OBJECT,
            "firstLeanValidityTheorem": DIRECT_HORNER_VALID_THEOREM,
            "familyBridgeValidityTheorem": DIRECT_HORNER_VALID_THEOREM,
            "familyBridgePayloadTheorem": TARGET_THEOREM,
            "activeActualMissingRemainderTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "activeActualHornerReceiverTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "activeActualCollapsedHornerTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "activeActualHornerFamilyTheorem": DIRECT_HORNER_VALID_THEOREM,
            "activeActualHornerFamilyPayloadTheorem": TARGET_THEOREM,
            "minimalRowDataRequired": [
                "exact segment cover for Set.Icc 0 (1/10)",
                "one proof-grade degree-0 rational coefficient for collapsedExpression",
                "proof-grade center enclosure for collapsedExpression at 1/20",
                "proof-grade signed activeD17-minus-deriv(NominalOrder16Poly) source row",
                "rational degree-0 budget comparison",
                f"proof-grade {COLLAPSED_SEGMENT_REMAINDER_THEOREM} rows",
                "Horner stage lower/upper bounds",
                "final +/- BiasedResidualRemainderAbs budget rows",
            ],
            "failureCodeIfRowsMissing": (
                COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP
            ),
            "failureCodeIfDegree0BudgetFails": (
                COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL
            ),
            "parentFailureCodeIfRowsMissing": DIRECT_ROW_SOURCE_GAP,
            "failureCodeIfSourceIntervalCertMissing": (
                COLLAPSED_SOURCE_INTERVAL_CERT_GAP
            ),
            "failureCodeIfCollapsedTaylorReceiverMissing": (
                COLLAPSED_TAYLOR_RECEIVER_GAP
            ),
            "failureCodeIfFamilyBridgeMissing": DIRECT_ROW_SOURCE_GAP,
            "failureCodeIfReceiverMissing": DIRECT_HORNER_RECEIVER_VALIDATION_GAP,
            "activeActualDegree0AuditFile": rel(ACTIVE_ACTUAL_DEGREE0_AUDIT_FILE),
            "activeActualDegree0BudgetKillTheorem": (
                ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_KILL_THEOREM
            ),
            "activeActualDegree0BudgetFailureCode": (
                ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_FAIL
            ),
            "degree0SignedSourceFile": rel(
                DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE
            ),
            "degree0SignedSourcePresent": (
                direct_collapsed_degree0_signed_source_present
            ),
            "degree0SignedSourceLeanChecked": (
                direct_collapsed_degree0_signed_source_lean_checked
            ),
            "degree0RawD17SignedFactorRowsFile": rel(
                DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE
            ),
            "degree0RawD17SignedFactorRowsPresent": (
                direct_collapsed_degree0_raw_d17_signed_factor_rows_present
            ),
            "degree0RawD17SignedFactorRowsLeanChecked": (
                direct_collapsed_degree0_raw_d17_signed_factor_rows_lean_checked
            ),
            "rawD17SignedFactorBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
            ),
            "rawD17RawPolySegmentBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment"
            ),
            "firstConcreteSubgap": (
                direct_collapsed_degree0_raw_d17_first_concrete_gap
            ),
            "whatMustNotBeReused": [
                "killed factor majorants",
                "activeActual degree-0 polyErrorAbs as the direct payload budget",
                "separate actual/nominal norm budgets",
                "zero-model budget",
                "sampled rows",
                "P45 machinery without a same-target theorem",
                "coarse P45/product budgets",
                "componentTaylorRemainder as an obligatory intermediate layer",
                "nominalOrder16Poly as an independent spendable budget",
            ],
            "advisoryOnly": True,
        },
        "directCollapsedTaylorReceiverReview": {
            "used": True,
            "url": COMPUTER_USE_REVIEW_URL,
            "recommendedOption": "C",
            "file": rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE),
            "present": direct_collapsed_taylor_source_present,
            "leanChecked": direct_collapsed_taylor_source_lean_checked,
            "sourceIntervalFile": rel(DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE),
            "sourceIntervalPresent": direct_collapsed_source_interval_present,
            "sourceIntervalLeanChecked": (
                direct_collapsed_source_interval_lean_checked
            ),
            "lowDegreeSourceFile": rel(DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE),
            "lowDegreeSourcePresent": direct_collapsed_low_degree_source_present,
            "lowDegreeSourceLeanChecked": (
                direct_collapsed_low_degree_source_lean_checked
            ),
            "degree0DerivativeShiftFile": rel(
                DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE
            ),
            "degree0DerivativeShiftPresent": (
                direct_collapsed_degree0_derivative_shift_present
            ),
            "degree0DerivativeShiftLeanChecked": (
                direct_collapsed_degree0_derivative_shift_lean_checked
            ),
            "degree0CenterAuditFile": rel(
                DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE
            ),
            "degree0CenterAuditPresent": (
                direct_collapsed_degree0_center_audit_present
            ),
            "degree0CenterAuditLeanChecked": (
                direct_collapsed_degree0_center_audit_lean_checked
            ),
            "degree0RawD17SignedFactorRowsFile": rel(
                DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE
            ),
            "degree0RawD17SignedFactorRowsPresent": (
                direct_collapsed_degree0_raw_d17_signed_factor_rows_present
            ),
            "degree0RawD17SignedFactorRowsLeanChecked": (
                direct_collapsed_degree0_raw_d17_signed_factor_rows_lean_checked
            ),
            "rawD17SignedFactorBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsedDegree0_rawD17_interval_of_signed_factor_segment"
            ),
            "rawD17RawPolySegmentBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment"
            ),
            "firstConcreteSubgap": (
                direct_collapsed_degree0_raw_d17_first_concrete_gap
            ),
            "receiverTheorem": COLLAPSED_TAYLOR_RECEIVER_THEOREM,
            "preferredLowDegreeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsed_degree0_remainder_of_signedD17_source"
            ),
            "preferredPolyDerivTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsed_degree0_remainder_of_polyDeriv_signedD17_source"
            ),
            "adapterTheorem": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert."
                "Valid.to_directHorner_valid"
            ),
            "sourceIntervalTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsedTaylorValid_of_source_interval"
            ),
            "sourceIntervalRemainderTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsed_segment_remainder_of_source_interval"
            ),
            "decision": (
                "Use the cheaper degree-0 receiver for the whole "
                "CollapsedExpression before spending the degree-15 Taylor "
                "route.  The checked derivative-shift bridge reduces the "
                "first missing proof object to signed-factor term rows for "
                "activeScale * D17(ComponentProductActual), then the same-"
                "segment subtraction against deriv(NominalOrder16Poly)."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RECEIVER_CLOSED"
                if direct_collapsed_low_degree_source_present
                else "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_SOURCE_INTERVAL_CERT_CLOSED"
                if direct_collapsed_source_interval_present
                else "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_TAYLOR_RECEIVER_CLOSED"
                if direct_collapsed_taylor_source_present
                else None
            ),
            "firstMissingRows": [
                "proof-grade center enclosure for CollapsedExpression at 1/20",
                "proof-grade signed-factor term rows for activeScale * D17(ComponentProductActual)",
                "proof-grade raw-D17 interval assembly from the signed-factor term rows",
                "exact same-segment signed subtraction rows against the checked nominal poly derivative row",
                "rational degree-0 budget comparison",
                "Horner stage bounds",
                "final +/- BiasedResidualRemainderAbs budget rows",
            ],
            "hiddenMismatchesToGuard": [
                "the signed source row must bound activeScale * D17(ComponentProductActual) - deriv(NominalOrder16Poly) before taking norms",
                "do not spend activeActual-alone, nominal-alone, or killed degree-0 activeActual budgets",
                "degree-15/source-interval rows remain valid but are no longer the first route-C gap",
            ],
            "failureCodeIfReceiverFails": COLLAPSED_TAYLOR_RECEIVER_GAP,
            "failureCodeIfSourceIntervalCertMissing": (
                COLLAPSED_SOURCE_INTERVAL_CERT_GAP
            ),
            "failureCodeIfRowsMissing": (
                direct_collapsed_degree0_raw_d17_first_concrete_gap
            ),
            "failureCodeIfDegree0BudgetFails": (
                COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL
            ),
            "proofClaimAllowedNow": False,
        },
        "directHornerRowStreamStatus": {
            "targetFile": rel(LEAN_OUT),
            "targetFileExists": LEAN_OUT.exists(),
            "requiredSymbols": direct_concrete_payload_symbols,
            "rowStreamPresent": direct_concrete_payload_present,
            "proofGrade": direct_concrete_payload_present,
            "failureCode": None
            if direct_concrete_payload_present
            else DIRECT_ROW_SOURCE_GAP,
        },
        "computerUseRouteReview": {
            "used": True,
            "url": COMPUTER_USE_REVIEW_URL,
            "recommendedOption": "A",
            "supersededForPartialNominalBridgeBy": "CHOSEN: A",
            "supersededForActiveActualAdapterBy": "CHOSEN: A",
            "supersededForDegree0BudgetKillBy": "CHOSEN: A",
            "decision": (
                "Build the direct collapsedExpression row source first.  Keep "
                "CollapsedExpression as one object and take norms only after "
                "the activeActual-minus-nominal subtraction; activeActual "
                "degree-0 is budget-killed for the direct payload."
            ),
            "firstArtifacts": [
                "scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.py",
                "ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.json",
                "ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.md",
            ],
            "theoremShape": [
                (
                    "theorem "
                    f"{COLLAPSED_SEGMENT_REMAINDER_THEOREM}"
                ),
                "  (i : Fin segmentCount) :",
                "  forall eta in Set.Icc (cellL i : Real) (cellU i : Real),",
                "    norm (CollapsedExpression eta -",
                "      rawOmegaATaylorPolynomial degree (center i) (coeff i) eta) <=",
                "    (polyErrorAbs i : Real)",
            ],
            "failureCodeIfFails": DIRECT_ROW_SOURCE_GAP,
            "mustCheckBeforeProgressClaim": [
                "generated target is definitionally or theorem-wise equal to the current target",
                "segment cover is exact if segmented mode is used",
                "every Horner/rational propagation row is Lean-checked",
                "analytic remainder row is proof-grade, not sampled",
                "final +/- BiasedResidualRemainderAbs budget passes exactly",
                "the interval_generated theorem compiles unconditionally",
            ],
            "internalTechniqueOnly": [
                "Horner split",
                "local-model segments",
                "source-Horner segments",
            ],
            "notProofEvidence": [
                "centered-Taylor factor majorants killed by exact budget",
                "P45/full-Taylor machinery for the wrong target",
                "zero-model/direct-source budget",
                "independent bounds on product summands",
                "center jets as uniform full-cell intervals",
                "sampled/probe interval rows",
            ],
        },
        "computerUseSmokeReview": {
            "used": True,
            "url": COMPUTER_USE_REVIEW_URL,
            "recommendedOption": "B",
            "decision": (
                "Before proof-row generation, validate the direct Horner receiver "
                "surface with an isolated smoke file."
            ),
            "firstFile": (
                "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
                "ScaledRemainderDirectHornerCertSmoke.lean"
            ),
            "firstTheoremObject": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainderDirectHorner_receiver_smoke"
            ),
            "failureCodeIfFails": DIRECT_HORNER_RECEIVER_VALIDATION_GAP,
            "mustCheckBeforeProgressClaim": [
                "direct Lean pass for the smoke file",
                ".olean generation",
                "exact target-expression match",
                "clean marker scan",
            ],
            "whatNotToReuse": [
                "killed factor-majorants",
                "P45/full-Taylor wrong target",
                "zero-model budget",
                "sampled rows",
                "separate product-summand norm bounds",
            ],
        },
        "payloadLedger": rel(PAYLOAD_LEDGER),
        "sourceHornerLedger": rel(BIASED_SOURCE_HORNER_LEDGER),
        "localModelLedger": rel(BIASED_LOCAL_MODEL_LEDGER),
        "componentTaylorResidualLedger": rel(COMPONENT_TAYLOR_RESIDUAL_LEDGER),
        "shapeSqDerivTightLedger": rel(SHAPESQ_DERIV_TIGHT_LEDGER),
        "upstreamRowSourceAudit": upstream_row_source_audit,
        "proofRowInputs": {
            "directNonzeroModelIntervalRowsLeanChecked": ledger_bool(
                payload_ledger, "directNonzeroModelIntervalRowsLeanChecked"
            ),
            "directNonzeroModelSourcePropLeanChecked": ledger_bool(
                payload_ledger, "directNonzeroModelSourcePropLeanChecked"
            ),
            "directHornerReceiverPresent": direct_horner_receiver_present,
            "directHornerReceiverLeanChecked": direct_horner_receiver_lean_checked,
            "directHornerSmokePresent": direct_horner_smoke_present,
            "directHornerSmokeLeanChecked": direct_horner_smoke_lean_checked,
            "directSourceBridgePresent": direct_source_bridge_present,
            "directSourceBridgeLeanChecked": direct_source_bridge_lean_checked,
            "directHornerSourceBridgePresent": (
                direct_horner_source_bridge_present
            ),
            "directHornerSourceBridgeLeanChecked": (
                direct_horner_source_bridge_lean_checked
            ),
            "directCollapsedTaylorSourcePresent": (
                direct_collapsed_taylor_source_present
            ),
            "directCollapsedTaylorSourceLeanChecked": (
                direct_collapsed_taylor_source_lean_checked
            ),
            "directConcretePayloadPresent": direct_concrete_payload_present,
            "directHornerLakeEnvLeanChecked": False,
            "sourceRemainderBoundLeanChecked": ledger_bool(
                source_horner_ledger, "sourceRemainderBoundLeanChecked"
            ),
            "localModelSourceRowsLeanChecked": ledger_bool(
                local_model_ledger, "sourceRowsLeanChecked"
            ),
            "localModelModelRowsLeanChecked": ledger_bool(
                local_model_ledger, "modelRowsLeanChecked"
            ),
        },
        "validation": {
            "directLeanPathMode": "passed",
            "directLeanCommands": [
                (
                    "LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 "
                    "-o .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.olean "
                    "-i .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.ilean "
                    "Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean"
                ),
                (
                    "LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 "
                    "-o .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.olean "
                    "-i .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.ilean "
                    "Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean"
                ),
                (
                    "LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 "
                    "-o .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.olean "
                    "-i .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.ilean "
                    "Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean"
                ),
                (
                    "LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 "
                    "-o .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.olean "
                    "-i .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.ilean "
                    "Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean"
                ),
                (
                    "LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 "
                    "-o .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.olean "
                    "-i .lake/build/lib/lean/Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.ilean "
                    "Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean"
                ),
                (
                    "LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 "
                    "Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedTaylorSource.lean"
                ),
            ],
            "lakeEnvLean": {
                "status": "not_completed_entrypoint_timeout",
                "command": (
                    "lake env lean Q3/Proofs/"
                    "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean"
                ),
                "note": (
                    "The direct Lean check generated .olean/.ilean files; "
                    "lake env lean remained nonresponsive in a bounded run."
                ),
            },
        },
        "cheapWholeExpressionPilot": whole_expression_pilot_contract,
        "implementationModes": implementation_modes,
        "requiredRows": required_rows,
        "symbolAudit": {
            rel(DIRECT_PAYLOAD_FILE): direct_payload_symbols,
            rel(ZERO_MODEL_FILE): zero_model_symbols,
            rel(NONZERO_MODEL_FILE): nonzero_model_symbols,
            rel(BIASED_LOCAL_MODEL_FILE): local_model_symbols,
            rel(BIASED_SOURCE_HORNER_FILE): source_horner_symbols,
            rel(BIASED_SOURCE_HORNER_PAYLOAD_FILE): biased_adapter_symbols,
            rel(DIRECT_HORNER_FILE): direct_horner_symbols,
            rel(DIRECT_HORNER_SMOKE_FILE): direct_horner_smoke_symbols,
            rel(DIRECT_SOURCE_BRIDGE_FILE): direct_source_bridge_symbols,
            rel(DIRECT_HORNER_SOURCE_BRIDGE_FILE): (
                direct_horner_source_bridge_symbols
            ),
            rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE): (
                direct_collapsed_taylor_source_symbols
            ),
            rel(DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_FILE): (
                direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_symbols
            ),
            rel(ACTIVE_ACTUAL_HORNER_SEGMENT_FILE): (
                active_actual_horner_segment_symbols
            ),
            rel(LEAN_OUT): direct_concrete_payload_symbols,
            rel(FACTOR_BUDGET_FILE): factor_budget_symbols,
        },
        "doNotReuse": [
            "centered-Taylor factor majorants killed by exact budget",
            "P45/full-Taylor machinery: wrong target",
            "zero-model/direct-source budget",
            "independent product-summand norm bounds",
            "center jets as uniform full-cell intervals",
            "sampled/probe interval rows",
        ],
        "guard": (
            "This generator must not write the Lean payload until the whole "
            "signed expression interval rows are proof-grade.  The current "
            "run is a fail-closed preflight, not Step33A.1-A closure."
        ),
    }


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Direct Scaled-Remainder Certificate Preflight",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Verdict",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- receiverReady: `{ledger['receiverReady']}`",
        f"- leanPayloadAllowed: `{ledger['leanPayloadAllowed']}`",
        f"- leanPayloadWritten: `{ledger['leanPayloadWritten']}`",
        f"- currentGap: `{ledger['currentGap']}`",
        f"- firstFailureCode: `{ledger['firstFailureCode']}`",
        f"- firstRowFailureCode: `{ledger['firstRowFailureCode']}`",
        "- directCollapsedTaylorSourcePresent: "
        f"`{ledger['directCollapsedTaylorSourcePresent']}`",
        "- directCollapsedTaylorSourceLeanChecked: "
        f"`{ledger['directCollapsedTaylorSourceLeanChecked']}`",
        "- directCollapsedDegree0DerivativeShiftLeanChecked: "
        f"`{ledger['directCollapsedDegree0DerivativeShiftLeanChecked']}`",
        "- directCollapsedDegree0CenterAuditLeanChecked: "
        f"`{ledger['directCollapsedDegree0CenterAuditLeanChecked']}`",
        "- directCollapsedDegree0SignedSourceLeanChecked: "
        f"`{ledger['directCollapsedDegree0SignedSourceLeanChecked']}`",
        "- directCollapsedDegree0RawD17SignedFactorRowsLeanChecked: "
        f"`{ledger['directCollapsedDegree0RawD17SignedFactorRowsLeanChecked']}`",
        "- directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillPresent: "
        f"`{ledger['directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillPresent']}`",
        "- directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillLeanChecked: "
        f"`{ledger['directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillLeanChecked']}`",
        "- nominalPolynomialBridgePresent: "
        f"`{ledger['nominalPolynomialBridgePresent']}`",
        "- nominalPolynomialBridgeLeanChecked: "
        f"`{ledger['nominalPolynomialBridgeLeanChecked']}`",
        "- activeActualRemainderBridgePresent: "
        f"`{ledger['activeActualRemainderBridgePresent']}`",
        "- activeActualRemainderBridgeLeanChecked: "
        f"`{ledger['activeActualRemainderBridgeLeanChecked']}`",
        "- activeActualHornerSegmentReceiverPresent: "
        f"`{ledger['activeActualHornerSegmentReceiverPresent']}`",
        "- activeActualHornerSegmentReceiverLeanChecked: "
        f"`{ledger['activeActualHornerSegmentReceiverLeanChecked']}`",
        "- activeActualHornerFamilyBridgePresent: "
        f"`{ledger['activeActualHornerFamilyBridgePresent']}`",
        "- activeActualHornerFamilyBridgeLeanChecked: "
        f"`{ledger['activeActualHornerFamilyBridgeLeanChecked']}`",
        "- firstConcreteUpstreamFailureCode: "
        f"`{ledger['firstConcreteUpstreamFailureCode']}`",
        f"- Computer Use route review: `{ledger['computerUseRouteReview']['recommendedOption']}`",
        "",
        "## Active-Actual Horner Row-Source Ledger",
        "",
        f"- file: `{ledger['activeActualHornerRowSourceLedgerFile']}`",
        f"- exists: `{ledger['activeActualHornerRowSourceLedger']['exists']}`",
        f"- schema: `{ledger['activeActualHornerRowSourceLedger']['schema']}`",
        "- proofStatus: "
        f"`{ledger['activeActualHornerRowSourceLedger']['proofStatus']}`",
        f"- proofGrade: `{ledger['activeActualHornerRowSourceLedger']['proofGrade']}`",
        "- proofSafeClosedFields: "
        f"`{ledger['activeActualHornerRowSourceLedger']['proofSafeClosedFields']}`",
        "- allPayloadObligationsPassed: "
        f"`{ledger['activeActualHornerRowSourceLedger']['allPayloadObligationsPassed']}`",
        "- firstFailureCode: "
        f"`{ledger['activeActualHornerRowSourceLedger']['firstFailureCode']}`",
        "",
        "This ledger is a generator contract only.  It is not a proof row and "
        "does not permit Lean payload emission while `allPayloadObligationsPassed` "
        "is false.",
        "",
        "## Target",
        "",
        f"- Lean file: `{ledger['targetLeanFile']}`",
        f"- theorem: `{ledger['targetTheorem']}`",
        f"- source-prop theorem: `{ledger['targetSourcePropTheorem']}`",
        f"- expression: `{ledger['targetExpression']}`",
        f"- budget: `{ledger['targetBudget']}`",
        "",
        "## Proof Row Inputs",
        "",
    ]
    for key, value in ledger["proofRowInputs"].items():
        lines.append(f"- `{key}`: `{value}`")

    pilot = ledger["cheapWholeExpressionPilot"]
    lines.extend(
        [
            "",
            "## Cheap Whole-Expression Pilot Contract",
            "",
            f"- phase: `{pilot['phase']}`",
            f"- status: `{pilot['status']}`",
            f"- proofGrade: `{pilot['proofGrade']}`",
            f"- pilotScript: `{pilot['pilotScript']}`",
            f"- pilotScriptExists: `{pilot['pilotScriptExists']}`",
            f"- pilotOutputJson: `{pilot['pilotOutputJson']}`",
            f"- pilotOutputMarkdown: `{pilot['pilotOutputMarkdown']}`",
            f"- pilotOutputLoaded: `{pilot['pilotOutputLoaded']}`",
            f"- pilotVerdict: `{pilot['pilotVerdict']}`",
            f"- sourceDataReady: `{pilot['sourceDataReady']}`",
            f"- sourceDataStatus: `{pilot['sourceDataStatus']}`",
            f"- commandWhenImplemented: `{pilot['commandWhenImplemented']}`",
            f"- mustEvaluateExpression: `{pilot['mustEvaluateExpression']}`",
            f"- mustFeedReceiverTheorem: `{pilot['mustFeedReceiverTheorem']}`",
            f"- receiverField: `{pilot['receiverField']}`",
            f"- targetInterval: `{pilot['targetInterval']}`",
            f"- preserveCancellation: `{pilot['preserveCancellation']}`",
            f"- phase2ResultNow: `{pilot['phase2ResultNow']}`",
            f"- firstFailureCode: `{pilot['firstFailureCode']}`",
            f"- decisionRule: {pilot['decisionRule']}",
            "",
            "Accepted pilot verdicts:",
            "",
        ]
    )
    for verdict in pilot["acceptedPilotVerdicts"]:
        lines.append(f"- `{verdict}`")
    lines.extend(["", "Blocking missing artifacts:", ""])
    for item in pilot["blockingMissingArtifacts"]:
        lines.append(
            f"- `{item.get('id')}`: {item.get('required')}"
        )
    lines.extend(["", "Required rows before payload:", ""])
    for item in pilot["requiredRows"]:
        lines.append(f"- {item}")
    lines.extend(["", "Do not use:", ""])
    for item in pilot["doNotUse"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "Next implementable patch:",
            "",
            pilot["nextImplementablePatch"],
        ]
    )

    interface = ledger["payloadLedgerInterface"]
    lines.extend(
        [
            "",
            "## Payload Ledger Interface",
            "",
            f"- path: `{interface['path']}`",
            f"- schema: `{interface['schema']}`",
            f"- expectedDataObject: `{interface['expectedDataObject']}`",
            f"- expectedValidityTheorem: `{interface['expectedValidityTheorem']}`",
            f"- certificateDataObject: `{interface['certificateDataObject']}`",
            f"- certificateValidityTheorem: `{interface['certificateValidityTheorem']}`",
            f"- matchesCertificate: `{interface['matchesCertificate']}`",
            f"- failureCodeIfMismatch: `{interface['failureCodeIfMismatch']}`",
        ]
    )

    latest_review = ledger["latestComputerUseRowReview"]
    route_fork = latest_review["routeForkFollowup"]
    row_stream = ledger["directHornerRowStreamStatus"]
    lines.extend(
        [
            "",
            "## Latest Computer Use Row Review",
            "",
            f"- used: `{latest_review['used']}`",
            f"- url: `{latest_review['url']}`",
            f"- recommendedOption: `{latest_review['recommendedOption']}`",
            f"- advisoryOnly: `{latest_review['advisoryOnly']}`",
            f"- decision: {latest_review['decision']}",
            f"- firstFileToEdit: `{latest_review['firstFileToEdit']}`",
            f"- firstFileToCreate: `{latest_review['firstFileToCreate']}`",
            f"- secondFileCreated: `{latest_review['secondFileCreated']}`",
            f"- firstLeanDataObject: `{latest_review['firstLeanDataObject']}`",
            f"- familyBridgeDataObject: `{latest_review['familyBridgeDataObject']}`",
            f"- firstLeanValidityTheorem: `{latest_review['firstLeanValidityTheorem']}`",
            f"- familyBridgeValidityTheorem: `{latest_review['familyBridgeValidityTheorem']}`",
            f"- familyBridgePayloadTheorem: `{latest_review['familyBridgePayloadTheorem']}`",
            "- activeActualMissingRemainderTheorem: "
            f"`{latest_review['activeActualMissingRemainderTheorem']}`",
            "- activeActualDegree0BudgetKillTheorem: "
            f"`{latest_review['activeActualDegree0BudgetKillTheorem']}`",
            "- activeActualDegree0BudgetFailureCode: "
            f"`{latest_review['activeActualDegree0BudgetFailureCode']}`",
            f"- failureCodeIfRowsMissing: `{latest_review['failureCodeIfRowsMissing']}`",
            "- parentFailureCodeIfRowsMissing: "
            f"`{latest_review['parentFailureCodeIfRowsMissing']}`",
            "- failureCodeIfCollapsedTaylorReceiverMissing: "
            f"`{latest_review['failureCodeIfCollapsedTaylorReceiverMissing']}`",
            "- failureCodeIfFamilyBridgeMissing: "
            f"`{latest_review['failureCodeIfFamilyBridgeMissing']}`",
            "",
            "### Minimal Row Data Required",
            "",
        ]
    )
    for item in latest_review["minimalRowDataRequired"]:
        lines.append(f"- {item}")
    collapsed_taylor_review = ledger["directCollapsedTaylorReceiverReview"]
    lines.extend(
        [
            "",
            "## Direct Collapsed Taylor Receiver Review",
            "",
            f"- used: `{collapsed_taylor_review['used']}`",
            f"- url: `{collapsed_taylor_review['url']}`",
            f"- recommendedOption: `{collapsed_taylor_review['recommendedOption']}`",
            f"- file: `{collapsed_taylor_review['file']}`",
            f"- present: `{collapsed_taylor_review['present']}`",
            f"- leanChecked: `{collapsed_taylor_review['leanChecked']}`",
            "- low-degree source file: "
            f"`{collapsed_taylor_review['lowDegreeSourceFile']}`",
            "- low-degree source present: "
            f"`{collapsed_taylor_review['lowDegreeSourcePresent']}`",
            "- low-degree source Lean-checked: "
            f"`{collapsed_taylor_review['lowDegreeSourceLeanChecked']}`",
            "- degree-0 derivative-shift file: "
            f"`{collapsed_taylor_review['degree0DerivativeShiftFile']}`",
            "- degree-0 derivative-shift present: "
            f"`{collapsed_taylor_review['degree0DerivativeShiftPresent']}`",
            "- degree-0 derivative-shift Lean-checked: "
            f"`{collapsed_taylor_review['degree0DerivativeShiftLeanChecked']}`",
            "- receiver theorem: "
            f"`{collapsed_taylor_review['receiverTheorem']}`",
            "- preferred low-degree theorem: "
            f"`{collapsed_taylor_review['preferredLowDegreeTheorem']}`",
            "- preferred poly-deriv theorem: "
            f"`{collapsed_taylor_review['preferredPolyDerivTheorem']}`",
            f"- adapter theorem: `{collapsed_taylor_review['adapterTheorem']}`",
            f"- decision: {collapsed_taylor_review['decision']}",
            f"- closed subgap: `{collapsed_taylor_review['closedSubgap']}`",
            "- failure code if receiver fails: "
            f"`{collapsed_taylor_review['failureCodeIfReceiverFails']}`",
            "- failure code if rows missing: "
            f"`{collapsed_taylor_review['failureCodeIfRowsMissing']}`",
            "- failure code if degree-0 budget fails: "
            f"`{collapsed_taylor_review['failureCodeIfDegree0BudgetFails']}`",
            "- proof claim allowed now: "
            f"`{collapsed_taylor_review['proofClaimAllowedNow']}`",
            "",
            "First missing rows:",
            "",
        ]
    )
    for item in collapsed_taylor_review["firstMissingRows"]:
        lines.append(f"- {item}")
    lines.extend(["", "Hidden mismatches to guard:", ""])
    for item in collapsed_taylor_review["hiddenMismatchesToGuard"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "### Sharp Two-Segment Factorwise Kill",
            "",
            "- file: "
            f"`{ledger['directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillFile']}`",
            "- present: "
            f"`{ledger['directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillPresent']}`",
            "- Lean checked: "
            f"`{ledger['directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillLeanChecked']}`",
            "- closed failure code: "
            f"`{ledger['directCollapsedDegree0RawD17SharpTwoSegmentBudgetFailureCode']}`",
            "- effect: this factorwise two-segment class is not a spendable "
            "direct row source; keep `CollapsedExpression` whole and build "
            "proof-grade direct rows.",
        ]
    )
    lines.extend(
        [
            "",
            "### Route Fork Follow-up",
            "",
            f"- used: `{route_fork['used']}`",
            f"- recommendedOption: `{route_fork['recommendedOption']}`",
            f"- decision: {route_fork['decision']}",
        ]
    )
    for key in ["whyNotA", "whyNotB", "whyNotC", "whyNotD"]:
        if key in route_fork:
            lines.append(f"- {key}: {route_fork[key]}")
    lines.extend(["", "### What Must Not Be Reused", ""])
    for item in latest_review["whatMustNotBeReused"]:
        lines.append(f"- {item}")

    lines.extend(
        [
            "",
            "## Direct Horner Row Stream Status",
            "",
            f"- targetFile: `{row_stream['targetFile']}`",
            f"- targetFileExists: `{row_stream['targetFileExists']}`",
            f"- rowStreamPresent: `{row_stream['rowStreamPresent']}`",
            f"- proofGrade: `{row_stream['proofGrade']}`",
            f"- failureCode: `{row_stream['failureCode']}`",
            "",
            "### Required Symbols",
            "",
        ]
    )
    for symbol, info in row_stream["requiredSymbols"].items():
        lines.append(
            f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
        )

    validation = ledger["validation"]
    lines.extend(
        [
            "",
            "## Validation",
            "",
            f"- directLeanPathMode: `{validation['directLeanPathMode']}`",
            f"- lakeEnvLean.status: `{validation['lakeEnvLean']['status']}`",
            f"- lakeEnvLean.command: `{validation['lakeEnvLean']['command']}`",
            f"- lakeEnvLean.note: {validation['lakeEnvLean']['note']}",
            "",
            "### Direct Lean Commands",
            "",
        ]
    )
    for command in validation["directLeanCommands"]:
        lines.append(f"- `{command}`")

    review = ledger["computerUseRouteReview"]
    lines.extend(
        [
            "",
            "## Computer Use Route Review",
            "",
            f"- used: `{review['used']}`",
            f"- url: `{review['url']}`",
            f"- recommendedOption: `{review['recommendedOption']}`",
            f"- decision: {review['decision']}",
            f"- failureCodeIfFails: `{review['failureCodeIfFails']}`",
            "",
            "### First Artifacts",
            "",
        ]
    )
    for artifact in review["firstArtifacts"]:
        lines.append(f"- `{artifact}`")
    lines.extend(["", "### Theorem Shape", "", "```text"])
    lines.extend(review["theoremShape"])
    lines.extend(["```", "", "### Must Check Before Progress Claim", ""])
    for item in review["mustCheckBeforeProgressClaim"]:
        lines.append(f"- {item}")
    lines.extend(["", "### Internal Technique Only", ""])
    for item in review["internalTechniqueOnly"]:
        lines.append(f"- {item}")
    lines.extend(["", "### Not Proof Evidence", ""])
    for item in review["notProofEvidence"]:
        lines.append(f"- {item}")

    smoke_review = ledger["computerUseSmokeReview"]
    lines.extend(
        [
            "",
            "## Computer Use Smoke Review",
            "",
            f"- used: `{smoke_review['used']}`",
            f"- url: `{smoke_review['url']}`",
            f"- recommendedOption: `{smoke_review['recommendedOption']}`",
            f"- decision: {smoke_review['decision']}",
            f"- firstFile: `{smoke_review['firstFile']}`",
            f"- firstTheoremObject: `{smoke_review['firstTheoremObject']}`",
            f"- failureCodeIfFails: `{smoke_review['failureCodeIfFails']}`",
            "",
            "### Must Check Before Progress Claim",
            "",
        ]
    )
    for item in smoke_review["mustCheckBeforeProgressClaim"]:
        lines.append(f"- {item}")
    lines.extend(["", "### What Not To Reuse", ""])
    for item in smoke_review["whatNotToReuse"]:
        lines.append(f"- {item}")

    audit = ledger["upstreamRowSourceAudit"]
    lines.extend(
        [
            "",
            "## Upstream Row-Source Audit",
            "",
            f"- directFailureCode: `{audit['directFailureCode']}`",
            "- firstConcreteUpstreamFailureCode: "
            f"`{audit['firstConcreteUpstreamFailureCode']}`",
            "- componentTaylorRemainderGapActive: "
            f"`{audit['componentTaylorRemainderGapActive']}`",
            "- proofGradeForDirectCertificate: "
            f"`{audit['proofGradeForDirectCertificate']}`",
            f"- verdict: {audit['verdict']}",
            f"- nextImplementablePatch: {audit['nextImplementablePatch']}",
            "",
            "### Component Taylor Residual Ledger",
            "",
        ]
    )
    for key, value in audit["componentTaylorResidualLedger"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "### ShapeSqDeriv Tight Ledger", ""])
    for key, value in audit["shapeSqDerivTightLedger"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "### Do Not Use As Closure", ""])
    for item in audit["doNotUseAsClosure"]:
        lines.append(f"- {item}")

    lines.extend(["", "## Implementation Modes", ""])
    for mode in ledger["implementationModes"]:
        lines.append(f"### {mode['mode']}")
        lines.append("")
        for key, value in mode.items():
            if key == "mode":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")

    lines.extend(["## Required Rows", ""])
    for row in ledger["requiredRows"]:
        lines.append(f"### {row['id']}")
        lines.append("")
        for key, value in row.items():
            if key == "id":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")

    lines.extend(["## Symbol Audit", ""])
    for path, symbols in ledger["symbolAudit"].items():
        lines.append(f"### {path}")
        lines.append("")
        for symbol, info in symbols.items():
            lines.append(
                f"- `{symbol}`: present=`{info['present']}`, line=`{info['line']}`"
            )
        lines.append("")

    lines.extend(["## Do Not Reuse", ""])
    for item in ledger["doNotReuse"]:
        lines.append(f"- {item}")

    lines.extend(["", "## Guard", "", str(ledger["guard"]), ""])
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")

    if ledger["leanPayloadAllowed"]:
        raise SystemExit(
            "proof rows are marked present, but Lean emission is intentionally "
            "not implemented in this preflight-only revision"
        )

    print(f"wrote {rel(JSON_OUT)}")
    print(f"wrote {rel(MD_OUT)}")
    print(ledger["proofStatus"])
    print(ledger["firstFailureCode"])


if __name__ == "__main__":
    main()
