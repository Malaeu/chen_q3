#!/usr/bin/env python3
"""Fail-closed ledger for the direct nonzero-model scaled-remainder payload.

The target is the same-unit signed residual

    CombinedCancellationOrder16ComponentSource - CombinedOrder16NonzeroModelPoly

on `[0, 1/10]`, at the canonical `BiasedResidualRemainderAbs` budget.  This
script does not emit proof rows and does not claim Step33A.1-A closure.  It
records the exact generator-facing payload surface and the first missing
proof-grade certificate.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA = (
    "q3_psdpd_step33_a1_sub0_combined_order16_"
    "scaled_remainder_direct_payload.v21"
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
INTERVAL_PAYLOAD_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderIntervalPayload.lean"
)
REMAINDER_BRIDGE_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerRemainderBridge.lean"
)
P45_FULL_TAYLOR_BRIDGE_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean"
)
ORDER16_NONZERO_MODEL_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean"
)
DIRECT_INTERVAL_PAYLOAD_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectIntervalPayload.lean"
)
DIRECT_MODEL_PAYLOAD_FILE = (
    PROOFS / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectModelPayload.lean"
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
BIASED_SOURCE_HORNER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerCert.lean"
)
BIASED_RESIDUAL_INTERVAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval.lean"
)
BIASED_SIGNED_FACTOR_ADAPTER_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSignedFactorAdapter.lean"
)
VIA_BIASED_RESIDUAL_FILE = (
    PROOFS
    / "PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderViaBiasedResidualPayload.lean"
)

JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json"
)
MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.md"
)
ROW_OBLIGATIONS_JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_row_obligations.json"
)
ROW_SOURCE_AUDIT_JSON_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.json"
)
ROW_SOURCE_AUDIT_MD_OUT = (
    REQUEST_DIR
    / "step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.md"
)
CANCELLATION_DIRECT_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_combined_cancellation_order16_direct_payload.json"
)
SOURCE_INTERVAL_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_combined_order16_source_interval.json"
)
SIGNED_FACTOR_ROWS_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_combined_order16_signed_factor_rows.json"
)
COMPONENT_TAYLOR_RESIDUAL_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
SHAPESQ_DERIV_TIGHT_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_shapesq_deriv_tight_payload.json"
)
ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER_FILE = (
    REQUEST_DIR / "step33_a1_sub0_active_actual_horner_row_source.json"
)

DIRECT_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval",
]

ZERO_MODEL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderSourceProp_of_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_zeroModel",
]

INTERVAL_PAYLOAD_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert",
    "Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert",
    "primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget",
]

REMAINDER_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound",
]

P45_FULL_TAYLOR_BRIDGE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_eq_scaledCancellationRhs",
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_bound_of_scaledCancellationRhs_bound",
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_bound",
]

DIRECT_SPLIT_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16Source_sub_nonzeroModelPoly"
)
DIRECT_HORNER_REMAINDER_FIELD = (
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert."
    "Valid.directRemainder"
)
DIRECT_SPLIT_RHS = (
    "primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * "
    "iteratedDeriv 16 "
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual "
    "eta + (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff - "
    "(primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) * "
    "iteratedDeriv 16 "
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta"
)
DIRECT_COLLAPSED_RHS = (
    "primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * "
    "iteratedDeriv 16 "
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta - "
    "(primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) * "
    "iteratedDeriv 16 "
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta"
)
WHOLE_EXPRESSION_ROW_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainder_wholeExpression_row"
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
DIRECT_HORNER_DATA_OBJECT = (
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
    "ScaledRemainderDirectHornerData"
)
DIRECT_HORNER_VALID_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "combinedOrder16ScaledRemainderDirectHorner_valid"
)

ORDER16_NONZERO_MODEL_SYMBOLS = [
    DIRECT_SPLIT_THEOREM,
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelSource",
    "primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff",
    "primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff",
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual",
    "primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal",
]

DIRECT_INTERVAL_PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget",
    "Step33Sub0CombinedCancellationOrder16DirectIntervalCert",
    "primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_direct_interval_to_source_field",
]

DIRECT_MODEL_PAYLOAD_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder",
    "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp",
]

DIRECT_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert",
    "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert",
    "structure Valid",
    "to_nonzeroModelSourceProp",
]

DIRECT_HORNER_SMOKE_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke",
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
    "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Coeff_eq_nonzeroModelCoeff",
    "primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_eq_nonzeroModelPoly",
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
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "activeActual_order16_segment_remainder_of_horner_cert"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "collapsed_segment_remainder_of_activeActualHorner"
    ),
]

ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_SYMBOLS = [
    "Step33Sub0ActiveActualOrder16HornerDirectSegmentCert",
    "Step33Sub0ActiveActualOrder16HornerDirectRangeCert",
    "Step33Sub0ActiveActualOrder16HornerFamilyCert",
    "theorem to_directHornerFamilyValid",
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "directHornerFamily_valid_of_activeActualHornerFamily"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "directPayloadTarget_of_activeActualHornerFamily"
    ),
    (
        "primaryFiniteRow0Parent0Split100Sub0_"
        "nonzeroModelSourceProp_of_activeActualHornerFamily"
    ),
]

BIASED_SOURCE_HORNER_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert",
    "Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_horner_family",
]

BIASED_RESIDUAL_SOURCE_SEGMENT_SYMBOLS = [
    "Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert",
    "namespace Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert",
    "theorem to_residual_bound_on_segment",
    "Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover",
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_source_segment_cover",
]

BIASED_SIGNED_FACTOR_ADAPTER_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover",
    "Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert",
]

VIA_BIASED_RESIDUAL_SYMBOLS = [
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_sub_bias_eq_biasedResidual",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegment_valid_of_biasedResidual",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidualSourceProp",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamilyOfBiasedResidual",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamily_valid_of_biasedResidual",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirect_payloadTarget_of_biasedResidual",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidual",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_bias_exceeds_direct_budget_rat",
    "primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_biasShift_upperBudget_impossible_of_nonneg",
]

CURRENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "NONZERO_MODEL_INTERVAL_CERT_GAP"
)
PARENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_"
    "SCALED_REMAINDER_BOUND_GAP"
)
P45_REUSE_FAILURE = (
    "STEP33_A1_SUB0_P45_FULL_TAYLOR_ORDER16_SOURCE_MISMATCH"
)
DIRECT_ROW_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
    "DIRECT_ROW_SOURCE_GAP"
)
BIAS_SHIFT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_"
    "TO_DIRECT_TARGET_BIAS_SHIFT_GAP"
)
BIAS_SHIFT_BUDGET_FAIL = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_"
    "TO_DIRECT_TARGET_BIAS_BUDGET_FAIL"
)
SOURCE_SEGMENT_PAYLOAD_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_"
    "SOURCE_SEGMENT_PAYLOAD_GAP"
)
FIRST_GENERATED_INTERVAL_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_interval_generated"
)
FIRST_GENERATED_SOURCE_PROP_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
    "nonzeroModel_sourceProp_generated"
)
FIRST_PROOF_PRODUCING_GENERATOR = (
    "scripts/generate_step33_a1_sub0_combined_order16_"
    "scaled_remainder_direct_payload.py"
)
ACTIVE_ACTUAL_HORNER_ROW_SOURCE_GENERATOR = (
    "scripts/generate_step33_a1_sub0_active_actual_horner_row_source.py"
)
FIRST_PROOF_PRODUCING_LEAN_FILE = (
    "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
    "ScaledRemainderDirectConcretePayload.lean"
)
POST_BUDGET_KILL_FAILURE = (
    "STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_"
    "ORDER16_BUDGET_CONSTANT_FAIL"
)
COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP = (
    "STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP"
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
ACTIVE_ACTUAL_NOMINAL_POLY_ALIGNMENT_GAP = (
    "STEP33_A1_SUB0_COMBINED_ORDER16_ACTIVE_ACTUAL_"
    "NOMINAL_POLY_ALIGNMENT_GAP"
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


def rel(path: Path) -> str:
    return str(path.relative_to(ROOT))


def file_contains(path: Path, symbols: list[str]) -> dict[str, bool]:
    if not path.exists():
        return {symbol: False for symbol in symbols}
    text = path.read_text(encoding="utf-8")
    return {symbol: symbol in text for symbol in symbols}


def all_true(items: dict[str, bool]) -> bool:
    return all(items.values())


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


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
    first_concrete_failure = (
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
            "Refine the direct scaled-remainder row worklist to the closest "
            "existing local source ledger."
        ),
        "directFailureCode": DIRECT_ROW_SOURCE_GAP,
        "firstConcreteUpstreamFailureCode": first_concrete_failure,
        "componentTaylorRemainderGapActive": component_gap_is_active,
        "componentTaylorResidualLedger": {
            "path": rel(COMPONENT_TAYLOR_RESIDUAL_LEDGER_FILE),
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
            "path": rel(SHAPESQ_DERIV_TIGHT_LEDGER_FILE),
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
            "ShapeSqDeriv tight same-coefficient payload is checked support, "
            "but it is not a final residual interval.  The current upstream "
            "proof-source gap is the component Taylor remainder source."
            if component_gap_is_active
            else "No more specific upstream row-source gap was found in the local ledgers."
        ),
        "proofGradeRowsForDirectTarget": False,
        "spendableForCurrentTarget": False,
        "nextImplementablePatch": (
            "Build the component Taylor remainder source consumed by exact "
            "raw-derivative assembly, then regenerate the direct nonzero-model "
            "scaled-remainder certificate."
        ),
        "doNotUseAsClosure": [
            "ShapeSqDeriv tight payload alone",
            "old rows0..11 product assembly budget",
            "stale ShapeSqDeriv rows gap",
        ],
    }


def summarize_existing_ledger(path: Path, keys: list[str]) -> dict[str, Any]:
    data = load_json(path)
    out: dict[str, Any] = {"path": rel(path), "exists": bool(data)}
    for key in keys:
        out[key] = data.get(key)
    return out


def build_direct_row_source_implementation_review() -> dict[str, Any]:
    return {
        "usedComputerUse": True,
        "advisoryOnly": True,
        "recommendedOption": "A_for_partial_nominal_bridge_then_fail_closed_rows",
        "decisionLabel": "CHOSEN: A",
        "decision": (
            "Add the partial nominal polynomial coefficient bridge, but keep "
            "the direct row generator fail-closed until a single proof-grade "
            "whole-expression coefficient/remainder row exists for "
            "collapsedExpression."
        ),
        "firstFileToCreate": rel(NOMINAL_POLYNOMIAL_BRIDGE_FILE),
        "firstAuditArtifacts": [
            rel(ROW_SOURCE_AUDIT_JSON_OUT),
            rel(ROW_SOURCE_AUDIT_MD_OUT),
        ],
        "auditObject": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderCollapsedRowSourceAudit"
        ),
        "auditObjectIsLeanTheorem": False,
        "firstLeanPayloadWhenRowsExist": FIRST_PROOF_PRODUCING_LEAN_FILE,
        "firstLeanDataObjectWhenRowsExist": DIRECT_HORNER_DATA_OBJECT,
        "firstLeanValidityTheoremWhenRowsExist": DIRECT_HORNER_VALID_THEOREM,
        "exactCoefficientSource": {
            "status": "PARTIAL_NOMINAL_POLY_BRIDGE_PRESENT_COMPLETE_STREAM_ABSENT",
            "partialBridgeFile": rel(NOMINAL_POLYNOMIAL_BRIDGE_FILE),
            "partialBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16CollapsedExpression_eq_activeActual_sub_"
                "nominalOrder16Poly"
            ),
            "notes": [
                "primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff is a model coefficient source, not the direct collapsed-expression residual coefficient stream.",
                "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff is the already-subtracted model coefficient source, not coefficients for ComponentSource - NonzeroModelPoly.",
                "The nominal polynomial bridge extracts the rational nominal subtracted polynomial only; it is not a complete coefficient stream for collapsedExpression.",
                "The checked collapse and nominal polynomial bridge do not produce Horner rows or an analytic remainder bound.",
            ],
        },
        "missingRemainderTheorem": {
            "name": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "statement": [
                f"theorem {COLLAPSED_SEGMENT_REMAINDER_THEOREM}",
                "    (i : Fin segmentCount) :",
                "    forall eta in Set.Icc (cellL i : Real) (cellU i : Real),",
                "      norm (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression eta -",
                "        rawOmegaATaylorPolynomial degree (center i) (coeff i) eta) <=",
                "      (polyErrorAbs i : Real)",
            ],
        },
        "minimalRowData": [
            "exact segment cover",
            "proof-grade rational coeff[i][j] for the complete collapsed expression",
            "Lean-checked Horner stage lower/upper bounds",
            f"{COLLAPSED_SEGMENT_REMAINDER_THEOREM} for every segment",
            "exact final +/- BiasedResidualRemainderAbs budget rows",
        ],
        "failureCodeIfRowsMissing": DIRECT_ROW_SOURCE_GAP,
        "whatMustNotBeReused": [
            "killed factor majorants",
            "P45/fullTaylor wrong target",
            "zero-model budget",
            "center jets as uniform bounds",
            "sampled rows",
            "separate actual/nominal norm budgets",
            "nominalOrder16Poly as an independent spendable budget",
        ],
        "whyNotDirectConcretePayloadYet": (
            "The partial nominal polynomial bridge is not the full "
            "collapsedExpression coefficient stream and does not prove the "
            "collapsed-segment remainder theorem."
        ),
        "whyNotB": (
            "B is already subsumed by "
            "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid."
            "of_collapsed_horner_range; adding another alias is not the first "
            "proof-producing row source."
        ),
        "whyNotD": (
            "The route is not impossible; the exact missing proof-row source is "
            "now named."
        ),
        "proofClaimAllowedNow": False,
        "step33A1ClosedClaimed": False,
    }


def build_ledger() -> dict[str, Any]:
    component_taylor_residual_ledger = load_json(COMPONENT_TAYLOR_RESIDUAL_LEDGER_FILE)
    shapesq_deriv_tight_ledger = load_json(SHAPESQ_DERIV_TIGHT_LEDGER_FILE)
    active_actual_horner_row_source_ledger = load_json(
        ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER_FILE
    )
    direct_symbols = file_contains(DIRECT_PAYLOAD_FILE, DIRECT_PAYLOAD_SYMBOLS)
    zero_model_symbols = file_contains(ZERO_MODEL_FILE, ZERO_MODEL_SYMBOLS)
    interval_symbols = file_contains(INTERVAL_PAYLOAD_FILE, INTERVAL_PAYLOAD_SYMBOLS)
    remainder_bridge_symbols = file_contains(
        REMAINDER_BRIDGE_FILE, REMAINDER_BRIDGE_SYMBOLS
    )
    p45_full_taylor_symbols = file_contains(
        P45_FULL_TAYLOR_BRIDGE_FILE, P45_FULL_TAYLOR_BRIDGE_SYMBOLS
    )
    order16_nonzero_model_symbols = file_contains(
        ORDER16_NONZERO_MODEL_FILE, ORDER16_NONZERO_MODEL_SYMBOLS
    )
    direct_interval_payload_symbols = file_contains(
        DIRECT_INTERVAL_PAYLOAD_FILE, DIRECT_INTERVAL_PAYLOAD_SYMBOLS
    )
    direct_model_payload_symbols = file_contains(
        DIRECT_MODEL_PAYLOAD_FILE, DIRECT_MODEL_PAYLOAD_SYMBOLS
    )
    direct_horner_symbols = file_contains(DIRECT_HORNER_FILE, DIRECT_HORNER_SYMBOLS)
    direct_horner_smoke_symbols = file_contains(
        DIRECT_HORNER_SMOKE_FILE, DIRECT_HORNER_SMOKE_SYMBOLS
    )
    direct_source_bridge_symbols = file_contains(
        DIRECT_SOURCE_BRIDGE_FILE, DIRECT_SOURCE_BRIDGE_SYMBOLS
    )
    direct_horner_source_bridge_symbols = file_contains(
        DIRECT_HORNER_SOURCE_BRIDGE_FILE, DIRECT_HORNER_SOURCE_BRIDGE_SYMBOLS
    )
    direct_collapsed_taylor_source_symbols = file_contains(
        DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE, DIRECT_COLLAPSED_TAYLOR_SOURCE_SYMBOLS
    )
    direct_collapsed_source_interval_symbols = file_contains(
        DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE,
        DIRECT_COLLAPSED_SOURCE_INTERVAL_SYMBOLS,
    )
    direct_collapsed_low_degree_source_symbols = file_contains(
        DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE,
        DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_SYMBOLS,
    )
    direct_collapsed_degree0_derivative_shift_symbols = file_contains(
        DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE,
        DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_SYMBOLS,
    )
    direct_collapsed_degree0_center_audit_symbols = file_contains(
        DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE,
        DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_SYMBOLS,
    )
    direct_collapsed_degree0_signed_source_symbols = file_contains(
        DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE,
        DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_SYMBOLS,
    )
    direct_collapsed_degree0_raw_d17_signed_factor_rows_symbols = file_contains(
        DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE,
        DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_SYMBOLS,
    )
    direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_symbols = (
        file_contains(
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_FILE,
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_SYMBOLS,
        )
    )
    nominal_polynomial_bridge_symbols = file_contains(
        NOMINAL_POLYNOMIAL_BRIDGE_FILE, NOMINAL_POLYNOMIAL_BRIDGE_SYMBOLS
    )
    active_actual_remainder_bridge_symbols = file_contains(
        ACTIVE_ACTUAL_REMAINDER_BRIDGE_FILE,
        ACTIVE_ACTUAL_REMAINDER_BRIDGE_SYMBOLS,
    )
    active_actual_horner_segment_symbols = file_contains(
        ACTIVE_ACTUAL_HORNER_SEGMENT_FILE,
        ACTIVE_ACTUAL_HORNER_SEGMENT_SYMBOLS,
    )
    active_actual_horner_family_bridge_symbols = file_contains(
        ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE,
        ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_SYMBOLS,
    )
    biased_source_horner_symbols = file_contains(
        BIASED_SOURCE_HORNER_FILE, BIASED_SOURCE_HORNER_SYMBOLS
    )
    biased_residual_source_segment_symbols = file_contains(
        BIASED_RESIDUAL_INTERVAL_FILE, BIASED_RESIDUAL_SOURCE_SEGMENT_SYMBOLS
    )
    biased_signed_factor_adapter_symbols = file_contains(
        BIASED_SIGNED_FACTOR_ADAPTER_FILE, BIASED_SIGNED_FACTOR_ADAPTER_SYMBOLS
    )
    via_biased_residual_symbols = file_contains(
        VIA_BIASED_RESIDUAL_FILE, VIA_BIASED_RESIDUAL_SYMBOLS
    )

    direct_surface_present = all_true(direct_symbols)
    zero_model_bridge_present = all_true(zero_model_symbols)
    interval_surface_present = all_true(interval_symbols)
    remainder_bridge_present = all_true(remainder_bridge_symbols)
    p45_full_taylor_bridge_present = all_true(p45_full_taylor_symbols)
    order16_nonzero_model_bridge_present = all_true(order16_nonzero_model_symbols)
    direct_interval_payload_present = all_true(direct_interval_payload_symbols)
    direct_model_payload_present = all_true(direct_model_payload_symbols)
    direct_horner_receiver_present = all_true(direct_horner_symbols)
    direct_horner_smoke_present = all_true(direct_horner_smoke_symbols)
    direct_source_bridge_present = all_true(direct_source_bridge_symbols)
    direct_horner_source_bridge_present = all_true(
        direct_horner_source_bridge_symbols
    )
    direct_collapsed_taylor_source_present = all_true(
        direct_collapsed_taylor_source_symbols
    )
    direct_collapsed_source_interval_present = all_true(
        direct_collapsed_source_interval_symbols
    )
    direct_collapsed_low_degree_source_present = all_true(
        direct_collapsed_low_degree_source_symbols
    )
    direct_collapsed_degree0_derivative_shift_present = all_true(
        direct_collapsed_degree0_derivative_shift_symbols
    )
    direct_collapsed_degree0_center_audit_present = all_true(
        direct_collapsed_degree0_center_audit_symbols
    )
    direct_collapsed_degree0_signed_source_present = all_true(
        direct_collapsed_degree0_signed_source_symbols
    )
    direct_collapsed_degree0_raw_d17_signed_factor_rows_present = all_true(
        direct_collapsed_degree0_raw_d17_signed_factor_rows_symbols
    )
    direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present = (
        all_true(
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_symbols
        )
    )
    nominal_polynomial_bridge_present = all_true(
        nominal_polynomial_bridge_symbols
    )
    active_actual_remainder_bridge_present = all_true(
        active_actual_remainder_bridge_symbols
    )
    active_actual_horner_segment_receiver_present = all_true(
        active_actual_horner_segment_symbols
    )
    active_actual_horner_family_bridge_present = all_true(
        active_actual_horner_family_bridge_symbols
    )
    biased_source_horner_present = all_true(biased_source_horner_symbols)
    biased_residual_source_segment_present = all_true(
        biased_residual_source_segment_symbols
    )
    biased_signed_factor_adapter_present = all_true(
        biased_signed_factor_adapter_symbols
    )
    via_biased_residual_bridge_present = all_true(via_biased_residual_symbols)

    proof_status = (
        "direct_nonzero_model_row_worklist_emitted_missing_interval_cert"
        if direct_surface_present
        and zero_model_bridge_present
        and interval_surface_present
        and remainder_bridge_present
        else "direct_nonzero_model_payload_surface_incomplete"
    )

    prior_ledgers = {
        "biasedScaledRemainderInterval": summarize_existing_ledger(
            REQUEST_DIR
            / "step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.json",
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "nonzeroModelResidualBridgeLeanChecked",
                "nonzeroModelResidualSourceBoundLeanChecked",
            ],
        ),
        "biasedResidualHornerPayload": summarize_existing_ledger(
            REQUEST_DIR / "step33_a1_sub0_biased_residual_horner_payload.json",
            [
                "proofStatus",
                "currentGap",
                "proofGrade",
                "scaledRemainderBoundLeanChecked",
                "nonzeroModelResidualBridgeLeanChecked",
                "nonzeroModelResidualSourceBoundLeanChecked",
            ],
        ),
    }
    upstream_row_source_audit = build_upstream_row_source_audit(
        component_taylor_residual_ledger,
        shapesq_deriv_tight_ledger,
    )
    direct_row_source_implementation_review = (
        build_direct_row_source_implementation_review()
    )
    first_concrete_upstream_failure = DIRECT_ROW_SOURCE_GAP
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
    first_concrete_upstream_failure = (
        direct_collapsed_degree0_raw_d17_first_concrete_gap
        if direct_collapsed_degree0_derivative_shift_present
        else direct_collapsed_taylor_row_failure
    )
    preferred_collapsed_low_degree_row_source_contract = {
        "choice": "A",
        "source": "preferred_collapsed_low_degree_signed_source_contract",
        "status": "fail_closed_contract_only",
        "proofGrade": False,
        "sameTarget": True,
        "generatorToPatch": FIRST_PROOF_PRODUCING_GENERATOR,
        "rowSourceLedger": rel(ROW_SOURCE_AUDIT_JSON_OUT),
        "leanFileToEmitOnlyWhenRowsPass": FIRST_PROOF_PRODUCING_LEAN_FILE,
        "finalTheoremWhenRowsPass": FIRST_GENERATED_INTERVAL_THEOREM,
        "rowTheoremWhenRowsPass": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
        "reason": (
            "The direct collapsed degree-0 receiver is the smallest current "
            "whole-expression route: it keeps activeActual-minus-nominal "
            "cancellation inside one target, uses the checked center row, and "
            "requires only a signed derivative source row plus exact rational "
            "budgets before Horner/final-budget emission."
        ),
        "receiverChain": [
            {
                "file": rel(DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE),
                "theorem": (
                    "primaryFiniteRow0Parent0Split100Sub0_"
                    "directCollapsed_degree0_hCenter_generated"
                ),
                "status": (
                    "checked"
                    if direct_collapsed_degree0_center_audit_present
                    else "missing"
                ),
                "failureCodeIfMissing": DIRECT_ROW_SOURCE_GAP,
            },
            {
                "file": rel(DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE),
                "theorem": (
                    "primaryFiniteRow0Parent0Split100Sub0_"
                    "collapsedExpression_deriv_eq_activeActualD17_sub_"
                    "nominalOrder16PolyDeriv"
                ),
                "status": (
                    "checked"
                    if direct_collapsed_degree0_derivative_shift_present
                    else "missing"
                ),
                "failureCodeIfMissing": (
                    COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP
                ),
            },
            {
                "file": rel(DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE),
                "theorem": (
                    "primaryFiniteRow0Parent0Split100Sub0_"
                    "combinedOrder16ScaledRemainder_"
                    "collapsed_degree0_remainder_of_signedD17_source"
                ),
                "status": (
                    "checked"
                    if direct_collapsed_low_degree_source_present
                    else "missing"
                ),
                "failureCodeIfMissing": COLLAPSED_DEGREE0_D17_SIGNED_SOURCE_GAP,
            },
            {
                "file": rel(DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE),
                "theorem": (
                    "Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert."
                    "Valid.to_collapsed_degree0_remainder"
                ),
                "status": (
                    "checked_receiver_rows_missing"
                    if direct_collapsed_degree0_signed_source_present
                    else "missing_receiver"
                ),
                "failureCodeIfMissing": COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP,
            },
        ],
        "requiredExactRowsBeforeLeanEmission": [
            {
                "id": "L0_segment_cover",
                "object": (
                    "Step33Sub0CollapsedDegree0SignedSourceSegmentCover "
                    "for the generated segments covering Set.Icc 0 (1/10)"
                ),
                "status": "missing",
                "failureCode": COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP,
            },
            {
                "id": "L1_signed_source_segment_rows",
                "object": (
                    "proof-grade lower/upper rows for "
                    "ActiveScaleCoeff * D17(ComponentProductActual) - "
                    "deriv(NominalOrder16Poly) on each segment"
                ),
                "status": "missing",
                "failureCode": COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP,
            },
            {
                "id": "L2_deriv_abs_budget",
                "object": (
                    "exact rational proof that the generated lower/upper rows "
                    "are contained in [-derivAbs, derivAbs]"
                ),
                "status": "missing",
                "failureCode": COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL,
            },
            {
                "id": "L3_degree0_remainder_budget",
                "object": (
                    "exact rational proof that coeffErrorAbs + "
                    "derivAbs * (1/20) <= polyErrorAbs"
                ),
                "status": "missing",
                "failureCode": COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL,
            },
            {
                "id": "L4_collapsed_segment_remainder",
                "object": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
                "status": "missing_until_L0_L3_pass",
                "failureCode": DIRECT_ROW_SOURCE_GAP,
            },
            {
                "id": "L5_horner_and_final_budget_rows",
                "object": (
                    "Horner stage bounds, segment cover for the direct family, "
                    "and final +/- BiasedResidualRemainderAbs rows"
                ),
                "status": "missing",
                "failureCode": COLLAPSED_SOURCE_INTERVAL_ROWS_GAP,
            },
        ],
        "firstFailureCodeIfRowsMissing": COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP,
        "parentFailureCodeIfRowsMissing": DIRECT_ROW_SOURCE_GAP,
        "budgetFailureCode": COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL,
        "proofClaimAllowedNow": False,
        "doNotUse": [
            "activeActual degree0 polyErrorAbs as the final direct budget",
            "factorwise RawD17/two-segment budget kills as closure",
            "separate activeActual and nominal independent norm budgets",
            "sampled point rows or Python diagnostics as proof",
            "DirectConcretePayload.lean before all L0-L5 rows pass",
        ],
    }

    source_availability_audit = [
        {
            "source": "order16_nonzero_model_normal_forms",
            "file": rel(ORDER16_NONZERO_MODEL_FILE),
            "artifactStatus": "lean_surface_present",
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "Exact normal-form names exist for the current residual, but "
                "there is no generated signed interval theorem proving the "
                "whole expression inside BiasedResidualRemainderAbs."
            ),
            "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
            "failureCode": DIRECT_ROW_SOURCE_GAP,
        },
        {
            "source": "direct_scaled_remainder_payload_surface",
            "file": rel(DIRECT_PAYLOAD_FILE),
            "artifactStatus": "lean_receiver_present",
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The receiver can consume a proof-grade direct payload, but "
                "the segment rows and whole-expression range certificate are "
                "still missing."
            ),
            "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
            "failureCode": CURRENT_GAP,
        },
        {
            "source": "direct_horner_receiver",
            "file": rel(DIRECT_HORNER_FILE),
            "smokeFile": rel(DIRECT_HORNER_SMOKE_FILE),
            "artifactStatus": (
                "lean_receiver_present_smoke_present"
                if direct_horner_receiver_present and direct_horner_smoke_present
                else "receiver_or_smoke_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The receiver can consume order16 shifted-residual direct Horner "
                "rows for ComponentSource - NonzeroModelPoly, but no concrete "
                "segment data, Horner stage bounds, or proof-grade remainder rows "
                "exist yet."
            ),
            "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
            "failureCode": DIRECT_ROW_SOURCE_GAP,
        },
        {
            "source": "direct_collapsed_expression_source_bridge",
            "file": rel(DIRECT_SOURCE_BRIDGE_FILE),
            "artifactStatus": (
                "lean_source_bridge_present"
                if direct_source_bridge_present
                else "source_bridge_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The exact collapse from ComponentSource - NonzeroModelPoly "
                "to one activeActual-minus-nominal expression is checked, and "
                "a proof-grade full-cell interval for that collapsed expression "
                "can feed the direct source proposition.  No Horner, remainder, "
                "or final budget rows are supplied by this bridge."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
                "DIRECT_COLLAPSE_BRIDGE_CLOSED"
            )
            if direct_source_bridge_present
            else None,
            "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
            "failureCode": DIRECT_ROW_SOURCE_GAP,
        },
        {
            "source": "direct_horner_collapsed_expression_source_bridge",
            "file": rel(DIRECT_HORNER_SOURCE_BRIDGE_FILE),
            "artifactStatus": (
                "lean_collapsed_horner_receiver_bridge_present"
                if direct_horner_source_bridge_present
                else "collapsed_horner_receiver_bridge_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "A Lean-checked receiver bridge now transports a "
                "proof-grade collapsedExpression Horner remainder row into "
                "the existing directRemainder field.  It still supplies no "
                "coefficients, no Horner range rows, and no final budget rows."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_"
                "DIRECT_HORNER_COLLAPSED_SOURCE_BRIDGE_CLOSED"
            )
            if direct_horner_source_bridge_present
            else None,
            "firstMissingProofObject": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "failureCode": DIRECT_ROW_SOURCE_GAP,
        },
        {
            "source": "direct_collapsed_taylor_receiver",
            "file": rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE),
            "artifactStatus": (
                "lean_collapsed_taylor_receiver_present"
                if direct_collapsed_taylor_source_present
                else "collapsed_taylor_receiver_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The Lean receiver converts segment-wise center-jet/order-16 "
                "Taylor proof data for the whole collapsedExpression into the "
                "existing direct Horner receiver.  It intentionally supplies "
                "no center jets, no order-16 derivative rows, no Horner range "
                "rows, and no final budget rows."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_TAYLOR_RECEIVER_CLOSED"
                if direct_collapsed_taylor_source_present
                else None
            ),
            "receiverTheorem": COLLAPSED_TAYLOR_RECEIVER_THEOREM,
            "adapterTheorem": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert."
                "Valid.to_directHorner_valid"
            ),
            "firstMissingProofObject": (
                "proof-grade lower/upper source-interval rows for collapsedExpression"
            ),
            "hiddenMismatchesToGuard": [
                "degree-15/Fin 16 rows must match the DirectHorner degree field",
                "CollapsedExpression already contains D16, so an order-16 row is a high derivative requirement on the source products",
                "segment centers must be local; the full-cell center 1/20 is not a universal local-row substitute",
            ],
            "failureCode": direct_collapsed_taylor_row_failure,
        },
        {
            "source": "direct_collapsed_low_degree_receiver",
            "file": rel(DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE),
            "artifactStatus": (
                "lean_collapsed_low_degree_receiver_present"
                if direct_collapsed_low_degree_source_present
                else "collapsed_low_degree_receiver_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The Lean receiver reduces the whole CollapsedExpression "
                "segment remainder to a degree-0 center row, a signed "
                "activeD17-minus-nominal-polynomial-derivative source row, "
                "and a rational budget comparison.  It avoids the "
                "degree-15/order-16 source row, but still emits no numeric "
                "source rows and no final Horner budget rows."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RECEIVER_CLOSED"
                if direct_collapsed_low_degree_source_present
                else None
            ),
            "receiverTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsed_degree0_remainder_of_signedD17_source"
            ),
            "derivativeShiftFile": rel(
                DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE
            ),
            "derivativeShiftPresent": (
                direct_collapsed_degree0_derivative_shift_present
            ),
            "derivativeShiftTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsedExpression_deriv_eq_activeActualD17_sub_"
                "nominalOrder16PolyDeriv"
            ),
            "centerAuditFile": rel(DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE),
            "centerAuditPresent": direct_collapsed_degree0_center_audit_present,
            "centerAuditTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "directCollapsed_degree0_hCenter_generated"
            ),
            "signedSourceFile": rel(DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE),
            "signedSourcePresent": direct_collapsed_degree0_signed_source_present,
            "signedSourceTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsed_degree0_remainder_of_signed_source_cert"
            ),
            "polyDerivReceiverTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsed_degree0_remainder_of_polyDeriv_signedD17_source"
            ),
            "firstMissingProofObject": (
                "proof-grade signed activeD17-minus-deriv(NominalOrder16Poly) "
                "source row"
            ),
            "failureCode": direct_collapsed_taylor_row_failure,
        },
        {
            "source": "direct_collapsed_source_interval_adapter",
            "file": rel(DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE),
            "artifactStatus": (
                "lean_collapsed_source_interval_adapter_present"
                if direct_collapsed_source_interval_present
                else "source_interval_adapter_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The Lean adapter converts future rational lower/upper "
                "source intervals for the whole collapsedExpression into the "
                "checked absolute-error Taylor receiver.  It supplies no "
                "source rows, no Horner range rows, and no final budget rows."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_SOURCE_INTERVAL_CERT_CLOSED"
                if direct_collapsed_source_interval_present
                else None
            ),
            "sourceIntervalTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsedTaylorValid_of_source_interval"
            ),
            "firstMissingProofObject": (
                "proof-grade rational lower/upper source-interval rows"
            ),
            "failureCode": direct_collapsed_taylor_row_failure,
        },
        {
            "source": "nominal_polynomial_bridge",
            "file": rel(NOMINAL_POLYNOMIAL_BRIDGE_FILE),
            "artifactStatus": (
                "lean_nominal_polynomial_bridge_present"
                if nominal_polynomial_bridge_present
                else "nominal_polynomial_bridge_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The Lean bridge extracts the rational nominal order-16 "
                "polynomial and rewrites collapsedExpression as activeActual "
                "minus nominalOrder16Poly.  This is a coefficient crosswalk "
                "only; the generator still needs one proof-grade "
                "whole-expression collapsed segment remainder row."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_NOMINAL_POLY_COEFF_CROSSWALK_CLOSED"
                if nominal_polynomial_bridge_present
                else None
            ),
            "firstMissingProofObject": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "failureCode": DIRECT_ROW_SOURCE_GAP,
        },
        {
            "source": "active_actual_remainder_bridge",
            "file": rel(ACTIVE_ACTUAL_REMAINDER_BRIDGE_FILE),
            "artifactStatus": (
                "lean_active_actual_remainder_adapter_present"
                if active_actual_remainder_bridge_present
                else "active_actual_remainder_adapter_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The Lean adapter transports a future proof-grade approximation "
                "for scaled D^16(ComponentProductActual) into the collapsed "
                "expression remainder by subtracting nominalOrder16Poly inside "
                "one coefficient stream.  It still supplies no activeActual "
                "coefficients, no analytic remainder theorem, no Horner rows, "
                "and no final budget rows."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_COMBINED_ORDER16_ACTIVE_ACTUAL_NOMINAL_POLY_ALIGNMENT_CLOSED"
                if active_actual_remainder_bridge_present
                else None
            ),
            "firstMissingProofObject": ACTIVE_ACTUAL_SEGMENT_REMAINDER_THEOREM,
            "missingCollapsedRemainderTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "failureCode": ACTIVE_ACTUAL_SEGMENT_REMAINDER_SOURCE_GAP,
            "failureCodeIfAdapterBreaks": ACTIVE_ACTUAL_NOMINAL_POLY_ALIGNMENT_GAP,
        },
        {
            "source": "active_actual_horner_segment_receiver",
            "file": rel(ACTIVE_ACTUAL_HORNER_SEGMENT_FILE),
            "artifactStatus": (
                "lean_active_actual_horner_segment_receiver_present"
                if active_actual_horner_segment_receiver_present
                else "active_actual_horner_segment_receiver_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The Lean receiver fixes the exact future row contract for "
                "scaled D^16(ComponentProductActual): degree-29 coefficients "
                "centered at 1/20 plus a proof-grade `remainderBound`.  It "
                "transports a valid activeActual row through the checked "
                "activeActual-to-collapsed adapter, but still supplies no "
                "concrete coefficients or interval/rational row source."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_SEGMENT_RECEIVER_CLOSED"
                if active_actual_horner_segment_receiver_present
                else None
            ),
            "firstMissingProofObject": ACTIVE_ACTUAL_SEGMENT_REMAINDER_THEOREM,
            "conditionalReceiverTheorem": ACTIVE_ACTUAL_HORNER_SEGMENT_THEOREM,
            "collapsedReceiverTheorem": ACTIVE_ACTUAL_COLLAPSED_HORNER_THEOREM,
            "missingCollapsedRemainderTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "failureCode": ACTIVE_ACTUAL_SEGMENT_REMAINDER_ROW_SOURCE_GAP,
            "failureCodeIfReceiverMissing": (
                ACTIVE_ACTUAL_HORNER_SEGMENT_RECEIVER_GAP
            ),
        },
        {
            "source": "active_actual_horner_family_bridge",
            "file": rel(ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE),
            "artifactStatus": (
                "lean_active_actual_horner_family_bridge_present"
                if active_actual_horner_family_bridge_present
                else "active_actual_horner_family_bridge_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The Lean bridge packages valid activeActual Horner segment "
                "rows as the existing DirectHorner family receiver expects "
                "them, using the checked collapsed coefficient stream.  It "
                "still supplies no activeActual coefficients, no Horner range "
                "rows, no segment cover rows, and no final budget rows."
            ),
            "closedSubgap": (
                "STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_BRIDGE_CLOSED"
                if active_actual_horner_family_bridge_present
                else None
            ),
            "conditionalFamilyTheorem": ACTIVE_ACTUAL_HORNER_FAMILY_VALID_THEOREM,
            "conditionalPayloadTheorem": ACTIVE_ACTUAL_HORNER_FAMILY_PAYLOAD_THEOREM,
            "firstMissingProofObject": ACTIVE_ACTUAL_SEGMENT_REMAINDER_THEOREM,
            "missingCollapsedRemainderTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "failureCode": ACTIVE_ACTUAL_SEGMENT_REMAINDER_ROW_SOURCE_GAP,
            "failureCodeIfBridgeMissing": ACTIVE_ACTUAL_HORNER_FAMILY_ALIGNMENT_GAP,
        },
        {
            "source": "biased_residual_source_segment_receiver_via_bias_shift",
            "file": rel(VIA_BIASED_RESIDUAL_FILE),
            "sourceSegmentFile": rel(BIASED_RESIDUAL_INTERVAL_FILE),
            "artifactStatus": (
                "lean_bias_shift_bridge_checked"
                if via_biased_residual_bridge_present
                and biased_residual_source_segment_present
                else "bias_shift_bridge_or_source_segment_receiver_missing"
            ),
            "sameTarget": True,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The checked bridge converts a biased-residual source-segment "
                "bound into the direct ComponentSource - NonzeroModelPoly "
                "payload, but the canonical direct budget cannot absorb the "
                "positive BiasRat shift: DirectR < BiasRat."
            ),
            "firstMissingProofObject": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_wholeExpression_row"
            ),
            "failureCode": BIAS_SHIFT_BUDGET_FAIL,
            "biasShiftFailureCode": BIAS_SHIFT_GAP,
            "budgetKillTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainder_biasShift_upperBudget_impossible_of_nonneg"
            ),
        },
        {
            "source": "combined_cancellation_order16_direct_zero_model_ledger",
            "ledger": rel(CANCELLATION_DIRECT_LEDGER_FILE),
            "artifactStatus": "local_ledger_present"
            if CANCELLATION_DIRECT_LEDGER_FILE.exists()
            else "ledger_missing",
            "sameTarget": False,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "This threshold zero-model route records a checked interface "
                "but is killed by the rawProduct17 centered-Taylor budget and "
                "does not bound ComponentSource - NonzeroModelPoly."
            ),
            "blockingGap": load_json(CANCELLATION_DIRECT_LEDGER_FILE).get(
                "currentGap"
            ),
            "failureCode": load_json(CANCELLATION_DIRECT_LEDGER_FILE).get(
                "failureCodeIfRawProduct17BoundFails"
            ),
        },
        {
            "source": "combined_order16_source_interval_ledger",
            "ledger": rel(SOURCE_INTERVAL_LEDGER_FILE),
            "artifactStatus": "local_ledger_present"
            if SOURCE_INTERVAL_LEDGER_FILE.exists()
            else "ledger_missing",
            "sameTarget": False,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "This is a zero-model whole-source interval receiver; its "
                "current gap is signed-factor/source rows, not the nonzero "
                "model residual interval needed here."
            ),
            "blockingGap": load_json(SOURCE_INTERVAL_LEDGER_FILE).get(
                "currentGap"
            ),
            "failureCode": load_json(SOURCE_INTERVAL_LEDGER_FILE).get(
                "failureCodeIfRowsMissing"
            ),
        },
        {
            "source": "combined_order16_signed_factor_rows_ledger",
            "ledger": rel(SIGNED_FACTOR_ROWS_LEDGER_FILE),
            "artifactStatus": "local_ledger_present"
            if SIGNED_FACTOR_ROWS_LEDGER_FILE.exists()
            else "ledger_missing",
            "sameTarget": False,
            "proofGradeRowsPresent": False,
            "spendableForCurrentTarget": False,
            "reason": (
                "The signed Leibniz checker interface is alive, but the "
                "centered-Taylor abs-row route is budget-killed and does not "
                "supply the direct nonzero-model source interval."
            ),
            "blockingGap": load_json(SIGNED_FACTOR_ROWS_LEDGER_FILE).get(
                "currentGap"
            ),
            "failureCode": load_json(SIGNED_FACTOR_ROWS_LEDGER_FILE).get(
                "failureCodeIfCenteredTaylorAbsRowsUsed"
            ),
        },
        {
            "source": "p45_full_taylor_bridge",
            "file": rel(P45_FULL_TAYLOR_BRIDGE_FILE),
            "artifactStatus": "lean_surface_present",
            "sameTarget": False,
            "proofGradeRowsPresent": p45_full_taylor_bridge_present,
            "spendableForCurrentTarget": False,
            "reason": (
                "P45/full-Taylor controls a derivative-level residual error; "
                "no local theorem converts it to the order-16 "
                "ComponentSource - NonzeroModelPoly interval."
            ),
            "failureCode": P45_REUSE_FAILURE,
        },
    ]

    row_obligations = [
        {
            "id": "R0_cell_cover",
            "object": "segment cells cover Set.Icc 0 (1/10)",
            "requiredFor": "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover",
            "status": "interface_ready_rows_missing",
            "proofGrade": False,
        },
        {
            "id": "R1_whole_signed_expression_range",
            "object": FIRST_GENERATED_INTERVAL_THEOREM,
            "statement": (
                "for all eta in [0,1/10], "
                "-BiasedResidualRemainderAbs <= ComponentSource eta - "
                "NonzeroModelPoly eta and ComponentSource eta - "
                "NonzeroModelPoly eta <= BiasedResidualRemainderAbs"
            ),
            "status": (
                "missing_first_proof_object_direct_horner_route_selected"
                if first_concrete_upstream_failure
                == COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
                else "missing_first_proof_object"
            ),
            "upstreamFailureCode": first_concrete_upstream_failure,
            "proofGrade": False,
        },
        {
            "id": "R2_horner_or_interval_rows",
            "object": "proof-grade rational/interval rows for the assembled signed expression",
            "requiredFor": FIRST_GENERATED_INTERVAL_THEOREM,
            "status": (
                "collapsed_source_interval_adapter_checked_rows_missing"
                if direct_collapsed_source_interval_present
                else "collapsed_taylor_receiver_checked_source_interval_cert_missing"
                if direct_collapsed_taylor_source_present
                else "direct_horner_receiver_ready_source_bridge_checked_rows_missing"
                if direct_horner_receiver_present
                and direct_horner_smoke_present
                and direct_source_bridge_present
                else "direct_horner_receiver_ready_rows_missing"
                if direct_horner_receiver_present and direct_horner_smoke_present
                else "missing_horner_allowed_only_as_internal_method"
            ),
            "upstreamFailureCode": first_concrete_upstream_failure,
            "directCollapsedTaylorReceiverFile": rel(
                DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE
            ),
            "directCollapsedTaylorReceiverPresent": (
                direct_collapsed_taylor_source_present
            ),
            "directCollapsedTaylorReceiverTheorem": (
                COLLAPSED_TAYLOR_RECEIVER_THEOREM
            ),
            "directCollapsedTaylorFailureCode": direct_collapsed_taylor_row_failure,
            "componentTaylorGapBypassedByDirectHornerRoute": (
                first_concrete_upstream_failure == COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
            ),
            "sourceSplitTheorem": DIRECT_SPLIT_THEOREM,
            "collapsedExpressionBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_eq_collapsedExpression"
            ),
            "collapsedHornerReceiverBridgeTheorem": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert."
                "Valid.of_collapsed_horner_range"
            ),
            "collapsedHornerFamilyBridgeTheorem": (
                "Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert."
                "valid_of_collapsed_horner_rows"
            ),
            "receiverField": DIRECT_HORNER_REMAINDER_FIELD,
            "guard": (
                "The Lean split theorem is allowed as the row-source "
                "crosswalk.  With the collapsed Horner source bridge, a "
                "future row may prove the remainder against "
                "CollapsedExpression and transport it into directRemainder.  "
                "The checked collapsed Taylor receiver now fixes the "
                "center-jet/order-16 row interface, but the coefficient "
                "stream, derivative rows, Horner range rows, and budget rows "
                "are still missing."
            ),
            "proofGrade": False,
        },
        {
            "id": "R2b_biased_residual_bias_shift",
            "object": (
                "reuse biased-residual source-segment bounds through the "
                "checked bias-shift bridge"
            ),
            "requiredFor": FIRST_GENERATED_SOURCE_PROP_THEOREM,
            "status": (
                "bias_shift_bridge_checked_but_current_direct_budget_killed"
                if via_biased_residual_bridge_present
                and biased_residual_source_segment_present
                else "bias_shift_bridge_missing"
            ),
            "bridgeFile": rel(VIA_BIASED_RESIDUAL_FILE),
            "bridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainder_nonzeroModel_sourceProp_of_biasedResidual"
            ),
            "generalBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainder_nonzeroModel_sourceProp_of_biasedResidualSourceProp"
            ),
            "firstMissingProofObject": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_wholeExpression_row"
            ),
            "missingRows": [
                "direct whole-expression row for ComponentSource - NonzeroModelPoly",
                "exact lower bias budget: -DirectR <= BiasRat - biasedAbs",
                "exact upper bias budget: BiasRat + biasedAbs <= DirectR",
            ],
            "failureCode": BIAS_SHIFT_BUDGET_FAIL,
            "biasShiftFailureCode": BIAS_SHIFT_GAP,
            "budgetKillTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainder_biasShift_upperBudget_impossible_of_nonneg"
            ),
            "proofGrade": False,
        },
        {
            "id": "R3_budget_rows",
            "object": (
                "lowerBudget and upperBudget against "
                "BiasedResidualRemainderAbs, including bias-shift rows if "
                "using the biased-residual receiver"
            ),
            "requiredFor": "Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert.Valid",
            "status": "missing",
            "proofGrade": False,
        },
        {
            "id": "R4_source_prop_adapter",
            "object": FIRST_GENERATED_SOURCE_PROP_THEOREM,
            "requiredFor": "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp",
            "status": "interface_ready_depends_on_R1",
            "proofGrade": False,
        },
        {
            "id": "R5_zero_model_payload_target",
            "object": "primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload",
            "requiredFor": "biased residual-Horner zero-model handoff",
            "status": "checked_bridge_depends_on_R4",
            "checkedBridge": bool(zero_model_bridge_present),
            "proofGrade": False,
        },
    ]

    candidate_reuse_routes = [
        {
            "route": "p45_full_taylor",
            "file": rel(P45_FULL_TAYLOR_BRIDGE_FILE),
            "surfacePresent": p45_full_taylor_bridge_present,
            "verdict": "rejected_not_same_expression",
            "failureCode": P45_REUSE_FAILURE,
        },
        {
            "route": "direct_payload_surface",
            "file": rel(DIRECT_PAYLOAD_FILE),
            "surfacePresent": direct_surface_present,
            "verdict": "usable_interface_no_rows",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "direct_interval_payload",
            "file": rel(DIRECT_INTERVAL_PAYLOAD_FILE),
            "surfacePresent": direct_interval_payload_present,
            "verdict": "old_source_interval_interface_not_scaled_nonzero_model_interval",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "direct_model_payload",
            "file": rel(DIRECT_MODEL_PAYLOAD_FILE),
            "surfacePresent": direct_model_payload_present,
            "verdict": "conditional_checker_only_hard_remainder_premise_is_current_gap",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "direct_collapsed_expression_source_bridge",
            "file": rel(DIRECT_SOURCE_BRIDGE_FILE),
            "surfacePresent": direct_source_bridge_present,
            "verdict": "usable_source_bridge_no_interval_rows",
            "failureCode": DIRECT_ROW_SOURCE_GAP,
        },
        {
            "route": "direct_collapsed_taylor_receiver",
            "file": rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE),
            "sourceIntervalFile": rel(DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE),
            "surfacePresent": direct_collapsed_taylor_source_present,
            "sourceIntervalPresent": direct_collapsed_source_interval_present,
            "verdict": (
                "source_interval_receiver_present_rows_missing"
                if direct_collapsed_source_interval_present
                else "usable_receiver_no_source_interval_rows"
                if direct_collapsed_taylor_source_present
                else "receiver_missing"
            ),
            "receiverTheorem": COLLAPSED_TAYLOR_RECEIVER_THEOREM,
            "sourceIntervalTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsedTaylorValid_of_source_interval"
            ),
            "failureCode": direct_collapsed_taylor_row_failure,
        },
        {
            "route": "direct_collapsed_degree0_receiver",
            "file": rel(DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE),
            "surfacePresent": direct_collapsed_low_degree_source_present,
            "verdict": (
                "preferred_low_degree_signed_source_surface_present_interval_rows_or_budget_missing"
                if direct_collapsed_degree0_signed_source_present
                else
                "preferred_low_degree_derivative_shift_and_center_present_poly_deriv_rows_or_budget_missing"
                if direct_collapsed_degree0_derivative_shift_present
                and direct_collapsed_degree0_center_audit_present
                else
                "preferred_low_degree_derivative_shift_present_poly_deriv_rows_missing"
                if direct_collapsed_degree0_derivative_shift_present
                else "preferred_low_degree_receiver_present_signed_d17_rows_missing"
                if direct_collapsed_low_degree_source_present
                else "preferred_low_degree_receiver_missing"
            ),
            "receiverTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsed_degree0_remainder_of_signedD17_source"
            ),
            "centerAuditFile": rel(DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE),
            "centerAuditPresent": direct_collapsed_degree0_center_audit_present,
            "centerAuditTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "directCollapsed_degree0_hCenter_generated"
            ),
            "signedSourceFile": rel(DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE),
            "signedSourcePresent": direct_collapsed_degree0_signed_source_present,
            "signedSourceTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "collapsed_degree0_remainder_of_signed_source_cert"
            ),
            "failureCode": direct_collapsed_taylor_row_failure,
        },
        {
            "route": "biased_source_horner",
            "file": rel(BIASED_SOURCE_HORNER_FILE),
            "surfacePresent": biased_source_horner_present,
            "verdict": "not_same_target_without_new_bridge",
            "failureCode": CURRENT_GAP,
        },
        {
            "route": "biased_residual_source_segments_via_bias_shift",
            "file": rel(VIA_BIASED_RESIDUAL_FILE),
            "sourceSegmentFile": rel(BIASED_RESIDUAL_INTERVAL_FILE),
            "surfacePresent": via_biased_residual_bridge_present,
            "sourceSegmentReceiverPresent": biased_residual_source_segment_present,
            "verdict": (
                "checked_bridge_but_canonical_direct_budget_killed_by_bias_shift"
            ),
            "firstMissingProofObject": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_wholeExpression_row"
            ),
            "failureCode": BIAS_SHIFT_BUDGET_FAIL,
            "biasShiftFailureCode": BIAS_SHIFT_GAP,
            "budgetKillTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainder_biasShift_upperBudget_impossible_of_nonneg"
            ),
        },
        {
            "route": "biased_signed_factor_adapter",
            "file": rel(BIASED_SIGNED_FACTOR_ADAPTER_FILE),
            "surfacePresent": biased_signed_factor_adapter_present,
            "verdict": "adapter_for_biased_route_only_not_direct_nonzero_model_rows",
            "failureCode": CURRENT_GAP,
        },
    ]

    return {
        "schema": SCHEMA,
        "generatedAt": datetime.now(timezone.utc).isoformat(),
        "route": "direct_nonzero_model_scaled_remainder_interval",
        "directPayloadFile": rel(DIRECT_PAYLOAD_FILE),
        "zeroModelPayloadFile": rel(ZERO_MODEL_FILE),
        "intervalPayloadFile": rel(INTERVAL_PAYLOAD_FILE),
        "remainderBridgeFile": rel(REMAINDER_BRIDGE_FILE),
        "p45FullTaylorBridgeFile": rel(P45_FULL_TAYLOR_BRIDGE_FILE),
        "order16NonzeroModelFile": rel(ORDER16_NONZERO_MODEL_FILE),
        "directIntervalPayloadFile": rel(DIRECT_INTERVAL_PAYLOAD_FILE),
        "directModelPayloadFile": rel(DIRECT_MODEL_PAYLOAD_FILE),
        "directHornerFile": rel(DIRECT_HORNER_FILE),
        "directHornerSmokeFile": rel(DIRECT_HORNER_SMOKE_FILE),
        "directSourceBridgeFile": rel(DIRECT_SOURCE_BRIDGE_FILE),
        "directHornerSourceBridgeFile": rel(DIRECT_HORNER_SOURCE_BRIDGE_FILE),
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
        "nominalPolynomialBridgeFile": rel(NOMINAL_POLYNOMIAL_BRIDGE_FILE),
        "activeActualRemainderBridgeFile": rel(ACTIVE_ACTUAL_REMAINDER_BRIDGE_FILE),
        "activeActualHornerSegmentFile": rel(ACTIVE_ACTUAL_HORNER_SEGMENT_FILE),
        "activeActualHornerFamilyBridgeFile": rel(
            ACTIVE_ACTUAL_HORNER_FAMILY_BRIDGE_FILE
        ),
        "activeActualHornerRowSourceLedgerFile": rel(
            ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER_FILE
        ),
        "activeActualDegree0AuditFile": rel(ACTIVE_ACTUAL_DEGREE0_AUDIT_FILE),
        "activeActualDegree0DirectBudgetKillTheorem": (
            ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_KILL_THEOREM
        ),
        "activeActualDegree0DirectBudgetFailureCode": (
            ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_FAIL
        ),
        "biasedSourceHornerFile": rel(BIASED_SOURCE_HORNER_FILE),
        "biasedResidualIntervalFile": rel(BIASED_RESIDUAL_INTERVAL_FILE),
        "biasedSignedFactorAdapterFile": rel(BIASED_SIGNED_FACTOR_ADAPTER_FILE),
        "viaBiasedResidualFile": rel(VIA_BIASED_RESIDUAL_FILE),
        "directPayloadSymbols": direct_symbols,
        "zeroModelSymbols": zero_model_symbols,
        "intervalPayloadSymbols": interval_symbols,
        "remainderBridgeSymbols": remainder_bridge_symbols,
        "p45FullTaylorBridgeSymbols": p45_full_taylor_symbols,
        "order16NonzeroModelSymbols": order16_nonzero_model_symbols,
        "directIntervalPayloadSymbols": direct_interval_payload_symbols,
        "directModelPayloadSymbols": direct_model_payload_symbols,
        "directHornerSymbols": direct_horner_symbols,
        "directHornerSmokeSymbols": direct_horner_smoke_symbols,
        "directSourceBridgeSymbols": direct_source_bridge_symbols,
        "directHornerSourceBridgeSymbols": direct_horner_source_bridge_symbols,
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
        "nominalPolynomialBridgeSymbols": nominal_polynomial_bridge_symbols,
        "activeActualRemainderBridgeSymbols": (
            active_actual_remainder_bridge_symbols
        ),
        "activeActualHornerSegmentSymbols": (
            active_actual_horner_segment_symbols
        ),
        "activeActualHornerFamilyBridgeSymbols": (
            active_actual_horner_family_bridge_symbols
        ),
        "biasedSourceHornerSymbols": biased_source_horner_symbols,
        "biasedResidualSourceSegmentSymbols": biased_residual_source_segment_symbols,
        "biasedSignedFactorAdapterSymbols": biased_signed_factor_adapter_symbols,
        "viaBiasedResidualSymbols": via_biased_residual_symbols,
        "directPayloadSurfacePresent": direct_surface_present,
        "zeroModelBridgePresent": zero_model_bridge_present,
        "intervalPayloadSurfacePresent": interval_surface_present,
        "remainderBridgePresent": remainder_bridge_present,
        "p45FullTaylorBridgePresent": p45_full_taylor_bridge_present,
        "order16NonzeroModelBridgePresent": order16_nonzero_model_bridge_present,
        "directIntervalPayloadPresent": direct_interval_payload_present,
        "directModelPayloadPresent": direct_model_payload_present,
        "directHornerReceiverPresent": direct_horner_receiver_present,
        "directHornerSmokePresent": direct_horner_smoke_present,
        "directSourceBridgePresent": direct_source_bridge_present,
        "directHornerSourceBridgePresent": direct_horner_source_bridge_present,
        "directCollapsedTaylorSourcePresent": direct_collapsed_taylor_source_present,
        "directCollapsedSourceIntervalPresent": (
            direct_collapsed_source_interval_present
        ),
        "directCollapsedSourceIntervalLeanChecked": (
            direct_collapsed_source_interval_present
        ),
        "directCollapsedLowDegreeSourcePresent": (
            direct_collapsed_low_degree_source_present
        ),
        "directCollapsedLowDegreeSourceLeanChecked": (
            direct_collapsed_low_degree_source_present
        ),
        "directCollapsedDegree0DerivativeShiftPresent": (
            direct_collapsed_degree0_derivative_shift_present
        ),
        "directCollapsedDegree0DerivativeShiftLeanChecked": (
            direct_collapsed_degree0_derivative_shift_present
        ),
        "directCollapsedDegree0CenterAuditPresent": (
            direct_collapsed_degree0_center_audit_present
        ),
        "directCollapsedDegree0CenterAuditLeanChecked": (
            direct_collapsed_degree0_center_audit_present
        ),
        "directCollapsedDegree0SignedSourcePresent": (
            direct_collapsed_degree0_signed_source_present
        ),
        "directCollapsedDegree0SignedSourceLeanChecked": (
            direct_collapsed_degree0_signed_source_present
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsFile": rel(
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsSymbols": (
            direct_collapsed_degree0_raw_d17_signed_factor_rows_symbols
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsPresent": (
            direct_collapsed_degree0_raw_d17_signed_factor_rows_present
        ),
        "directCollapsedDegree0RawD17SignedFactorRowsLeanChecked": (
            direct_collapsed_degree0_raw_d17_signed_factor_rows_present
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillFile": rel(
            DIRECT_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_KILL_FILE
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillSymbols": (
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_symbols
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillPresent": (
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetKillLeanChecked": (
            direct_collapsed_degree0_raw_d17_sharp_two_segment_budget_kill_present
        ),
        "directCollapsedDegree0RawD17SharpTwoSegmentBudgetFailureCode": (
            COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_FAIL
        ),
        "nominalPolynomialBridgePresent": nominal_polynomial_bridge_present,
        "activeActualRemainderBridgePresent": (
            active_actual_remainder_bridge_present
        ),
        "activeActualRemainderBridgeLeanChecked": (
            active_actual_remainder_bridge_present
        ),
        "activeActualHornerSegmentReceiverPresent": (
            active_actual_horner_segment_receiver_present
        ),
        "activeActualHornerSegmentReceiverLeanChecked": (
            active_actual_horner_segment_receiver_present
        ),
        "activeActualHornerFamilyBridgePresent": (
            active_actual_horner_family_bridge_present
        ),
        "activeActualHornerFamilyBridgeLeanChecked": (
            active_actual_horner_family_bridge_present
        ),
        "activeActualHornerRowSourceLedger": summarize_existing_ledger(
            ACTIVE_ACTUAL_HORNER_ROW_SOURCE_LEDGER_FILE,
            [
                "schema",
                "proofStatus",
                "proofGrade",
                "proofSafeClosedFields",
                "currentGap",
                "firstFailureCode",
                "outLeanWritten",
                "leanValidationStatus",
            ],
        ),
        "biasedSourceHornerPresent": biased_source_horner_present,
        "biasedResidualSourceSegmentPresent": biased_residual_source_segment_present,
        "biasedSignedFactorAdapterPresent": biased_signed_factor_adapter_present,
        "viaBiasedResidualBridgePresent": via_biased_residual_bridge_present,
        "proofStatus": proof_status,
        "proofGrade": False,
        "currentGap": direct_collapsed_taylor_row_failure,
        "parentGap": PARENT_GAP,
        "firstFailureCode": direct_collapsed_taylor_row_failure,
        "firstRowFailureCode": direct_collapsed_taylor_row_failure,
        "directRowFailureCode": DIRECT_ROW_SOURCE_GAP,
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
        "biasShiftFailureCode": BIAS_SHIFT_GAP,
        "biasShiftBudgetFailureCode": BIAS_SHIFT_BUDGET_FAIL,
        "firstConcreteUpstreamFailureCode": first_concrete_upstream_failure,
        "firstMissingProofObject": FIRST_GENERATED_INTERVAL_THEOREM,
        "rowWorklistEmitted": True,
        "rowWorklistFile": rel(ROW_OBLIGATIONS_JSON_OUT),
        "rowSourceAuditEmitted": True,
        "rowSourceAuditFile": rel(ROW_SOURCE_AUDIT_JSON_OUT),
        "rowSourceAuditMarkdownFile": rel(ROW_SOURCE_AUDIT_MD_OUT),
        "directRowSourceImplementationReview": (
            direct_row_source_implementation_review
        ),
        "rowObligations": row_obligations,
        "candidateReuseRoutes": candidate_reuse_routes,
        "sourceAvailabilityAudit": source_availability_audit,
        "upstreamRowSourceAudit": upstream_row_source_audit,
        "p45FullTaylorReuseVerdict": "not_spendable_for_order16_direct_source_bound",
        "p45FullTaylorReuseFailureCode": P45_REUSE_FAILURE,
        "proshkaRouteReviewDecision": "CHOSEN: A",
        "proshkaRouteReviewQuestion": (
            "Does the existing P45/full-Taylor interval machinery prove the "
            "order-16 ComponentSource - NonzeroModelPoly source bound, or is "
            "a separate direct certificate target still needed?"
        ),
        "proshkaRouteReviewAnswer": (
            "A: proceed with the direct rational/Horner interval generator; "
            "P45/full-Taylor bounds a different derivative-level expression "
            "and does not prove the uniform order-16 source-minus-nonzero-model "
            "interval."
        ),
        "proshkaRowWorklistDecision": "CHOSEN: A",
        "proshkaRowWorklistAnswer": (
            "First patch should emit exact row obligations; an immediate Lean "
            "certificate would still be conditional without proof-grade "
            "whole-expression remainder source rows."
        ),
        "proshkaPostBudgetKillDecision": "CHOSEN: A",
        "proshkaPostBudgetKillContext": (
            "The centered-Taylor factor-derivative receiver route was tried "
            "as a proof/kill test and is budget-killed by "
            f"{POST_BUDGET_KILL_FAILURE}."
        ),
        "proshkaPostBudgetKillAnswer": (
            "Build a proof-grade rational/interval generator for the whole "
            "signed expression ComponentSource - NonzeroModelPoly on "
            "[0,1/10].  A Horner split is only an implementation technique "
            "inside that direct certificate."
        ),
        "latestComputerUseDegree0BudgetKillReview": {
            "used": True,
            "destination": "in-app ChatGPT Pro / Louise browser",
            "recommendedOption": "A",
            "decision": (
                "The activeActual degree-0 source theorem is useful as a "
                "checked local source, but it is killed for the direct "
                "Step33A.1-A payload budget.  The next proof-producing route "
                "must build the direct collapsedExpression segment remainder "
                "for ComponentSource - NonzeroModelPoly as one expression."
            ),
            "firstFileToEdit": FIRST_PROOF_PRODUCING_GENERATOR,
            "firstLeanFileToCreateWhenRowsPass": FIRST_PROOF_PRODUCING_LEAN_FILE,
            "firstTheoremTarget": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "activeActualDegree0AuditFile": rel(ACTIVE_ACTUAL_DEGREE0_AUDIT_FILE),
            "budgetKillTheorem": ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_KILL_THEOREM,
            "failureCodeIfBudgetFalse": ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_FAIL,
            "failureCodeIfRowsStillMissing": DIRECT_ROW_SOURCE_GAP,
            "doNotReuse": [
                "degree0 activeActual polyErrorAbs as the direct payload budget",
                "RawProduct18 absolute majorant as a same-target direct row",
                "separate activeActual/nominal norm budgets",
                "sampled rows",
            ],
            "proofClaimAllowedNow": False,
        },
        "directHornerRowRouteReview": {
            "used": True,
            "destination": "in-app ChatGPT Pro / Louise browser",
            "recommendedOption": "A",
            "decision": "direct_collapsed_expression_row_source",
            "firstFileToEdit": (
                "scripts/generate_step33_a1_sub0_combined_order16_"
                "scaled_remainder_direct_payload.py"
            ),
            "firstLeanFileToCreateWhenRowsPass": FIRST_PROOF_PRODUCING_LEAN_FILE,
            "firstObject": (
                DIRECT_HORNER_DATA_OBJECT
            ),
            "validTheorem": DIRECT_HORNER_VALID_THEOREM,
            "finalTheorem": FIRST_GENERATED_INTERVAL_THEOREM,
            "theoremShape": (
                "for all eta in Set.Icc 0 (1/10), -R <= "
                "ComponentSource eta - NonzeroModelPoly eta and "
                "ComponentSource eta - NonzeroModelPoly eta <= R, with "
                "R = CombinedOrder16BiasedResidualRemainderAbs"
            ),
            "requiredRows": [
                "exact segment cover",
                "one same-target rational polynomial coefficient stream for collapsedExpression",
                "Lean-checked Horner stage bounds",
                "proof-grade collapsedExpression remainder rows",
                "exact final +/- R budget rows",
            ],
            "failureCodeIfFails": DIRECT_ROW_SOURCE_GAP,
            "reason": (
                "The activeActual degree-0 source is Lean-checked but killed "
                "for the final direct budget.  The direct receiver subtracts "
                "NonzeroModelPoly and preserves the needed cancellation, so "
                "the next proof-grade route must keep the collapsedExpression "
                "as one object until the final norm/budget rows."
            ),
            "proofClaimAllowedNow": False,
        },
        "directCollapsedTaylorReceiverReview": {
            "used": True,
            "destination": "in-app ChatGPT Pro / Louise browser",
            "recommendedOption": "C",
            "file": rel(DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE),
            "present": direct_collapsed_taylor_source_present,
            "sourceIntervalFile": rel(DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE),
            "sourceIntervalPresent": direct_collapsed_source_interval_present,
            "sourceIntervalLeanChecked": direct_collapsed_source_interval_present,
            "lowDegreeSourceFile": rel(DIRECT_COLLAPSED_LOW_DEGREE_SOURCE_FILE),
            "lowDegreeSourcePresent": direct_collapsed_low_degree_source_present,
            "lowDegreeSourceLeanChecked": direct_collapsed_low_degree_source_present,
            "degree0DerivativeShiftFile": rel(
                DIRECT_COLLAPSED_DEGREE0_DERIVATIVE_SHIFT_FILE
            ),
            "degree0DerivativeShiftPresent": (
                direct_collapsed_degree0_derivative_shift_present
            ),
            "degree0DerivativeShiftLeanChecked": (
                direct_collapsed_degree0_derivative_shift_present
            ),
            "degree0CenterAuditFile": rel(
                DIRECT_COLLAPSED_DEGREE0_CENTER_AUDIT_FILE
            ),
            "degree0CenterAuditPresent": (
                direct_collapsed_degree0_center_audit_present
            ),
            "degree0CenterAuditLeanChecked": (
                direct_collapsed_degree0_center_audit_present
            ),
            "degree0SignedSourceFile": rel(
                DIRECT_COLLAPSED_DEGREE0_SIGNED_SOURCE_FILE
            ),
            "degree0SignedSourcePresent": (
                direct_collapsed_degree0_signed_source_present
            ),
            "degree0SignedSourceLeanChecked": (
                direct_collapsed_degree0_signed_source_present
            ),
            "degree0RawD17SignedFactorRowsFile": rel(
                DIRECT_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_ROWS_FILE
            ),
            "degree0RawD17SignedFactorRowsPresent": (
                direct_collapsed_degree0_raw_d17_signed_factor_rows_present
            ),
            "degree0RawD17SignedFactorRowsLeanChecked": (
                direct_collapsed_degree0_raw_d17_signed_factor_rows_present
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
                "Horner stage bounds and final +/- BiasedResidualRemainderAbs budget rows",
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
        "directSplitIdentity": {
            "theorem": DIRECT_SPLIT_THEOREM,
            "file": rel(ORDER16_NONZERO_MODEL_FILE),
            "present": order16_nonzero_model_symbols.get(DIRECT_SPLIT_THEOREM, False),
            "collapsedBridgeFile": rel(DIRECT_SOURCE_BRIDGE_FILE),
            "collapsedBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_eq_collapsedExpression"
            ),
            "collapsedBridgePresent": direct_source_bridge_present,
            "collapsedSourcePropBridgeTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval"
            ),
            "leftHandSide": (
                "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16"
                "ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0"
                "CombinedOrder16NonzeroModelPoly eta"
            ),
            "rightHandSide": DIRECT_SPLIT_RHS,
            "collapsedWholeExpressionRhs": DIRECT_COLLAPSED_RHS,
            "receiverField": DIRECT_HORNER_REMAINDER_FIELD,
            "usableAsRowSourceCrosswalk": order16_nonzero_model_symbols.get(
                DIRECT_SPLIT_THEOREM, False
            ),
            "proofGradeRowsPresent": False,
            "budgetSpendAllowed": False,
            "guard": (
                "This identity is bookkeeping/crosswalk evidence only until "
                "a generator supplies proof-grade directRemainder rows and "
                "final budget rows.  It does not itself prove the interval."
            ),
        },
        "directWholeExpressionRowReview": {
            "used": True,
            "destination": "in-app ChatGPT Pro / Louise browser",
            "recommendedOption": "C",
            "decision": "fail_closed_collapsed_row_source_audit",
            "firstFileToEdit": (
                "scripts/generate_step33_a1_sub0_combined_order16_"
                "scaled_remainder_direct_payload.py"
            ),
            "firstLeanFileToCreateWhenRowsPass": FIRST_PROOF_PRODUCING_LEAN_FILE,
            "firstObject": (
                DIRECT_HORNER_DATA_OBJECT
            ),
            "rowTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "rowTheoremShape": (
                "for every segment, norm of collapsedExpression eta minus "
                "the segment polynomial is at most polyErrorAbs; the existing "
                "Lean bridge then transports that row into directRemainder"
            ),
            "collapsedExpression": DIRECT_COLLAPSED_RHS,
            "requiredRows": [
                "exact collapse from cancellation+scale-mismatch split to activeActual-minus-nominal form (checked in DirectSourceBridge)",
                "one rational coefficient stream for the complete signed expression",
                "proof-grade collapsedExpression segment remainder row",
                "exact Horner stageLower/stageUpper rows",
                "exact [0,1/10] coverage",
                "final +/- BiasedResidualRemainderAbs budget rows",
            ],
            "doNotProduce": [
                "DirectConcretePayload.lean before the collapsed segment remainder theorem exists",
                "separate error budgets for the two split summands",
                "triangle-loss resurrection of the killed factor-majorant route",
                "biased residual/local-model detour before this row source is killed",
            ],
            "failureCodeIfFails": DIRECT_ROW_SOURCE_GAP,
            "proofClaimAllowedNow": False,
        },
        "preferredCollapsedLowDegreeRowSourceContract": (
            preferred_collapsed_low_degree_row_source_contract
        ),
        "biasedResidualReuseReview": {
            "used": True,
            "destination": "in-app ChatGPT Pro / Louise browser",
            "reuse": "YES_WITH_EXPLICIT_BIAS_SHIFT",
            "decision": "reuse_biased_residual_source_segment_receiver_via_checked_bias_shift",
            "currentBudgetVerdict": "KILLED_FOR_CANONICAL_DIRECT_R",
            "bridgeFile": rel(VIA_BIASED_RESIDUAL_FILE),
            "sourceSegmentFile": rel(BIASED_RESIDUAL_INTERVAL_FILE),
            "leanBridgeChecked": via_biased_residual_bridge_present,
            "firstGeneratorPatch": (
                "scripts/generate_step33_a1_sub0_combined_order16_"
                "scaled_remainder_direct_payload.py"
            ),
            "firstLeanPayloadFile": (
                "Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16"
                "ScaledRemainderViaBiasedResidualPayload.lean"
            ),
            "firstMissingProofGradeRow": (
                "the direct whole-expression row; the biased-residual reuse "
                "route is killed by DirectR < BiasRat"
            ),
            "requiredRows": [
                "direct whole-expression proof row for ComponentSource - NonzeroModelPoly",
                "exact bias shift theorem from direct residual to biased residual",
                "budget-kill theorem showing DirectR < BiasRat",
                "fallback exact segment cover/Horner rows for the direct target",
            ],
            "warning": (
                "Source - BiasedModel is not Source - NonzeroModel; the fixed "
                "BiasRat shift and the BiasRat +/- biasedAbs budget rows must "
                "be checked in the direct target normalization.  In the current "
                "canonical budget they fail because DirectR < BiasRat."
            ),
            "failureCodeIfBridgeMissing": BIAS_SHIFT_GAP,
            "failureCodeIfRowsMissing": DIRECT_ROW_SOURCE_GAP,
            "failureCodeIfBudgetFails": BIAS_SHIFT_BUDGET_FAIL,
            "budgetKillTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "scaledRemainder_biasShift_upperBudget_impossible_of_nonneg"
            ),
            "proofClaimAllowedNow": False,
        },
        "splitSummandsPolicy": {
            "algebraicSplitAllowedForRowSource": True,
            "independentNormSpendAllowed": False,
            "finalReceiverTargetMustBeWholeExpression": True,
            "proshkaFollowupDecision": "CHOSEN: C",
            "nominalPolynomialBridgeDecision": "CHOSEN: A",
            "activeActualRemainderBridgeDecision": "CHOSEN: A",
            "activeActualHornerSegmentReceiverDecision": "CHOSEN: B",
            "activeActualHornerFamilyBridgeDecision": "CHOICE: A",
            "partialNominalPolynomialBridgeAllowed": True,
            "oneCoefficientStreamRequired": True,
            "reason": (
                "The local Lean split names the exact target expression, but "
                "the proof-grade row object must still be one coefficient "
                "stream for the complete signed expression.  The nominal "
                "polynomial bridge is allowed only as a coefficient crosswalk; "
                "separate product-summand budgets are not spendable, because "
                "they revive the killed triangle-loss route."
            ),
        },
        "postBudgetKillFailureCode": POST_BUDGET_KILL_FAILURE,
        "nextImplementablePatch": (
            "Build the direct whole-expression collapsedExpression "
            "lower/upper source-interval rows through "
            "primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_"
            "collapsedTaylorValid_of_source_interval, then emit Horner and "
            f"budget rows for {COLLAPSED_SEGMENT_REMAINDER_THEOREM}.  Keep "
            f"{ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_KILL_THEOREM} as a "
            "Lean-checked kill for spending the degree-0 activeActual source "
            "as the final direct payload budget.  Do not emit "
            "DirectConcretePayload.lean before collapsed rows, Horner rows, "
            "and final +/- BiasedResidualRemainderAbs budget rows exist."
        ),
        "nextProofProducingPatch": {
            "generator": FIRST_PROOF_PRODUCING_GENERATOR,
            "preferredContract": (
                "preferredCollapsedLowDegreeRowSourceContract"
            ),
            "rowSourceGenerator": FIRST_PROOF_PRODUCING_GENERATOR,
            "rowSourceLedger": rel(ROW_SOURCE_AUDIT_JSON_OUT),
            "leanFile": FIRST_PROOF_PRODUCING_LEAN_FILE,
            "theorem": FIRST_GENERATED_INTERVAL_THEOREM,
            "missingRemainderTheorem": COLLAPSED_SEGMENT_REMAINDER_THEOREM,
            "activeActualMissingRemainderTheorem": (
                ACTIVE_ACTUAL_SEGMENT_REMAINDER_THEOREM
            ),
            "activeActualHornerReceiverTheorem": (
                ACTIVE_ACTUAL_HORNER_SEGMENT_THEOREM
            ),
            "activeActualCollapsedHornerTheorem": (
                ACTIVE_ACTUAL_COLLAPSED_HORNER_THEOREM
            ),
            "activeActualHornerFamilyTheorem": (
                ACTIVE_ACTUAL_HORNER_FAMILY_VALID_THEOREM
            ),
            "activeActualHornerFamilyPayloadTheorem": (
                ACTIVE_ACTUAL_HORNER_FAMILY_PAYLOAD_THEOREM
            ),
            "sourcePropTheorem": FIRST_GENERATED_SOURCE_PROP_THEOREM,
            "collapsedTaylorReceiverFile": rel(
                DIRECT_COLLAPSED_TAYLOR_SOURCE_FILE
            ),
            "collapsedTaylorReceiverTheorem": (
                COLLAPSED_TAYLOR_RECEIVER_THEOREM
            ),
            "collapsedSourceIntervalFile": rel(
                DIRECT_COLLAPSED_SOURCE_INTERVAL_FILE
            ),
            "collapsedSourceIntervalTheorem": (
                "primaryFiniteRow0Parent0Split100Sub0_"
                "combinedOrder16ScaledRemainder_"
                "collapsedTaylorValid_of_source_interval"
            ),
            "failureCodeIfRowsStillMissing": (
                COLLAPSED_SOURCE_INTERVAL_ROWS_GAP
            ),
            "failureCodeIfSourceIntervalCertMissing": (
                COLLAPSED_SOURCE_INTERVAL_CERT_GAP
            ),
            "parentFailureCodeIfRowsStillMissing": DIRECT_ROW_SOURCE_GAP,
            "failureCodeIfCollapsedTaylorReceiverFails": (
                COLLAPSED_TAYLOR_RECEIVER_GAP
            ),
            "failureCodeIfFamilyBridgeMissing": (
                ACTIVE_ACTUAL_HORNER_FAMILY_ALIGNMENT_GAP
            ),
            "failureCodeIfReceiverMissing": (
                ACTIVE_ACTUAL_HORNER_SEGMENT_RECEIVER_GAP
            ),
            "activeActualDegree0BudgetKillTheorem": (
                ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_KILL_THEOREM
            ),
            "activeActualDegree0BudgetFailureCode": (
                ACTIVE_ACTUAL_DEGREE0_DIRECT_BUDGET_FAIL
            ),
            "proofClaimAllowedNow": False,
        },
        "upstreamProofProducingPatch": {
            "failureCode": first_concrete_upstream_failure,
            "patch": upstream_row_source_audit["nextImplementablePatch"],
            "proofClaimAllowedNow": False,
        },
        "directNonzeroModelIntervalRowsLeanChecked": False,
        "directNonzeroModelSourcePropLeanChecked": False,
        "directHornerRowsLeanChecked": False,
        "zeroModelPayloadTargetLeanChecked": zero_model_bridge_present,
        "step33A1ClosedClaimed": False,
        "doNotSplitSummands": True,
        "doNotUseIndependentSummandBudgets": True,
        "targetExpression": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16"
            "ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0"
            "CombinedOrder16NonzeroModelPoly eta"
        ),
        "targetBudget": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16Biased"
            "ResidualRemainderAbs"
        ),
        "targetProp": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderNonzeroModelSourceProp"
        ),
        "targetPayload": (
            "primaryFiniteRow0Parent0Split100Sub0CombinedOrder16"
            "ScaledRemainderDirectPayloadTarget"
        ),
        "firstGeneratedIntervalTheorem": FIRST_GENERATED_INTERVAL_THEOREM,
        "firstGeneratedSourcePropTheorem": FIRST_GENERATED_SOURCE_PROP_THEOREM,
        "whyP45FullTaylorIsNotEnough": (
            "The P45/full-Taylor bridge rewrites a derivative-level residual "
            "error into the scaled cancellation RHS. The current direct target "
            "is the order-16 source residual ComponentSource - NonzeroModelPoly, "
            "which Lean identifies with ActiveScaleCoeff * D^16"
            "(ComponentProductCancellationResidual) plus the same-unit "
            "scale-mismatch nominal-product term. No local theorem converts the "
            "P45/full-Taylor interval into this order-16 source interval."
        ),
        "theoremShape": (
            "prove a signed interval on [0,1/10] for ComponentSource - "
            "NonzeroModelPoly inside +/- BiasedResidualRemainderAbs; then "
            "use primaryFiniteRow0Parent0Split100Sub0_"
            "combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_"
            "full_cell_interval or a direct family payload target"
        ),
        "certificateShape": [
            "exact target-expression hash/name",
            "segment cells covering [0,1/10]",
            "per-segment rational polynomial coefficients if a model is used",
            "exact Horner stage bounds if a Horner model is used",
            "proof-grade whole-expression remainder rows",
            f"{COLLAPSED_SEGMENT_REMAINDER_THEOREM} for every segment",
            "final lower/upper budget rows against BiasedResidualRemainderAbs",
            "the Lean split theorem may be used to generate the row source",
            "no independent product-summand norm budgets unless recombined "
            "into the directRemainder row",
            "global residualAbs = BiasedResidualRemainderAbs",
        ],
        "doNotReuseAfterPostBudgetKill": [
            "centered-Taylor factor majorants killed by exact budget",
            "P45/full-Taylor machinery: wrong target",
            "zero-model/direct-source budget",
            "independent product-summand norm bounds",
            "center jets as uniform full-cell intervals",
            "sampled/probe interval rows",
        ],
        "priorLedgers": prior_ledgers,
        "guard": (
            "This is an interface and fail-closed ledger only.  It does not "
            "prove the interval rows, and it must not be treated as Step33A.1-A "
            "closure until the direct nonzero-model source proposition is "
            "Lean-checked or backed by proof-grade generated rows."
        ),
    }


def render_symbols(title: str, symbols: dict[str, bool]) -> list[str]:
    return ["", f"## {title}", ""] + [
        f"- `{symbol}`: `{present}`" for symbol, present in symbols.items()
    ]


def render_markdown(ledger: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Direct Scaled-Remainder Payload Ledger",
        "",
        f"schema: `{ledger['schema']}`",
        f"route: `{ledger['route']}`",
        f"proofStatus: `{ledger['proofStatus']}`",
        "",
        "## Status",
        "",
        f"- proofGrade: `{ledger['proofGrade']}`",
        f"- directPayloadSurfacePresent: `{ledger['directPayloadSurfacePresent']}`",
        f"- zeroModelBridgePresent: `{ledger['zeroModelBridgePresent']}`",
        f"- intervalPayloadSurfacePresent: `{ledger['intervalPayloadSurfacePresent']}`",
        f"- remainderBridgePresent: `{ledger['remainderBridgePresent']}`",
        f"- p45FullTaylorBridgePresent: `{ledger['p45FullTaylorBridgePresent']}`",
        "- order16NonzeroModelBridgePresent: "
        f"`{ledger['order16NonzeroModelBridgePresent']}`",
        "- directIntervalPayloadPresent: "
        f"`{ledger['directIntervalPayloadPresent']}`",
        f"- directModelPayloadPresent: `{ledger['directModelPayloadPresent']}`",
        f"- directHornerReceiverPresent: `{ledger['directHornerReceiverPresent']}`",
        f"- directHornerSmokePresent: `{ledger['directHornerSmokePresent']}`",
        f"- directSourceBridgePresent: `{ledger['directSourceBridgePresent']}`",
        "- directHornerSourceBridgePresent: "
        f"`{ledger['directHornerSourceBridgePresent']}`",
        "- directCollapsedTaylorSourcePresent: "
        f"`{ledger['directCollapsedTaylorSourcePresent']}`",
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
        f"- biasedSourceHornerPresent: `{ledger['biasedSourceHornerPresent']}`",
        "- biasedResidualSourceSegmentPresent: "
        f"`{ledger['biasedResidualSourceSegmentPresent']}`",
        "- biasedSignedFactorAdapterPresent: "
        f"`{ledger['biasedSignedFactorAdapterPresent']}`",
        "- viaBiasedResidualBridgePresent: "
        f"`{ledger['viaBiasedResidualBridgePresent']}`",
        "- directNonzeroModelIntervalRowsLeanChecked: "
        f"`{ledger['directNonzeroModelIntervalRowsLeanChecked']}`",
        "- directNonzeroModelSourcePropLeanChecked: "
        f"`{ledger['directNonzeroModelSourcePropLeanChecked']}`",
        f"- directHornerRowsLeanChecked: `{ledger['directHornerRowsLeanChecked']}`",
        "- zeroModelPayloadTargetLeanChecked: "
        f"`{ledger['zeroModelPayloadTargetLeanChecked']}`",
        f"- step33A1ClosedClaimed: `{ledger['step33A1ClosedClaimed']}`",
        f"- doNotSplitSummands: `{ledger['doNotSplitSummands']}`",
        "- doNotUseIndependentSummandBudgets: "
        f"`{ledger['doNotUseIndependentSummandBudgets']}`",
        f"- rowWorklistEmitted: `{ledger['rowWorklistEmitted']}`",
        f"- rowWorklistFile: `{ledger['rowWorklistFile']}`",
        f"- rowSourceAuditEmitted: `{ledger['rowSourceAuditEmitted']}`",
        f"- rowSourceAuditFile: `{ledger['rowSourceAuditFile']}`",
        "- rowSourceAuditMarkdownFile: "
        f"`{ledger['rowSourceAuditMarkdownFile']}`",
        f"- firstMissingProofObject: `{ledger['firstMissingProofObject']}`",
        f"- firstRowFailureCode: `{ledger['firstRowFailureCode']}`",
        "- firstConcreteUpstreamFailureCode: "
        f"`{ledger['firstConcreteUpstreamFailureCode']}`",
        "",
        "## Current Gap",
        "",
        f"`{ledger['currentGap']}`",
        "",
        "Parent gap:",
        "",
        f"`{ledger['parentGap']}`",
        "",
        "First failure code if the direct route fails:",
        "",
        f"`{ledger['firstFailureCode']}`",
        "",
        "First row-source failure code if the row generator fails:",
        "",
        f"`{ledger['firstRowFailureCode']}`",
        "",
        "Bias-shift bridge failure code if the adapter breaks:",
        "",
        f"`{ledger['biasShiftFailureCode']}`",
        "",
        "Bias-shift budget failure code for the current direct budget:",
        "",
        f"`{ledger['biasShiftBudgetFailureCode']}`",
        "",
        "P45/full-Taylor reuse verdict:",
        "",
        f"`{ledger['p45FullTaylorReuseVerdict']}`",
        "",
        "P45/full-Taylor reuse failure code:",
        "",
        f"`{ledger['p45FullTaylorReuseFailureCode']}`",
        "",
        "## Target",
        "",
        f"- expression: `{ledger['targetExpression']}`",
        f"- budget: `{ledger['targetBudget']}`",
        f"- prop: `{ledger['targetProp']}`",
        f"- payload: `{ledger['targetPayload']}`",
        f"- first interval theorem: `{ledger['firstGeneratedIntervalTheorem']}`",
        f"- first source-prop theorem: `{ledger['firstGeneratedSourcePropTheorem']}`",
        "",
        "## Route Review",
        "",
        f"- decision: `{ledger['proshkaRouteReviewDecision']}`",
        f"- question: {ledger['proshkaRouteReviewQuestion']}",
        f"- answer: {ledger['proshkaRouteReviewAnswer']}",
        f"- row worklist decision: `{ledger['proshkaRowWorklistDecision']}`",
        f"- row worklist answer: {ledger['proshkaRowWorklistAnswer']}",
        "",
        "## Direct Horner Row Route Review",
        "",
        f"- used: `{ledger['directHornerRowRouteReview']['used']}`",
        "- destination: "
        f"`{ledger['directHornerRowRouteReview']['destination']}`",
        "- recommended option: "
        f"`{ledger['directHornerRowRouteReview']['recommendedOption']}`",
        f"- decision: `{ledger['directHornerRowRouteReview']['decision']}`",
        "- first file to edit: "
        f"`{ledger['directHornerRowRouteReview']['firstFileToEdit']}`",
        "- first Lean file when rows pass: "
        f"`{ledger['directHornerRowRouteReview']['firstLeanFileToCreateWhenRowsPass']}`",
        f"- first object: `{ledger['directHornerRowRouteReview']['firstObject']}`",
        f"- valid theorem: `{ledger['directHornerRowRouteReview']['validTheorem']}`",
        f"- final theorem: `{ledger['directHornerRowRouteReview']['finalTheorem']}`",
        f"- theorem shape: {ledger['directHornerRowRouteReview']['theoremShape']}",
        "- failure code if fails: "
        f"`{ledger['directHornerRowRouteReview']['failureCodeIfFails']}`",
        "- proof claim allowed now: "
        f"`{ledger['directHornerRowRouteReview']['proofClaimAllowedNow']}`",
        f"- reason: {ledger['directHornerRowRouteReview']['reason']}",
        "",
        "Required rows:",
        "",
    ]
    lines.extend(
        f"- {item}" for item in ledger["directHornerRowRouteReview"]["requiredRows"]
    )
    collapsed_taylor_review = ledger["directCollapsedTaylorReceiverReview"]
    lines.extend(
        [
            "",
            "## Direct Collapsed Taylor Receiver Review",
            "",
            f"- used: `{collapsed_taylor_review['used']}`",
            f"- destination: `{collapsed_taylor_review['destination']}`",
            "- recommended option: "
            f"`{collapsed_taylor_review['recommendedOption']}`",
            f"- file: `{collapsed_taylor_review['file']}`",
            f"- present: `{collapsed_taylor_review['present']}`",
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
            "- preferred poly-deriv theorem: "
            f"`{collapsed_taylor_review['preferredPolyDerivTheorem']}`",
            "- preferred low-degree theorem: "
            f"`{collapsed_taylor_review['preferredLowDegreeTheorem']}`",
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
    lines.extend(
        f"- {item}" for item in collapsed_taylor_review["firstMissingRows"]
    )
    lines.extend(["", "Hidden mismatches to guard:", ""])
    lines.extend(
        f"- {item}" for item in collapsed_taylor_review["hiddenMismatchesToGuard"]
    )
    split_identity = ledger["directSplitIdentity"]
    split_policy = ledger["splitSummandsPolicy"]
    lines.extend(
        [
        "",
        "## Direct Split Identity",
        "",
        f"- theorem: `{split_identity['theorem']}`",
        f"- file: `{split_identity['file']}`",
        f"- present: `{split_identity['present']}`",
        f"- leftHandSide: `{split_identity['leftHandSide']}`",
        f"- rightHandSide: `{split_identity['rightHandSide']}`",
        "- collapsedWholeExpressionRhs: "
        f"`{split_identity['collapsedWholeExpressionRhs']}`",
        f"- receiverField: `{split_identity['receiverField']}`",
        "- usableAsRowSourceCrosswalk: "
        f"`{split_identity['usableAsRowSourceCrosswalk']}`",
        f"- proofGradeRowsPresent: `{split_identity['proofGradeRowsPresent']}`",
        f"- budgetSpendAllowed: `{split_identity['budgetSpendAllowed']}`",
        f"- guard: {split_identity['guard']}",
        "",
        "## Split Summands Policy",
        "",
        "- algebraicSplitAllowedForRowSource: "
        f"`{split_policy['algebraicSplitAllowedForRowSource']}`",
        "- independentNormSpendAllowed: "
        f"`{split_policy['independentNormSpendAllowed']}`",
        "- finalReceiverTargetMustBeWholeExpression: "
        f"`{split_policy['finalReceiverTargetMustBeWholeExpression']}`",
        f"- proshkaFollowupDecision: `{split_policy['proshkaFollowupDecision']}`",
        "- oneCoefficientStreamRequired: "
        f"`{split_policy['oneCoefficientStreamRequired']}`",
        f"- reason: {split_policy['reason']}",
        "",
        "## Direct Whole-Expression Row Review",
        "",
        "- recommended option: "
        f"`{ledger['directWholeExpressionRowReview']['recommendedOption']}`",
        "- decision: "
        f"`{ledger['directWholeExpressionRowReview']['decision']}`",
        "- first file to edit: "
        f"`{ledger['directWholeExpressionRowReview']['firstFileToEdit']}`",
        "- first Lean file when rows pass: "
        f"`{ledger['directWholeExpressionRowReview']['firstLeanFileToCreateWhenRowsPass']}`",
        f"- first object: `{ledger['directWholeExpressionRowReview']['firstObject']}`",
        f"- row theorem: `{ledger['directWholeExpressionRowReview']['rowTheorem']}`",
        "- row theorem shape: "
        f"{ledger['directWholeExpressionRowReview']['rowTheoremShape']}",
        "- collapsed expression: "
        f"`{ledger['directWholeExpressionRowReview']['collapsedExpression']}`",
        "- failure code if fails: "
        f"`{ledger['directWholeExpressionRowReview']['failureCodeIfFails']}`",
        "- proof claim allowed now: "
        f"`{ledger['directWholeExpressionRowReview']['proofClaimAllowedNow']}`",
        "",
        "Required rows:",
        "",
        ]
    )
    lines.extend(
        f"- {item}"
        for item in ledger["directWholeExpressionRowReview"]["requiredRows"]
    )
    lines.extend(["", "Do not produce:", ""])
    lines.extend(
        f"- {item}" for item in ledger["directWholeExpressionRowReview"]["doNotProduce"]
    )
    impl_review = ledger["directRowSourceImplementationReview"]
    missing_theorem = impl_review["missingRemainderTheorem"]
    exact_coeff = impl_review["exactCoefficientSource"]
    lines.extend(
        [
            "",
            "## Direct Row-Source Implementation Review",
            "",
            f"- usedComputerUse: `{impl_review['usedComputerUse']}`",
            f"- advisoryOnly: `{impl_review['advisoryOnly']}`",
            f"- recommended option: `{impl_review['recommendedOption']}`",
            f"- decision label: `{impl_review['decisionLabel']}`",
            f"- first file to create: `{impl_review['firstFileToCreate']}`",
            f"- audit object: `{impl_review['auditObject']}`",
            "- audit object is Lean theorem: "
            f"`{impl_review['auditObjectIsLeanTheorem']}`",
            "- first Lean payload when rows exist: "
            f"`{impl_review['firstLeanPayloadWhenRowsExist']}`",
            "- first Lean data object when rows exist: "
            f"`{impl_review['firstLeanDataObjectWhenRowsExist']}`",
            "- first Lean validity theorem when rows exist: "
            f"`{impl_review['firstLeanValidityTheoremWhenRowsExist']}`",
            f"- coefficient source status: `{exact_coeff['status']}`",
            f"- partial bridge file: `{exact_coeff['partialBridgeFile']}`",
            f"- partial bridge theorem: `{exact_coeff['partialBridgeTheorem']}`",
            f"- missing theorem: `{missing_theorem['name']}`",
            "- failure code if rows missing: "
            f"`{impl_review['failureCodeIfRowsMissing']}`",
            "- proof claim allowed now: "
            f"`{impl_review['proofClaimAllowedNow']}`",
            f"- step33A1ClosedClaimed: `{impl_review['step33A1ClosedClaimed']}`",
            "",
            "Decision:",
            "",
            impl_review["decision"],
            "",
            "Coefficient-source notes:",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in exact_coeff["notes"])
    lines.extend(["", "Missing theorem statement:", "", "```lean"])
    lines.extend(missing_theorem["statement"])
    lines.extend(
        [
            "```",
            "",
            "## Active-Actual Remainder Adapter",
            "",
            "- file: "
            f"`{ledger['activeActualRemainderBridgeFile']}`",
            "- present: "
            f"`{ledger['activeActualRemainderBridgePresent']}`",
            "- Lean checked this run: "
            f"`{ledger['activeActualRemainderBridgeLeanChecked']}`",
            "- closed subgap: "
            "`STEP33_A1_SUB0_COMBINED_ORDER16_ACTIVE_ACTUAL_NOMINAL_POLY_ALIGNMENT_CLOSED`",
            "- next missing theorem: "
            f"`{ledger['nextProofProducingPatch']['activeActualMissingRemainderTheorem']}`",
            "- next failure code if rows are still missing: "
            f"`{ledger['nextProofProducingPatch']['failureCodeIfRowsStillMissing']}`",
            "",
            "Meaning: a future proof-grade scaled-active-actual segment "
            "approximation can be transported to the collapsed-expression "
            "remainder row by subtracting `nominalOrder16Poly` inside the same "
            "coefficient stream.  This is not a row certificate and does not "
            "close Step33A.1-A.",
            "",
            "## Active-Actual Horner Segment Receiver",
            "",
            "- file: "
            f"`{ledger['activeActualHornerSegmentFile']}`",
            "- present: "
            f"`{ledger['activeActualHornerSegmentReceiverPresent']}`",
            "- Lean checked this run: "
            f"`{ledger['activeActualHornerSegmentReceiverLeanChecked']}`",
            "- conditional activeActual theorem: "
            f"`{ledger['nextProofProducingPatch']['activeActualHornerReceiverTheorem']}`",
            "- collapsed receiver theorem: "
            f"`{ledger['nextProofProducingPatch']['activeActualCollapsedHornerTheorem']}`",
            "- next failure code if rows are still missing: "
            f"`{ledger['nextProofProducingPatch']['failureCodeIfRowsStillMissing']}`",
            "",
            "Meaning: a future proof-grade activeActual Horner row can now feed "
            "the checked activeActual/nominal adapter.  This receiver is "
            "conditional and supplies no concrete coefficients or interval row "
            "data.",
            "",
            "## Active-Actual Horner Family Bridge",
            "",
            "- file: "
            f"`{ledger['activeActualHornerFamilyBridgeFile']}`",
            "- present: "
            f"`{ledger['activeActualHornerFamilyBridgePresent']}`",
            "- Lean checked this run: "
            f"`{ledger['activeActualHornerFamilyBridgeLeanChecked']}`",
            "- conditional family theorem: "
            f"`{ledger['nextProofProducingPatch']['activeActualHornerFamilyTheorem']}`",
            "- conditional payload theorem: "
            f"`{ledger['nextProofProducingPatch']['activeActualHornerFamilyPayloadTheorem']}`",
            "- next failure code if rows are still missing: "
            f"`{ledger['nextProofProducingPatch']['failureCodeIfRowsStillMissing']}`",
            "- failure code if this bridge breaks: "
            f"`{ledger['nextProofProducingPatch']['failureCodeIfFamilyBridgeMissing']}`",
            "",
            "Meaning: valid activeActual Horner segment rows can now be packaged "
            "as the existing DirectHorner family receiver expects.  This is a "
            "conditional bridge only; the activeActual segment rows, Horner "
            "range rows, cover rows, and budget rows are still missing.",
            "",
            "## Active-Actual Horner Row-Source Ledger",
            "",
            "- file: "
            f"`{ledger['activeActualHornerRowSourceLedgerFile']}`",
            "- exists: "
            f"`{ledger['activeActualHornerRowSourceLedger']['exists']}`",
            "- schema: "
            f"`{ledger['activeActualHornerRowSourceLedger']['schema']}`",
            "- proofStatus: "
            f"`{ledger['activeActualHornerRowSourceLedger']['proofStatus']}`",
            "- proofGrade: "
            f"`{ledger['activeActualHornerRowSourceLedger']['proofGrade']}`",
            "- proofSafeClosedFields: "
            f"`{ledger['activeActualHornerRowSourceLedger']['proofSafeClosedFields']}`",
            "- outLeanWritten: "
            f"`{ledger['activeActualHornerRowSourceLedger']['outLeanWritten']}`",
            "- firstFailureCode: "
            f"`{ledger['activeActualHornerRowSourceLedger']['firstFailureCode']}`",
            "",
            "Meaning: this is the fail-closed generator contract selected by "
            "Computer Use / Proshka.  It records the exact segment/family/range/"
            "budget rows required before any activeActual Horner payload may be "
            "written; it is not a proof object.",
            "",
            "Minimal row data:",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in impl_review["minimalRowData"])
    lines.extend(["", "Do not reuse:", ""])
    lines.extend(f"- {item}" for item in impl_review["whatMustNotBeReused"])
    lines.extend(
        [
            "",
            "Route options rejected:",
            "",
            "- why no DirectConcretePayload yet: "
            f"{impl_review['whyNotDirectConcretePayloadYet']}",
            f"- whyNotB: {impl_review['whyNotB']}",
            f"- whyNotD: {impl_review['whyNotD']}",
        ]
    )
    reuse_review = ledger["biasedResidualReuseReview"]
    lines.extend(
        [
            "",
            "## Biased Residual Reuse Review",
            "",
            f"- reuse: `{reuse_review['reuse']}`",
            f"- decision: `{reuse_review['decision']}`",
            f"- current budget verdict: `{reuse_review['currentBudgetVerdict']}`",
            f"- bridge file: `{reuse_review['bridgeFile']}`",
            f"- source segment file: `{reuse_review['sourceSegmentFile']}`",
            f"- Lean bridge checked: `{reuse_review['leanBridgeChecked']}`",
            f"- first generator patch: `{reuse_review['firstGeneratorPatch']}`",
            f"- first Lean payload file: `{reuse_review['firstLeanPayloadFile']}`",
            "- first missing proof-grade row: "
            f"`{reuse_review['firstMissingProofGradeRow']}`",
            "- failure code if bridge missing: "
            f"`{reuse_review['failureCodeIfBridgeMissing']}`",
            "- failure code if rows missing: "
            f"`{reuse_review['failureCodeIfRowsMissing']}`",
            "- failure code if budget fails: "
            f"`{reuse_review['failureCodeIfBudgetFails']}`",
            f"- budget kill theorem: `{reuse_review['budgetKillTheorem']}`",
            f"- proof claim allowed now: `{reuse_review['proofClaimAllowedNow']}`",
            f"- warning: {reuse_review['warning']}",
            "",
            "Required rows:",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in reuse_review["requiredRows"])
    lines.extend(
        [
        "",
        "## Post-Budget-Kill Route Review",
        "",
        f"- decision: `{ledger['proshkaPostBudgetKillDecision']}`",
        f"- context: {ledger['proshkaPostBudgetKillContext']}",
        f"- answer: {ledger['proshkaPostBudgetKillAnswer']}",
        f"- killed factor route: `{ledger['postBudgetKillFailureCode']}`",
        "",
        "## Active-Actual Degree0 Direct-Budget Kill",
        "",
        "- decision: "
        f"`{ledger['latestComputerUseDegree0BudgetKillReview']['recommendedOption']}`",
        "- first theorem target: "
        f"`{ledger['latestComputerUseDegree0BudgetKillReview']['firstTheoremTarget']}`",
        "- audit file: "
        f"`{ledger['latestComputerUseDegree0BudgetKillReview']['activeActualDegree0AuditFile']}`",
        "- budget kill theorem: "
        f"`{ledger['latestComputerUseDegree0BudgetKillReview']['budgetKillTheorem']}`",
        "- failure code if budget false: "
        f"`{ledger['latestComputerUseDegree0BudgetKillReview']['failureCodeIfBudgetFalse']}`",
        "- proof claim allowed now: "
        f"`{ledger['latestComputerUseDegree0BudgetKillReview']['proofClaimAllowedNow']}`",
        "",
        "## Next Proof-Producing Patch",
        "",
        f"- generator: `{ledger['nextProofProducingPatch']['generator']}`",
        f"- Lean file: `{ledger['nextProofProducingPatch']['leanFile']}`",
        f"- theorem: `{ledger['nextProofProducingPatch']['theorem']}`",
        "- missing remainder theorem: "
        f"`{ledger['nextProofProducingPatch']['missingRemainderTheorem']}`",
        "- collapsed Taylor receiver file: "
        f"`{ledger['nextProofProducingPatch']['collapsedTaylorReceiverFile']}`",
        "- collapsed Taylor receiver theorem: "
        f"`{ledger['nextProofProducingPatch']['collapsedTaylorReceiverTheorem']}`",
        "- source-prop theorem: "
        f"`{ledger['nextProofProducingPatch']['sourcePropTheorem']}`",
        "- failure code if rows still missing: "
        f"`{ledger['nextProofProducingPatch']['failureCodeIfRowsStillMissing']}`",
        "- parent failure code if rows still missing: "
        f"`{ledger['nextProofProducingPatch']['parentFailureCodeIfRowsStillMissing']}`",
        "- failure code if collapsed Taylor receiver fails: "
        f"`{ledger['nextProofProducingPatch']['failureCodeIfCollapsedTaylorReceiverFails']}`",
        "- proof claim allowed now: "
        f"`{ledger['nextProofProducingPatch']['proofClaimAllowedNow']}`",
        "",
        "Next implementable patch:",
        "",
        str(ledger["nextImplementablePatch"]),
        "",
        "## Why P45/full-Taylor Is Not Enough",
        "",
        str(ledger["whyP45FullTaylorIsNotEnough"]),
        "",
        "## Theorem Shape",
        "",
        str(ledger["theoremShape"]),
        "",
        "## Certificate Shape",
        "",
    ]
    )
    lines.extend(f"- {item}" for item in ledger["certificateShape"])
    lines.extend(["", "## Do Not Reuse After Post-Budget-Kill", ""])
    lines.extend(f"- {item}" for item in ledger["doNotReuseAfterPostBudgetKill"])
    lines.extend(["", "## Row Obligations", ""])
    for row in ledger["rowObligations"]:
        lines.append(f"### {row['id']}")
        lines.append("")
        for key, value in row.items():
            if key == "id":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Candidate Reuse Routes", ""])
    for route in ledger["candidateReuseRoutes"]:
        lines.append(f"### {route['route']}")
        lines.append("")
        for key, value in route.items():
            if key == "route":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Source Availability Audit", ""])
    for item in ledger["sourceAvailabilityAudit"]:
        lines.append(f"### {item['source']}")
        lines.append("")
        for key, value in item.items():
            if key == "source":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    audit = ledger["upstreamRowSourceAudit"]
    lines.extend(["## Upstream Row-Source Audit", ""])
    lines.extend(
        [
            f"- directFailureCode: `{audit['directFailureCode']}`",
            "- firstConcreteUpstreamFailureCode: "
            f"`{audit['firstConcreteUpstreamFailureCode']}`",
            "- componentTaylorRemainderGapActive: "
            f"`{audit['componentTaylorRemainderGapActive']}`",
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
    lines.append("")
    lines.extend(render_symbols("Direct Payload Symbols", ledger["directPayloadSymbols"]))
    lines.extend(render_symbols("Zero Model Symbols", ledger["zeroModelSymbols"]))
    lines.extend(render_symbols("Interval Payload Symbols", ledger["intervalPayloadSymbols"]))
    lines.extend(render_symbols("Remainder Bridge Symbols", ledger["remainderBridgeSymbols"]))
    lines.extend(
        render_symbols(
            "P45/full-Taylor Bridge Symbols", ledger["p45FullTaylorBridgeSymbols"]
        )
    )
    lines.extend(
        render_symbols(
            "Order16 Nonzero-Model Symbols", ledger["order16NonzeroModelSymbols"]
        )
    )
    lines.extend(
        render_symbols(
            "Direct Interval Payload Symbols", ledger["directIntervalPayloadSymbols"]
        )
    )
    lines.extend(
        render_symbols("Direct Model Payload Symbols", ledger["directModelPayloadSymbols"])
    )
    lines.extend(
        render_symbols("Direct Horner Symbols", ledger["directHornerSymbols"])
    )
    lines.extend(
        render_symbols("Direct Horner Smoke Symbols", ledger["directHornerSmokeSymbols"])
    )
    lines.extend(
        render_symbols("Direct Source Bridge Symbols", ledger["directSourceBridgeSymbols"])
    )
    lines.extend(
        render_symbols(
            "Direct Horner Source Bridge Symbols",
            ledger["directHornerSourceBridgeSymbols"],
        )
    )
    lines.extend(
        render_symbols(
            "Direct Collapsed Taylor Source Symbols",
            ledger["directCollapsedTaylorSourceSymbols"],
        )
    )
    lines.extend(
        render_symbols(
            "Active-Actual Horner Segment Symbols",
            ledger["activeActualHornerSegmentSymbols"],
        )
    )
    lines.extend(
        render_symbols(
            "Active-Actual Horner Family Bridge Symbols",
            ledger["activeActualHornerFamilyBridgeSymbols"],
        )
    )
    lines.extend(
        render_symbols("Biased Source Horner Symbols", ledger["biasedSourceHornerSymbols"])
    )
    lines.extend(
        render_symbols(
            "Biased Residual Source Segment Symbols",
            ledger["biasedResidualSourceSegmentSymbols"],
        )
    )
    lines.extend(
        render_symbols(
            "Biased Signed-Factor Adapter Symbols",
            ledger["biasedSignedFactorAdapterSymbols"],
        )
    )
    lines.extend(
        render_symbols(
            "Via Biased Residual Bridge Symbols",
            ledger["viaBiasedResidualSymbols"],
        )
    )
    lines.extend(["", "## Prior Ledgers", ""])
    for name, summary in ledger["priorLedgers"].items():
        lines.append(f"### {name}")
        lines.append("")
        for key, value in summary.items():
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Guard", "", str(ledger["guard"]), ""])
    return "\n".join(lines)


def render_row_source_audit_markdown(ledger: dict[str, Any]) -> str:
    review = ledger["directRowSourceImplementationReview"]
    coeff = review["exactCoefficientSource"]
    missing = review["missingRemainderTheorem"]
    preferred = ledger["preferredCollapsedLowDegreeRowSourceContract"]
    lines = [
        "# Step33A.1-A Direct Row-Source Audit",
        "",
        f"schema: `{SCHEMA}.row_source_audit`",
        f"route: `{ledger['route']}`",
        f"proofGrade: `{ledger['proofGrade']}`",
        f"currentGap: `{ledger['currentGap']}`",
        f"firstRowFailureCode: `{ledger['firstRowFailureCode']}`",
        "",
        "## Verdict",
        "",
        f"- recommended option: `{review['recommendedOption']}`",
        f"- decision label: `{review['decisionLabel']}`",
        f"- first file to create: `{review['firstFileToCreate']}`",
        f"- proof claim allowed now: `{review['proofClaimAllowedNow']}`",
        f"- step33A1ClosedClaimed: `{review['step33A1ClosedClaimed']}`",
        f"- audit object: `{review['auditObject']}`",
        f"- audit object is Lean theorem: `{review['auditObjectIsLeanTheorem']}`",
        "",
        review["decision"],
        "",
        "## Target",
        "",
        f"- expression: `{ledger['targetExpression']}`",
        f"- budget: `{ledger['targetBudget']}`",
        f"- target prop: `{ledger['targetProp']}`",
        f"- first interval theorem: `{ledger['firstGeneratedIntervalTheorem']}`",
        f"- direct source bridge present: `{ledger['directSourceBridgePresent']}`",
        f"- direct source bridge file: `{ledger['directSourceBridgeFile']}`",
        "",
        "## Exact Coefficient Source",
        "",
        f"- status: `{coeff['status']}`",
        f"- partial bridge file: `{coeff['partialBridgeFile']}`",
        f"- partial bridge theorem: `{coeff['partialBridgeTheorem']}`",
        "",
    ]
    lines.extend(f"- {note}" for note in coeff["notes"])
    lines.extend(
        [
            "",
            "## Missing Remainder Theorem",
            "",
            f"- name: `{missing['name']}`",
            "",
            "```lean",
        ]
    )
    lines.extend(missing["statement"])
    lines.extend(["```", "", "## Minimal Row Data", ""])
    lines.extend(f"- {item}" for item in review["minimalRowData"])
    lines.extend(["", "## Do Not Reuse", ""])
    lines.extend(f"- {item}" for item in review["whatMustNotBeReused"])
    lines.extend(
        [
            "",
            "## Preferred Collapsed Low-Degree Row-Source Contract",
            "",
            f"- choice: `{preferred['choice']}`",
            f"- source: `{preferred['source']}`",
            f"- status: `{preferred['status']}`",
            f"- proofGrade: `{preferred['proofGrade']}`",
            f"- generator to patch: `{preferred['generatorToPatch']}`",
            "- Lean file to emit only when rows pass: "
            f"`{preferred['leanFileToEmitOnlyWhenRowsPass']}`",
            "- final theorem when rows pass: "
            f"`{preferred['finalTheoremWhenRowsPass']}`",
            "- row theorem when rows pass: "
            f"`{preferred['rowTheoremWhenRowsPass']}`",
            "- first failure if rows are missing: "
            f"`{preferred['firstFailureCodeIfRowsMissing']}`",
            "- parent failure if rows are missing: "
            f"`{preferred['parentFailureCodeIfRowsMissing']}`",
            "- budget failure code: "
            f"`{preferred['budgetFailureCode']}`",
            "",
            preferred["reason"],
            "",
            "### Receiver Chain",
            "",
        ]
    )
    for receiver in preferred["receiverChain"]:
        lines.append(f"- `{receiver['status']}`: `{receiver['theorem']}`")
        lines.append(f"  file: `{receiver['file']}`")
        lines.append(
            f"  failureCodeIfMissing: `{receiver['failureCodeIfMissing']}`"
        )
    lines.extend(["", "### Required Exact Rows Before Lean Emission", ""])
    for row in preferred["requiredExactRowsBeforeLeanEmission"]:
        lines.append(f"- `{row['id']}`: `{row['status']}`")
        lines.append(f"  object: `{row['object']}`")
        lines.append(f"  failureCode: `{row['failureCode']}`")
    lines.extend(["", "### Contract Do Not Use", ""])
    lines.extend(f"- {item}" for item in preferred["doNotUse"])
    lines.extend(
        [
            "",
            "## Route Options",
            "",
            "- why no DirectConcretePayload yet: "
            f"{review['whyNotDirectConcretePayloadYet']}",
            f"- whyNotB: {review['whyNotB']}",
            f"- whyNotD: {review['whyNotD']}",
            "",
            "## Active-Actual Horner Row-Source Ledger",
            "",
        ]
    )
    for key, value in ledger["activeActualHornerRowSourceLedger"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Source Availability Audit",
            "",
        ]
    )
    for item in ledger["sourceAvailabilityAudit"]:
        lines.append(f"### {item['source']}")
        lines.append("")
        for key, value in item.items():
            if key == "source":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Row Obligations", ""])
    for row in ledger["rowObligations"]:
        lines.append(f"### {row['id']}")
        lines.append("")
        for key, value in row.items():
            if key == "id":
                continue
            lines.append(f"- `{key}`: `{value}`")
        lines.append("")
    lines.extend(["## Guard", "", ledger["guard"], ""])
    return "\n".join(lines)


def main() -> None:
    ledger = build_ledger()
    REQUEST_DIR.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")
    ROW_OBLIGATIONS_JSON_OUT.write_text(
        json.dumps(
            {
                "schema": f"{SCHEMA}.row_obligations",
                "generatedAt": ledger["generatedAt"],
                "route": ledger["route"],
                "currentGap": ledger["currentGap"],
                "firstRowFailureCode": ledger["firstRowFailureCode"],
                "rowSourceAuditEmitted": ledger["rowSourceAuditEmitted"],
                "rowSourceAuditFile": ledger["rowSourceAuditFile"],
                "rowSourceAuditMarkdownFile": ledger[
                    "rowSourceAuditMarkdownFile"
                ],
                "firstConcreteUpstreamFailureCode": ledger[
                    "firstConcreteUpstreamFailureCode"
                ],
                "firstMissingProofObject": ledger["firstMissingProofObject"],
                "targetExpression": ledger["targetExpression"],
                "targetBudget": ledger["targetBudget"],
                "directSplitIdentity": ledger["directSplitIdentity"],
                "splitSummandsPolicy": ledger["splitSummandsPolicy"],
                "directWholeExpressionRowReview": ledger[
                    "directWholeExpressionRowReview"
                ],
                "preferredCollapsedLowDegreeRowSourceContract": ledger[
                    "preferredCollapsedLowDegreeRowSourceContract"
                ],
                "doNotUseIndependentSummandBudgets": ledger[
                    "doNotUseIndependentSummandBudgets"
                ],
                "proshkaPostBudgetKillDecision": ledger[
                    "proshkaPostBudgetKillDecision"
                ],
                "postBudgetKillFailureCode": ledger["postBudgetKillFailureCode"],
                "latestComputerUseDegree0BudgetKillReview": ledger[
                    "latestComputerUseDegree0BudgetKillReview"
                ],
                "directHornerRowRouteReview": ledger["directHornerRowRouteReview"],
                "directRowSourceImplementationReview": ledger[
                    "directRowSourceImplementationReview"
                ],
                "preferredCollapsedLowDegreeRowSourceContract": ledger[
                    "preferredCollapsedLowDegreeRowSourceContract"
                ],
                "nextImplementablePatch": ledger["nextImplementablePatch"],
                "nextProofProducingPatch": ledger["nextProofProducingPatch"],
                "activeActualHornerRowSourceLedger": ledger[
                    "activeActualHornerRowSourceLedger"
                ],
                "upstreamProofProducingPatch": ledger["upstreamProofProducingPatch"],
                "rowObligations": ledger["rowObligations"],
                "candidateReuseRoutes": ledger["candidateReuseRoutes"],
                "sourceAvailabilityAudit": ledger["sourceAvailabilityAudit"],
                "upstreamRowSourceAudit": ledger["upstreamRowSourceAudit"],
                "doNotReuseAfterPostBudgetKill": ledger[
                    "doNotReuseAfterPostBudgetKill"
                ],
                "guard": ledger["guard"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    ROW_SOURCE_AUDIT_JSON_OUT.write_text(
        json.dumps(
            {
                "schema": f"{SCHEMA}.row_source_audit",
                "generatedAt": ledger["generatedAt"],
                "route": ledger["route"],
                "proofGrade": ledger["proofGrade"],
                "currentGap": ledger["currentGap"],
                "firstRowFailureCode": ledger["firstRowFailureCode"],
                "targetExpression": ledger["targetExpression"],
                "targetBudget": ledger["targetBudget"],
                "targetProp": ledger["targetProp"],
                "directSourceBridgePresent": ledger["directSourceBridgePresent"],
                "directSourceBridgeFile": ledger["directSourceBridgeFile"],
                "directSourceBridgeSymbols": ledger["directSourceBridgeSymbols"],
                "directRowSourceImplementationReview": ledger[
                    "directRowSourceImplementationReview"
                ],
                "preferredCollapsedLowDegreeRowSourceContract": ledger[
                    "preferredCollapsedLowDegreeRowSourceContract"
                ],
                "activeActualHornerRowSourceLedger": ledger[
                    "activeActualHornerRowSourceLedger"
                ],
                "sourceAvailabilityAudit": ledger["sourceAvailabilityAudit"],
                "rowObligations": ledger["rowObligations"],
                "doNotReuseAfterPostBudgetKill": ledger[
                    "doNotReuseAfterPostBudgetKill"
                ],
                "guard": ledger["guard"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    MD_OUT.write_text(render_markdown(ledger), encoding="utf-8")
    ROW_SOURCE_AUDIT_MD_OUT.write_text(
        render_row_source_audit_markdown(ledger), encoding="utf-8"
    )
    print(ledger["proofStatus"])
    print(ledger["firstFailureCode"])
    print(ledger["firstRowFailureCode"])
    print(ledger["currentGap"])
    print(ledger["p45FullTaylorReuseVerdict"])


if __name__ == "__main__":
    main()
