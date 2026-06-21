#!/usr/bin/env python3
"""Fail-closed cancellation-preserving residual interval certificate ledger.

This generator records the exact local Lean surface for the Step33A.1-A
first-subchunk route-A interval gate.  It extracts the generated derivative
model coefficients from the checked HRaw landing file and emits a self-contained
JSON/Markdown ledger for the missing proof:

    raw derivative closed form - full Taylor derivative model

on [0, 1/10].

The output is deliberately not Lean proof data.  It closes only the
coefficient-extraction bookkeeping and fails closed until component Taylor
bounds, exact residual assembly, and an interval/rational residual range proof
are available.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
LANDING_FILE = ROOT / "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean"
SEGMENTED_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_segmented_residual_deriv_interval_payload.json"
)
COMPONENT_PAYLOAD = (
    REQUEST_DIR / "step33_a1_sub0_component_taylor_residual_payload.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR / "step33_a1_sub0_cancellation_residual_interval_certificate.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR / "step33_a1_sub0_cancellation_residual_interval_certificate.md"
)

SCHEMA = "q3_psdpd_step33_a1_sub0_cancellation_residual_interval_certificate.v2"
ROUTE_ID = "STEP33_A1_SUB0_CANCELLATION_RESIDUAL_INTERVAL"
STATUS = "fail_closed_missing_component_taylor_remainder_bounds"
FIRST_FAILURE = "STEP33_A1_SUB0_COMPONENT_TAYLOR_BOUNDS_MISSING"
SECOND_FAILURE = "STEP33_A1_SUB0_ASSEMBLED_RESIDUAL_RANGE_PROOF_MISSING"
NO_LEAN_PAYLOAD_FAILURE = "STEP33_A1_SUB0_CANCELLATION_INTERVAL_LEAN_PAYLOAD_MISSING"
COARSE_SHAPESQ_BUDGET_FAILURE = (
    "STEP33_A1_SUB0_SHAPESQ_COARSE_VALUE_REMAINDER_SCALE_FREE_BUDGET_FAIL"
)

COEFF_DEF = "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff"
RAW_TAYLOR_COEFF_DEF = "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeff"
RAW_TAYLOR_CERT_DEF = "primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert"
POLY_DERIV_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel"
)
RESIDUAL_CROSSWALK = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm"
)
TARGET_THEOREM = (
    "primaryFiniteRow0Parent0Split100Sub0_fullTaylor_"
    "residual_deriv_closedForm_interval"
)
DIRECT_VALID_BRIDGE = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "fullTaylor_direct_segment_cert_valid_of_residual_bounds"
)
PROOF_DATA_WRAPPER = (
    "primaryFiniteRow0Parent0Split100Sub0_"
    "fullTaylor_cellSlopeExactIntegralProofData_of_checked_"
    "hRawCenterCoeffAbs_and_residual_bounds"
)
DIRECT_SEGMENT_DATA = "primaryFiniteRow0Parent0Split100Sub0DirectResidualSegmentCert"

CELL_L = "0"
CELL_U = "1/10"
CENTER = "1/20"
RADIUS = "1/20"
TARGET_LOWER = "-94119513411/500000000000000000000000000000"
TARGET_UPPER = "1866608532757/500000000000000000000000000000"


COEFF_RE = re.compile(
    r"^\s*\|\s*(?P<idx>\d+|_)\s*=>\s*"
    r"\((?P<num>-?\d+)\s*:\s*Rat\)\s*/\s*(?P<den>\d+)\s*$"
)


def rat_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def parse_rat(text: str) -> Fraction:
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(int(text), 1)


def load_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected object root")
    return data


def file_hash(path: Path) -> str | None:
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()[:16]


def line_of_symbol(lines: list[str], symbol: str) -> int | None:
    needle = symbol
    for index, line in enumerate(lines, start=1):
        if needle in line:
            return index
    return None


def extract_coefficients(path: Path) -> tuple[list[dict[str, Any]], dict[str, int]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    start = line_of_symbol(lines, f"def {COEFF_DEF}")
    if start is None:
        raise ValueError(f"{path}: missing {COEFF_DEF}")

    coeffs: list[dict[str, Any]] = []
    end = start
    for line_no in range(start, len(lines) + 1):
        line = lines[line_no - 1]
        if line_no > start and line.startswith("def "):
            end = line_no - 1
            break
        match = COEFF_RE.match(line)
        if not match:
            continue
        idx_text = match.group("idx")
        idx = 15 if idx_text == "_" else int(idx_text)
        value = Fraction(int(match.group("num")), int(match.group("den")))
        coeffs.append(
            {
                "index": idx,
                "leanMatchIndex": idx_text,
                "value": rat_text(value),
                "sourceLine": line_no,
            }
        )
    else:
        end = len(lines)

    coeffs = sorted(coeffs, key=lambda item: item["index"])
    expected = list(range(16))
    actual = [int(item["index"]) for item in coeffs]
    if actual != expected:
        raise ValueError(f"{path}: expected coefficient indices {expected}, got {actual}")

    symbol_lines = {
        COEFF_DEF: start,
        RAW_TAYLOR_COEFF_DEF: line_of_symbol(lines, f"def {RAW_TAYLOR_COEFF_DEF}") or 0,
        RAW_TAYLOR_CERT_DEF: line_of_symbol(lines, f"def {RAW_TAYLOR_CERT_DEF}") or 0,
        POLY_DERIV_CROSSWALK: line_of_symbol(lines, f"theorem {POLY_DERIV_CROSSWALK}")
        or 0,
        RESIDUAL_CROSSWALK: line_of_symbol(lines, f"theorem {RESIDUAL_CROSSWALK}")
        or 0,
        DIRECT_SEGMENT_DATA: line_of_symbol(lines, f"def {DIRECT_SEGMENT_DATA}") or 0,
        DIRECT_VALID_BRIDGE: line_of_symbol(lines, f"theorem {DIRECT_VALID_BRIDGE}")
        or 0,
        PROOF_DATA_WRAPPER: line_of_symbol(lines, f"def {PROOF_DATA_WRAPPER}") or 0,
    }
    symbol_lines[f"{COEFF_DEF}_end"] = end
    return coeffs, symbol_lines


def raw_taylor_coefficients_from_deriv(coeffs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    raw_coeffs: list[dict[str, Any]] = [
        {
            "index": 0,
            "value": "primaryFiniteRow0Parent0Split100Sub0RawCenterCoeff0",
            "source": "Lean def primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeff",
        }
    ]
    for item in coeffs:
        idx = int(item["index"])
        value = parse_rat(str(item["value"])) / Fraction(idx + 1, 1)
        raw_coeffs.append(
            {
                "index": idx + 1,
                "value": rat_text(value),
                "source": f"{COEFF_DEF}[{idx}] / {idx + 1}",
            }
        )
    return raw_coeffs


def segmented_summary(segmented: dict[str, Any] | None) -> dict[str, Any]:
    if not segmented:
        return {
            "exists": False,
            "schema": None,
            "status": None,
            "proofSafeClosedFields": None,
            "outLeanWritten": None,
            "segmentCount": None,
            "coveragePassed": None,
            "allSegmentsBudgetPassed": None,
            "segments": [],
        }
    return {
        "exists": True,
        "schema": segmented.get("schema"),
        "status": segmented.get("status"),
        "proofSafeClosedFields": segmented.get("proofSafeClosedFields"),
        "outLeanWritten": segmented.get("outLeanWritten"),
        "segmentCount": segmented.get("segmentCount"),
        "coveragePassed": segmented.get("coveragePassed"),
        "allSegmentsBudgetPassed": segmented.get("allSegmentsBudgetPassed"),
        "segments": segmented.get("segments", []),
    }


def component_payload_audit(component: dict[str, Any] | None) -> dict[str, Any]:
    if not component:
        return {
            "exists": False,
            "schema": None,
            "status": None,
            "firstFailure": None,
            "proofSafeClosedFields": None,
            "shapeSqDerivTaylorSourcePresent": None,
            "shapeSqTaylorSourcePresent": None,
            "shapeSqValueRemainderAbs": None,
            "shapeSqDerivRemainderAbs": None,
            "targetWidth": None,
            "targetUpperAbs": None,
            "shapeSqValueRemainderToTargetWidthRatio": None,
            "shapeSqDerivRemainderToTargetWidthRatio": None,
            "scaleFreeShapeSqValueRemainderWithinTargetWidth": False,
            "scaleFreeShapeSqDerivRemainderWithinTargetWidth": False,
            "auditFailure": "STEP33_A1_SUB0_COMPONENT_PAYLOAD_MISSING",
            "interpretation": (
                "No component payload is available, so the cancellation "
                "certificate cannot audit the current component Taylor source."
            ),
        }

    proof_status = component.get("proofStatus", {})
    cell = component.get("cell", {})
    shape_sq = component.get("shapeSqTaylorSource", {})
    shape_sq_deriv = component.get("shapeSqDerivTaylorSource", {})

    target_width = parse_rat(str(cell["targetWidth"]))
    target_upper_abs = abs(parse_rat(str(cell["targetUpper"])))
    shape_sq_value_remainder = parse_rat(
        str(shape_sq["constantTaylorRemainderAbs"])
    )
    shape_sq_deriv_remainder = parse_rat(
        str(shape_sq_deriv["constantTaylorRemainderAbs"])
    )

    value_within_width = shape_sq_value_remainder <= target_width
    deriv_within_width = shape_sq_deriv_remainder <= target_width

    return {
        "exists": True,
        "schema": component.get("schema"),
        "status": component.get("status"),
        "firstFailure": component.get("firstFailure"),
        "proofSafeClosedFields": proof_status.get("proofSafeClosedFields"),
        "shapeSqDerivTaylorSourcePresent": proof_status.get(
            "shapeSqDerivTaylorSourcePresent"
        ),
        "shapeSqTaylorSourcePresent": proof_status.get("shapeSqTaylorSourcePresent"),
        "shapeSqValueRemainderAbs": rat_text(shape_sq_value_remainder),
        "shapeSqDerivRemainderAbs": rat_text(shape_sq_deriv_remainder),
        "targetWidth": rat_text(target_width),
        "targetUpperAbs": rat_text(target_upper_abs),
        "shapeSqValueRemainderToTargetWidthRatio": rat_text(
            shape_sq_value_remainder / target_width
        ),
        "shapeSqDerivRemainderToTargetWidthRatio": rat_text(
            shape_sq_deriv_remainder / target_width
        ),
        "scaleFreeShapeSqValueRemainderWithinTargetWidth": value_within_width,
        "scaleFreeShapeSqDerivRemainderWithinTargetWidth": deriv_within_width,
        "auditFailure": None if value_within_width else COARSE_SHAPESQ_BUDGET_FAILURE,
        "interpretation": (
            "Scale-free sanity audit only: the coarse shape-square value "
            "remainder is compared to the final target interval width before "
            "Omega/product propagation.  Failure rejects the current coarse "
            "interval-product assembly source, but it is not a Lean "
            "impossibility theorem and does not kill Step33A.1-A."
        ),
    }


def build_report(
    landing_path: Path, segmented_path: Path, component_path: Path
) -> dict[str, Any]:
    coeffs, symbol_lines = extract_coefficients(landing_path)
    segmented = load_json(segmented_path)
    component = load_json(component_path)
    target_lower = parse_rat(TARGET_LOWER)
    target_upper = parse_rat(TARGET_UPPER)
    target_width = target_upper - target_lower
    component_audit = component_payload_audit(component)

    return {
        "schema": SCHEMA,
        "routeId": ROUTE_ID,
        "status": STATUS,
        "firstFailure": FIRST_FAILURE,
        "failureCodes": [
            FIRST_FAILURE,
            *(
                [COARSE_SHAPESQ_BUDGET_FAILURE]
                if component_audit["auditFailure"] == COARSE_SHAPESQ_BUDGET_FAILURE
                else []
            ),
            SECOND_FAILURE,
            NO_LEAN_PAYLOAD_FAILURE,
            "STEP33_A1_SUB0_CANCELLATION_PRESERVING_TAYLOR_REMAINDER_GAP",
        ],
        "proofStatus": {
            "isLeanProofData": False,
            "outLeanWritten": False,
            "proofSafeClosedFields": 0,
            "componentTaylorBoundsProved": False,
            "exactCoefficientExtractionDone": True,
            "exactCoefficientAssemblyProved": False,
            "assembledResidualCoeffPresent": False,
            "assembledResidualRemainderBoundPresent": False,
            "residualRangeProved": False,
            "budgetPassed": False,
        },
        "cell": {
            "cellL": CELL_L,
            "cellU": CELL_U,
            "center": CENTER,
            "radius": RADIUS,
            "targetLower": TARGET_LOWER,
            "targetUpper": TARGET_UPPER,
            "targetWidth": rat_text(target_width),
        },
        "targetExpression": (
            "primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta - "
            "rawOmegaATaylorPolynomial 15 (1/20) "
            "primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta"
        ),
        "targetTheorem": {
            "file": "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean",
            "name": TARGET_THEOREM,
            "statementAscii": (
                f"theorem {TARGET_THEOREM} {{eta : Real}} "
                "(heta : eta in Set.Icc 0 (1/10)) : "
                f"{TARGET_LOWER} <= targetExpression eta and "
                f"targetExpression eta <= {TARGET_UPPER}"
            ),
        },
        "leanConsumers": {
            "directSegmentData": DIRECT_SEGMENT_DATA,
            "directValidityBridge": DIRECT_VALID_BRIDGE,
            "proofDataWrapper": PROOF_DATA_WRAPPER,
            "polynomialDerivativeCrosswalk": POLY_DERIV_CROSSWALK,
            "residualDerivativeCrosswalk": RESIDUAL_CROSSWALK,
        },
        "extractedFullTaylorPolynomialDerivCoeff": coeffs,
        "rawTaylorCoeffDerivedFromDerivmodel": raw_taylor_coefficients_from_deriv(coeffs),
        "assembledResidualCoeff": None,
        "assembledResidualRemainderAbs": None,
        "componentTaylorInputsRequired": [
            "omegaCoeff[]",
            "omegaRemainderAbs",
            "omegaDerivCoeff[]",
            "omegaDerivRemainderAbs",
            "shapeCoeff[]",
            "shapeRemainderAbs",
            "shapeDerivCoeff[]",
            "shapeDerivRemainderAbs",
            "exact product/convolution assembly before interval spending",
        ],
        "requiredProofGradeCertificate": {
            "kind": "interval_or_rational_same_expression_residual_bound",
            "mustProve": (
                "for all eta in Set.Icc 0 (1/10), targetLower <= "
                "RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 15 "
                "(1/20) ResidualDerivmodelCoeff eta <= targetUpper"
            ),
            "mayFeed": (
                "ResidualDerivativeSegmentIntervalCert.DirectValid."
                "of_single_residual_bounds"
            ),
            "mustNotUse": [
                "sampled direct-derivative overlay as proof",
                "independent raw/poly interval boxes as the proof object",
                "RawCenterCoeffOnlyCert residual bounds for the full Taylor route",
                "the coarse 1/250 shape-square value source as final budget "
                "closure unless an exact same-expression assembly proves it",
            ],
            "currentSmallestUsefulPatch": (
                "Either replace the coarse shape-square derivative/value "
                "source with a sharper nonconstant Taylor source, or prove a "
                "direct same-expression residual interval bound in the local "
                "normalization."
            ),
        },
        "segmentedPayload": segmented_summary(segmented),
        "componentPayloadAudit": component_audit,
        "sourceDefinitionLines": symbol_lines,
        "sourceDefinitionHashes": {
            "Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean": file_hash(
                landing_path
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_segmented_residual_deriv_interval_payload.json": file_hash(
                segmented_path
            ),
            "ACTIVE/requests/step33_bootstrap/"
            "step33_a1_sub0_component_taylor_residual_payload.json": file_hash(
                component_path
            ),
        },
    }


def render_md(report: dict[str, Any]) -> str:
    lines = [
        "# Step33A.1-A Sub0 Cancellation Residual Interval Certificate",
        "",
        "Fail-closed ledger. This is not Lean proof data and does not close",
        "Step33A.1-A.",
        "",
        "## Status",
        "",
        f"- schema: `{report['schema']}`",
        f"- route: `{report['routeId']}`",
        f"- status: `{report['status']}`",
        f"- first failure: `{report['firstFailure']}`",
        f"- Lean emitted: `{report['proofStatus']['outLeanWritten']}`",
        f"- proof-safe closed fields: `{report['proofStatus']['proofSafeClosedFields']}`",
        f"- exact coefficient extraction done: `{report['proofStatus']['exactCoefficientExtractionDone']}`",
        f"- component Taylor bounds proved: `{report['proofStatus']['componentTaylorBoundsProved']}`",
        f"- exact coefficient assembly proved: `{report['proofStatus']['exactCoefficientAssemblyProved']}`",
        f"- residual range proved: `{report['proofStatus']['residualRangeProved']}`",
        "",
        "## Target",
        "",
        f"- cell: `[{report['cell']['cellL']}, {report['cell']['cellU']}]`",
        f"- center: `{report['cell']['center']}`",
        f"- radius: `{report['cell']['radius']}`",
        f"- target lower: `{report['cell']['targetLower']}`",
        f"- target upper: `{report['cell']['targetUpper']}`",
        f"- target width: `{report['cell']['targetWidth']}`",
        f"- expression: `{report['targetExpression']}`",
        f"- target theorem: `{report['targetTheorem']['name']}`",
        "",
        "```text",
        report["targetTheorem"]["statementAscii"],
        "```",
        "",
        "## Lean Consumers",
        "",
    ]
    for key, value in report["leanConsumers"].items():
        line_no = report["sourceDefinitionLines"].get(value)
        suffix = f" (line {line_no})" if line_no else ""
        lines.append(f"- {key}: `{value}`{suffix}")

    lines.extend(
        [
            "",
            "## Extracted Full Taylor Polynomial Derivative Coefficients",
            "",
            "These are extracted from the local Lean definition",
            f"`{COEFF_DEF}`. They are exact rationals, but extraction is",
            "bookkeeping only; it is not the missing interval proof.",
            "",
            "| i | coeff | source line |",
            "| --- | --- | --- |",
        ]
    )
    for item in report["extractedFullTaylorPolynomialDerivCoeff"]:
        lines.append(
            f"| {item['index']} | `{item['value']}` | {item['sourceLine']} |"
        )

    lines.extend(
        [
            "",
            "## Required Component Inputs",
            "",
        ]
    )
    for item in report["componentTaylorInputsRequired"]:
        lines.append(f"- `{item}`")

    lines.extend(
        [
            "",
            "## Required Proof-Grade Certificate",
            "",
            f"- kind: `{report['requiredProofGradeCertificate']['kind']}`",
            f"- may feed: `{report['requiredProofGradeCertificate']['mayFeed']}`",
            f"- must prove: {report['requiredProofGradeCertificate']['mustProve']}",
            "",
            "Must not use:",
        ]
    )
    for item in report["requiredProofGradeCertificate"]["mustNotUse"]:
        lines.append(f"- {item}")

    lines.extend(
        [
            "",
            "Current smallest useful patch:",
            "",
            report["requiredProofGradeCertificate"]["currentSmallestUsefulPatch"],
        ]
    )

    segmented = report["segmentedPayload"]
    lines.extend(
        [
            "",
            "## Segmented Payload Cross-Check",
            "",
            f"- exists: `{segmented['exists']}`",
            f"- schema: `{segmented['schema']}`",
            f"- status: `{segmented['status']}`",
            f"- proof-safe closed fields: `{segmented['proofSafeClosedFields']}`",
            f"- Lean emitted: `{segmented['outLeanWritten']}`",
            f"- segment count: `{segmented['segmentCount']}`",
            f"- coverage passed: `{segmented['coveragePassed']}`",
            f"- all segments budget passed: `{segmented['allSegmentsBudgetPassed']}`",
            "",
            "## Component Payload Coarse Budget Sanity",
            "",
        ]
    )

    component = report["componentPayloadAudit"]
    lines.extend(
        [
            f"- exists: `{component['exists']}`",
            f"- schema: `{component['schema']}`",
            f"- status: `{component['status']}`",
            f"- first failure: `{component['firstFailure']}`",
            f"- proof-safe closed fields: `{component['proofSafeClosedFields']}`",
            f"- shapeSq deriv Taylor source present: `{component['shapeSqDerivTaylorSourcePresent']}`",
            f"- shapeSq value Taylor source present: `{component['shapeSqTaylorSourcePresent']}`",
            f"- target width: `{component['targetWidth']}`",
            f"- target upper abs: `{component['targetUpperAbs']}`",
            f"- shapeSq value remainder abs: `{component['shapeSqValueRemainderAbs']}`",
            f"- shapeSq deriv remainder abs: `{component['shapeSqDerivRemainderAbs']}`",
            f"- value remainder / target width: `{component['shapeSqValueRemainderToTargetWidthRatio']}`",
            f"- deriv remainder / target width: `{component['shapeSqDerivRemainderToTargetWidthRatio']}`",
            f"- value remainder within target width: `{component['scaleFreeShapeSqValueRemainderWithinTargetWidth']}`",
            f"- deriv remainder within target width: `{component['scaleFreeShapeSqDerivRemainderWithinTargetWidth']}`",
            f"- audit failure: `{component['auditFailure']}`",
            "",
            component["interpretation"],
            "",
            "This section is fail-closed diagnostic evidence only. It does not",
            "prove a mathematical obstruction to Step33A.1-A and must not be",
            "used as a Lean theorem.",
            "",
            "## Source Definition Lines",
            "",
        ]
    )
    for key, value in report["sourceDefinitionLines"].items():
        lines.append(f"- `{key}`: `{value}`")

    lines.extend(
        [
            "",
            "## Failure Codes",
            "",
        ]
    )
    for code in report["failureCodes"]:
        lines.append(f"- `{code}`")

    lines.extend(
        [
            "",
            "## Decision",
            "",
            "The route-A Lean receiver and crosswalk names are present, and the",
            "full Taylor derivative-model coefficients have been extracted from",
            "the local Lean source. The current gap is narrower but still open:",
            "there is no component Taylor/remainder certificate that assembles the",
            "same residual expression before spending the interval remainder.",
            "Therefore no Lean payload is emitted and Step33A.1-A remains open.",
            "",
        ]
    )
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--landing", type=Path, default=LANDING_FILE)
    parser.add_argument("--segmented-payload", type=Path, default=SEGMENTED_PAYLOAD)
    parser.add_argument("--component-payload", type=Path, default=COMPONENT_PAYLOAD)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    report = build_report(args.landing, args.segmented_payload, args.component_payload)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(report), encoding="utf-8")

    print(
        "status={status} first_failure={failure} coeffs={coeffs} out_json={out_json}".format(
            status=report["status"],
            failure=report["firstFailure"],
            coeffs=len(report["extractedFullTaylorPolynomialDerivCoeff"]),
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
