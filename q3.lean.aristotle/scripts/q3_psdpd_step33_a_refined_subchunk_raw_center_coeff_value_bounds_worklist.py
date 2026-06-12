#!/usr/bin/env python3
"""Build the raw-center-coeff value-bounds worklist for refined subchunks.

This is a fail-closed control-plane artifact for the active Step33A.1-A
raw-Omega route.  It consumes the v12 direct proof-input worklist, reloads the
selected direct overlays to recover `cert.coeff 0`, and records the exact
value-bounds targets for proving `hRawCenterCoeffAbs` through:

    RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_raw_value_bounds_at

The output is not Lean proof data.  It deliberately leaves the two analytic
raw-value inequalities open:

* rawLower <= step22PositiveAxisOmegaAIntegrand k ell x anchor
* step22PositiveAxisOmegaAIntegrand k ell x anchor <= rawUpper

The two comparisons against `cert.coeff 0` are exact rational metadata and
must still be materialized as Lean proof terms during payload emission.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


getcontext().prec = 100

ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_direct_proof_input_worklist.json"
)
DEFAULT_AUDITS = [
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30.json",
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_1_denom1e30_derivfit.json",
]
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_raw_center_coeff_value_bounds_worklist.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_raw_center_coeff_value_bounds_worklist.md"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_proof_input_worklist.v12"
)
DIRECT_OVERLAY_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.v27"
)
DERIVATIVE_AUDIT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7"
)
OUTPUT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_raw_center_coeff_value_bounds_worklist.v4"
)

VALUE_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_raw_value_bounds_at"
)
COMPONENT_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate.raw_center_coeff_abs_of_raw_component_bounds_at"
)
COMPONENT_CORNER_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_raw_component_corner_bounds_at"
)
INTERVAL_COMPONENT_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_interval_raw_component_bounds_at"
)
INTERVAL_COMPONENT_CORNER_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_interval_raw_component_corner_bounds_at"
)
LOCAL_INTERVAL_COMPONENT_CORNER_BOUNDS_RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_local_interval_raw_component_corner_bounds_at"
)

COMPONENT_ANALYTIC_INPUTS = [
    "omegaLower <= step22OmegaArchWeight anchor",
    "step22OmegaArchWeight anchor <= omegaUpper",
    "shapeSqLower <= centeredBSplineImagTransformRealClosedForm k ell anchor ^ 2",
    "centeredBSplineImagTransformRealClosedForm k ell anchor ^ 2 <= shapeSqUpper",
    "cosLower <= Real.cos (anchor * x)",
    "Real.cos (anchor * x) <= cosUpper",
]

PRODUCT_CORNER_INPUTS = [
    "rawLower <= (ell / pi) * omegaLower * shapeSqLower * cosLower",
    "rawLower <= (ell / pi) * omegaLower * shapeSqLower * cosUpper",
    "rawLower <= (ell / pi) * omegaLower * shapeSqUpper * cosLower",
    "rawLower <= (ell / pi) * omegaLower * shapeSqUpper * cosUpper",
    "rawLower <= (ell / pi) * omegaUpper * shapeSqLower * cosLower",
    "rawLower <= (ell / pi) * omegaUpper * shapeSqLower * cosUpper",
    "rawLower <= (ell / pi) * omegaUpper * shapeSqUpper * cosLower",
    "rawLower <= (ell / pi) * omegaUpper * shapeSqUpper * cosUpper",
    "(ell / pi) * omegaLower * shapeSqLower * cosLower <= rawUpper",
    "(ell / pi) * omegaLower * shapeSqLower * cosUpper <= rawUpper",
    "(ell / pi) * omegaLower * shapeSqUpper * cosLower <= rawUpper",
    "(ell / pi) * omegaLower * shapeSqUpper * cosUpper <= rawUpper",
    "(ell / pi) * omegaUpper * shapeSqLower * cosLower <= rawUpper",
    "(ell / pi) * omegaUpper * shapeSqLower * cosUpper <= rawUpper",
    "(ell / pi) * omegaUpper * shapeSqUpper * cosLower <= rawUpper",
    "(ell / pi) * omegaUpper * shapeSqUpper * cosUpper <= rawUpper",
]

INTERVAL_COMPONENT_INPUTS = [
    "anchor ∈ Set.Ioc L U",
    "∀ eta ∈ Set.Ioc L U, omegaLower <= step22OmegaArchWeight eta",
    "∀ eta ∈ Set.Ioc L U, step22OmegaArchWeight eta <= omegaUpper",
    "∀ eta ∈ Set.Ioc L U, shapeSqLower <= centeredBSplineImagTransformRealClosedForm k ell eta ^ 2",
    "∀ eta ∈ Set.Ioc L U, centeredBSplineImagTransformRealClosedForm k ell eta ^ 2 <= shapeSqUpper",
    "∀ eta ∈ Set.Ioc L U, cosLower <= Real.cos (eta * x)",
    "∀ eta ∈ Set.Ioc L U, Real.cos (eta * x) <= cosUpper",
]

LOCAL_INTERVAL_COMPONENT_INPUTS = [
    "anchor ∈ Set.Ioc a b",
    "∀ eta ∈ Set.Ioc a b, omegaLower <= step22OmegaArchWeight eta",
    "∀ eta ∈ Set.Ioc a b, step22OmegaArchWeight eta <= omegaUpper",
    "∀ eta ∈ Set.Ioc a b, shapeSqLower <= centeredBSplineImagTransformRealClosedForm k ell eta ^ 2",
    "∀ eta ∈ Set.Ioc a b, centeredBSplineImagTransformRealClosedForm k ell eta ^ 2 <= shapeSqUpper",
    "∀ eta ∈ Set.Ioc a b, cosLower <= Real.cos (eta * x)",
    "∀ eta ∈ Set.Ioc a b, Real.cos (eta * x) <= cosUpper",
]


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: expected object root")
    return payload


def validate_schema(payload: dict[str, Any], *, path: Path, schema: str) -> None:
    found = payload.get("schema")
    if found != schema:
        raise ValueError(f"{path}: expected schema {schema!r}, found {found!r}")


def parse_fraction(value: Any, *, field: str) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        num, den = text.split("/", 1)
        return Fraction(int(num), int(den))
    return Fraction(Decimal(text))


def fraction_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_of_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def decimal_sci(value: Fraction | Decimal) -> str:
    if isinstance(value, Fraction):
        value = decimal_of_fraction(value)
    return format(value, ".18E")


def overlay_path(parent: dict[str, Any]) -> Path:
    raw = parent.get("path")
    if not raw:
        raise ValueError(f"parent missing overlay path: {parent!r}")
    path = Path(str(raw))
    if path.is_absolute():
        return path
    return (ROOT / path).resolve()


def audit_key(pilot: dict[str, Any], subchunk: int) -> tuple[Any, ...]:
    return (
        pilot.get("family"),
        pilot.get("row"),
        pilot.get("parentChunk"),
        pilot.get("split"),
        subchunk,
    )


def build_audit_index(paths: list[Path]) -> dict[tuple[Any, ...], dict[str, Any]]:
    index: dict[tuple[Any, ...], dict[str, Any]] = {}
    for path in paths:
        payload = load_json(path)
        validate_schema(payload, path=path, schema=DERIVATIVE_AUDIT_SCHEMA)
        pilot = payload.get("pilot") or {}
        for row in payload.get("subchunks") or []:
            key = audit_key(pilot, int(row["subchunk"]))
            if key in index:
                raise ValueError(f"duplicate derivative audit row for {key}")
            indexed = dict(row)
            indexed["source"] = str(path)
            index[key] = indexed
    return index


def by_subchunk(overlay: dict[str, Any]) -> dict[int, dict[str, Any]]:
    rows = {}
    for row in overlay.get("subchunks") or []:
        subchunk = int(row["subchunk"])
        if subchunk in rows:
            raise ValueError(f"duplicate overlay subchunk {subchunk}")
        rows[subchunk] = row
    return rows


def sampled_diagnostic(row: dict[str, Any] | None, sample_radius: Fraction) -> dict[str, Any]:
    if row is None:
        return {
            "status": "missing_derivative_audit_row",
            "sampledResidualPasses": None,
            "anchorResidualPasses": None,
        }

    sampled = parse_fraction(
        row.get("sampledResidualAbsUpper"), field="sampledResidualAbsUpper"
    )
    anchor = parse_fraction(
        row.get("anchorResidualAbsUpper"), field="anchorResidualAbsUpper"
    )
    sampled_margin = sample_radius - sampled
    anchor_margin = sample_radius - anchor
    return {
        "status": "diagnostic_only_not_proof",
        "source": row.get("source"),
        "sampledResidualAbsUpper": fraction_string(sampled),
        "sampledResidualAbsUpperDecimal": decimal_sci(sampled),
        "anchorResidualAbsUpper": fraction_string(anchor),
        "anchorResidualAbsUpperDecimal": decimal_sci(anchor),
        "sampledResidualMargin": fraction_string(sampled_margin),
        "sampledResidualMarginDecimal": decimal_sci(sampled_margin),
        "anchorResidualMargin": fraction_string(anchor_margin),
        "anchorResidualMarginDecimal": decimal_sci(anchor_margin),
        "sampledResidualPasses": sampled_margin >= 0,
        "anchorResidualPasses": anchor_margin >= 0,
    }


def build_entry(
    *,
    parent: dict[str, Any],
    work_item: dict[str, Any],
    overlay_row: dict[str, Any],
    audit_index: dict[tuple[Any, ...], dict[str, Any]],
) -> dict[str, Any]:
    seeded = overlay_row.get("seededFields") or {}
    coeff = seeded.get("coeff") or []
    if not coeff:
        raise ValueError(f"overlay subchunk missing coeff: {overlay_row!r}")
    coeff0 = parse_fraction(coeff[0], field="coeff[0]")
    sample_radius = parse_fraction(
        work_item["seededScalars"]["sampleRadius"], field="sampleRadius"
    )
    raw_lower = coeff0 - sample_radius
    raw_upper = coeff0 + sample_radius
    subchunk = int(work_item["subchunk"])
    key = (
        parent.get("family"),
        parent.get("row"),
        parent.get("parentChunk"),
        parent.get("split"),
        subchunk,
    )
    diagnostic = sampled_diagnostic(audit_index.get(key), sample_radius)
    return {
        "family": parent.get("family"),
        "row": parent.get("row"),
        "parentChunk": parent.get("parentChunk"),
        "split": parent.get("split"),
        "subchunk": subchunk,
        "left": work_item.get("left"),
        "right": work_item.get("right"),
        "anchor": work_item["seededScalars"].get("anchor"),
        "sampleRadius": fraction_string(sample_radius),
        "sampleRadiusDecimal": decimal_sci(sample_radius),
        "coeff0": fraction_string(coeff0),
        "coeff0Decimal": decimal_sci(coeff0),
        "rawLower": fraction_string(raw_lower),
        "rawLowerDecimal": decimal_sci(raw_lower),
        "rawUpper": fraction_string(raw_upper),
        "rawUpperDecimal": decimal_sci(raw_upper),
        "receiver": VALUE_BOUNDS_RECEIVER,
        "componentBoundsReceiver": COMPONENT_BOUNDS_RECEIVER,
        "componentCornerBoundsReceiver": COMPONENT_CORNER_BOUNDS_RECEIVER,
        "intervalComponentBoundsReceiver": INTERVAL_COMPONENT_BOUNDS_RECEIVER,
        "intervalComponentCornerBoundsReceiver": INTERVAL_COMPONENT_CORNER_BOUNDS_RECEIVER,
        "localIntervalComponentCornerBoundsReceiver": LOCAL_INTERVAL_COMPONENT_CORNER_BOUNDS_RECEIVER,
        "openAnalyticInputs": [
            "rawLower <= step22PositiveAxisOmegaAIntegrand k ell x anchor",
            "step22PositiveAxisOmegaAIntegrand k ell x anchor <= rawUpper",
        ],
        "componentAnalyticInputs": COMPONENT_ANALYTIC_INPUTS,
        "intervalComponentInputs": INTERVAL_COMPONENT_INPUTS,
        "localIntervalComponentInputs": LOCAL_INTERVAL_COMPONENT_INPUTS,
        "productCornerArithmeticInputs": PRODUCT_CORNER_INPUTS,
        "closedArithmeticInputs": {
            "hCoeffLower": {
                "relation": "-sampleRadius <= rawLower - cert.coeff 0",
                "passes": True,
                "excess": "0/1",
                "proofHint": "by norm_num",
            },
            "hCoeffUpper": {
                "relation": "rawUpper - cert.coeff 0 <= sampleRadius",
                "passes": True,
                "excess": "0/1",
                "proofHint": "by norm_num",
            },
        },
        "diagnostic": diagnostic,
        "proofStatus": "address_only_not_lean_proof",
    }


def build_worklist(worklist_path: Path, audit_paths: list[Path]) -> dict[str, Any]:
    direct = load_json(worklist_path)
    validate_schema(direct, path=worklist_path, schema=WORKLIST_SCHEMA)
    audit_index = build_audit_index(audit_paths)

    entries = []
    parents = []
    for parent in direct.get("parents") or []:
        path = overlay_path(parent)
        overlay = load_json(path)
        validate_schema(overlay, path=path, schema=DIRECT_OVERLAY_SCHEMA)
        overlay_rows = by_subchunk(overlay)
        parent_entries = []
        for work_item in parent.get("subchunks") or []:
            subchunk = int(work_item["subchunk"])
            if "hRawCenterCoeffAbs" not in work_item.get("remainingAnalyticFields", []):
                continue
            entry = build_entry(
                parent=parent,
                work_item=work_item,
                overlay_row=overlay_rows[subchunk],
                audit_index=audit_index,
            )
            entries.append(entry)
            parent_entries.append(entry)
        parents.append(
            {
                "family": parent.get("family"),
                "row": parent.get("row"),
                "parentChunk": parent.get("parentChunk"),
                "split": parent.get("split"),
                "path": str(path),
                "hRawCenterCoeffAbsFields": len(parent_entries),
                "rawValueAnalyticInputs": 2 * len(parent_entries),
                "coeffComparisonArithmeticInputs": 2 * len(parent_entries),
                "sampledDiagnosticPassing": sum(
                    1
                    for entry in parent_entries
                    if entry["diagnostic"].get("sampledResidualPasses") is True
                ),
                "entries": parent_entries,
            }
        )

    if not entries:
        raise ValueError("no hRawCenterCoeffAbs entries found")

    sampled_failures = [
        entry
        for entry in entries
        if entry["diagnostic"].get("sampledResidualPasses") is not True
    ]
    anchor_failures = [
        entry
        for entry in entries
        if entry["diagnostic"].get("anchorResidualPasses") is not True
    ]
    worst_sampled = min(
        entries,
        key=lambda entry: Decimal(
            entry["diagnostic"].get("sampledResidualMarginDecimal", "Infinity")
        ),
    )
    return {
        "schema": OUTPUT_SCHEMA,
        "status": "raw_center_coeff_value_bounds_worklist_address_only",
        "meaning": (
            "Fail-closed worklist for proving hRawCenterCoeffAbs via "
            "raw_center_coeff_abs_of_raw_value_bounds_at.  This is not Lean "
            "proof data."
        ),
        "directWorklist": str(worklist_path),
        "directWorklistSchema": direct.get("schema"),
        "receiver": VALUE_BOUNDS_RECEIVER,
        "totals": {
            "parents": len(parents),
            "hRawCenterCoeffAbsFields": len(entries),
            "rawValueAnalyticInputs": 2 * len(entries),
            "componentAnalyticInputs": len(COMPONENT_ANALYTIC_INPUTS) * len(entries),
            "intervalComponentInputs": len(INTERVAL_COMPONENT_INPUTS) * len(entries),
            "localIntervalComponentInputs": len(LOCAL_INTERVAL_COMPONENT_INPUTS)
            * len(entries),
            "anchorMembershipInputs": len(entries),
            "productCornerArithmeticInputs": len(PRODUCT_CORNER_INPUTS) * len(entries),
            "coeffComparisonArithmeticInputs": 2 * len(entries),
            "coeffComparisonArithmeticPassing": 2 * len(entries),
            "sampledDiagnosticPassing": len(entries) - len(sampled_failures),
            "sampledDiagnosticFailingOrMissing": len(sampled_failures),
            "anchorDiagnosticPassing": len(entries) - len(anchor_failures),
            "anchorDiagnosticFailingOrMissing": len(anchor_failures),
            "proofSafeClosedFields": 0,
        },
        "worstSampledDiagnostic": worst_sampled,
        "parents": parents,
        "routeGuard": [
            "address-only worklist",
            "not Lean proof data",
            "sampled diagnostics are not trusted proof inputs",
            "component corner receiver is checked Lean glue, not a numerical oracle",
            "local interval component receiver allows a,b around anchor distinct from cert L,U",
            "rawLower/rawUpper are target enclosures around coeff0, not claims",
            "do not emit RefinedPayloadFin while raw-value inequalities remain unproved",
            "do not mutate CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3",
        ],
    }


def render_md(worklist: dict[str, Any]) -> str:
    totals = worklist["totals"]
    worst = worklist["worstSampledDiagnostic"]
    lines = [
        "# Step33A.1-A Raw-Center-Coeff Value-Bounds Worklist",
        "",
        "Address-only worklist.  This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{worklist['schema']}`",
        f"- status: `{worklist['status']}`",
        f"- receiver: `{worklist['receiver']}`",
        f"- component corner receiver: `{COMPONENT_CORNER_BOUNDS_RECEIVER}`",
        f"- interval component corner receiver: `{INTERVAL_COMPONENT_CORNER_BOUNDS_RECEIVER}`",
        f"- local interval component corner receiver: `{LOCAL_INTERVAL_COMPONENT_CORNER_BOUNDS_RECEIVER}`",
        f"- parents: `{totals['parents']}`",
        f"- hRawCenterCoeffAbs fields: `{totals['hRawCenterCoeffAbsFields']}`",
        f"- raw-value analytic inputs: `{totals['rawValueAnalyticInputs']}`",
        f"- component analytic inputs: `{totals['componentAnalyticInputs']}`",
        f"- interval component inputs: `{totals['intervalComponentInputs']}`",
        f"- local interval component inputs: `{totals['localIntervalComponentInputs']}`",
        f"- anchor membership inputs: `{totals['anchorMembershipInputs']}`",
        f"- product corner arithmetic inputs: `{totals['productCornerArithmeticInputs']}`",
        f"- coeff comparison arithmetic inputs: `{totals['coeffComparisonArithmeticInputs']}`",
        f"- coeff comparison arithmetic passing: `{totals['coeffComparisonArithmeticPassing']}`",
        f"- sampled diagnostic passing: `{totals['sampledDiagnosticPassing']}`",
        f"- anchor diagnostic passing: `{totals['anchorDiagnosticPassing']}`",
        f"- proof-safe closed fields: `{totals['proofSafeClosedFields']}`",
        "",
        "## Bound Shape",
        "",
        "For each subchunk the target raw-value enclosure is:",
        "",
        "```text",
        "rawLower = coeff0 - sampleRadius",
        "rawUpper = coeff0 + sampleRadius",
        "```",
        "",
        "The coeff0 comparisons are exact rational metadata; the two raw-value",
        "inequalities remain analytic proof obligations.",
        "",
        "The checked component-corner receiver can prove each raw-value",
        "enclosure from six component bounds and sixteen rational product-corner",
        "comparisons.",
        "",
        "The checked interval-component receiver lets generated code reuse",
        "component bounds on `(L,U]` plus the already seeded `hAnchorIn` fact,",
        "instead of emitting separate pointwise component proofs at each anchor.",
        "",
        "The checked local-interval receiver is the sharper active target when",
        "full-subchunk component boxes are too wide: it uses an auxiliary",
        "`anchor ∈ Set.Ioc a b` fact and component proofs on `(a,b]`, while",
        "the Taylor certificate remains on its original `(L,U]` window.",
        "",
        "## Worst Sampled Diagnostic",
        "",
        f"- family: `{worst['family']}`",
        f"- row: `{worst['row']}`",
        f"- parentChunk: `{worst['parentChunk']}`",
        f"- subchunk: `{worst['subchunk']}`",
        f"- interval: `({worst['left']}, {worst['right']}]`",
        f"- sampleRadius: `{worst['sampleRadiusDecimal']}`",
        f"- sampled residual margin: `{worst['diagnostic'].get('sampledResidualMarginDecimal')}`",
        "",
        "## Parents",
        "",
        "| family | row | parent | split | hRawCenterCoeffAbs | raw analytic inputs | coeff arithmetic | sampled pass |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for parent in worklist["parents"]:
        lines.append(
            "| `{family}` | `{row}` | `{parent}` | `{split}` | `{fields}` | `{raw}` | `{arith}` | `{sampled}` |".format(
                family=parent["family"],
                row=parent["row"],
                parent=parent["parentChunk"],
                split=parent["split"],
                fields=parent["hRawCenterCoeffAbsFields"],
                raw=parent["rawValueAnalyticInputs"],
                arith=parent["coeffComparisonArithmeticInputs"],
                sampled=parent["sampledDiagnosticPassing"],
            )
        )
    lines.extend(["", "## Guard", ""])
    for item in worklist["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--audit", type=Path, action="append")
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    args = parser.parse_args()

    audit_paths = args.audit if args.audit else DEFAULT_AUDITS
    worklist = build_worklist(args.worklist, audit_paths)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(worklist, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.parent.mkdir(parents=True, exist_ok=True)
    args.out_md.write_text(render_md(worklist), encoding="utf-8")

    totals = worklist["totals"]
    print(
        "status={status} fields={fields} raw_inputs={raw_inputs} out_json={out_json}".format(
            status=worklist["status"],
            fields=totals["hRawCenterCoeffAbsFields"],
            raw_inputs=totals["rawValueAnalyticInputs"],
            out_json=args.out_json,
        )
    )


if __name__ == "__main__":
    run()
