#!/usr/bin/env python3
"""Probe local raw-Omega component intervals for refined subchunk anchors.

This is a fail-closed diagnostic for the active Step33A.1-A route.  It consumes
the raw-center-coeff worklist and checks whether tiny auxiliary intervals
`(anchor - width, anchor]` can feed the checked Lean receiver

    RawOmegaATaylorModelCertificate.
      raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at

The output is not Lean proof data.  It records candidate component boxes,
tight scale interval corners, and the first/largest passing width per selected
subchunk so the later Lean emitter has a concrete target.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from decimal import Decimal, InvalidOperation, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any

try:
    from flint import acb, arb
except ImportError as exc:  # pragma: no cover - environment guard
    raise SystemExit(
        "python-flint is required. Run with:\n"
        "  uv run --with python-flint python "
        "scripts/q3_psdpd_step33_a_refined_subchunk_local_component_interval_probe.py"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    set_precision,
    spline_packet_ball,
)
from q3_psdpd_step22_arch_interval import sinc_acb


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
DEFAULT_WORKLIST = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_raw_center_coeff_value_bounds_worklist.json"
)
DEFAULT_PROOF_DATA = (
    REQUEST_DIR / "a_chunk_taylor_payload_proof_data_skeleton.json"
)
DEFAULT_OUT_JSON = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_local_component_interval_probe.json"
)
DEFAULT_OUT_MD = (
    REQUEST_DIR
    / "a_chunk_taylor_payload_refined_subchunk_local_component_interval_probe.md"
)

WORKLIST_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_raw_center_coeff_value_bounds_worklist.v4"
)
PROOF_DATA_SCHEMA = "q3_psdpd_step33_a_chunk_taylor_payload_proof_data.v1"
OUTPUT_SCHEMA = (
    "q3_psdpd_step33_a_refined_subchunk_local_component_interval_probe.v2"
)
RECEIVER = (
    "RawOmegaATaylorModelCertificate."
    "raw_center_coeff_abs_of_local_interval_raw_component_scale_interval_corner_bounds_at"
)
DEFAULT_SCALE_LOWER = "0.095492965855137201461330258023"
DEFAULT_SCALE_UPPER = "0.095492965855137201461330258024"
DEFAULT_SCALE_MODE = "d29_pi_p30_decimal_bounds"

DEFAULT_WIDTHS = ",".join(
    f"1e-{n}"
    for n in [
        40,
        38,
        36,
        34,
        32,
        30,
        28,
        26,
        24,
        22,
        20,
        19,
        18,
        17,
        16,
        15,
        14,
        13,
        12,
        11,
        10,
        9,
        8,
        7,
        6,
        5,
        4,
        3,
        2,
    ]
)


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


def parse_fraction(value: Any) -> Fraction:
    text = str(value).strip()
    if "/" in text:
        return Fraction(text)
    return Fraction(Decimal(text))


def decimal_of_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def decimal_sci(value: Decimal | Fraction) -> str:
    if isinstance(value, Fraction):
        value = decimal_of_fraction(value)
    return format(value, ".18E")


def decimal_payload(value: Decimal | Fraction) -> str:
    if isinstance(value, Fraction):
        value = decimal_of_fraction(value)
    return format(value, ".80E")


def decimal_text(value: Decimal) -> str:
    return format(value, "f")


def family_k(family: str, k_by_family: dict[str, int]) -> int:
    if family in k_by_family:
        return k_by_family[family]
    if family.startswith("primary_"):
        return 11
    if family.startswith("control_"):
        return 9
    raise ValueError(f"unknown family {family!r}")


def family_ell(_family: str) -> Decimal:
    # `primaryK11EllRat` and `controlK9EllRat` are both `3 / 10`.
    return Decimal("0.3")


def scale_proof_names(family: str) -> dict[str, str]:
    if family.startswith("primary_"):
        return {
            "hScaleLower": "primaryK11Ell_div_pi_tightScaleLower",
            "hScaleUpper": "primaryK11Ell_div_pi_tightScaleUpper",
        }
    if family.startswith("control_"):
        return {
            "hScaleLower": "controlK9Ell_div_pi_tightScaleLower",
            "hScaleUpper": "controlK9Ell_div_pi_tightScaleUpper",
        }
    raise ValueError(f"unknown family {family!r}")


def distance_maps(proof_data: dict[str, Any]) -> tuple[dict[str, dict[int, Decimal]], dict[str, int]]:
    validate_schema(
        proof_data, path=DEFAULT_PROOF_DATA, schema=PROOF_DATA_SCHEMA
    )
    distances: dict[str, dict[int, Decimal]] = {}
    k_by_family: dict[str, int] = {}
    for family in proof_data.get("families") or []:
        family_id = str(family["id"])
        k_by_family[family_id] = int(family["k"])
        distances[family_id] = {
            int(row["index"]): Decimal(str(row["distance"]))
            for row in family.get("distances") or []
        }
    return distances, k_by_family


def parse_widths(text: str) -> list[Decimal]:
    widths = sorted({Decimal(item.strip()) for item in text.split(",") if item.strip()})
    if not widths:
        raise ValueError("at least one width candidate is required")
    if any(width <= 0 for width in widths):
        raise ValueError("all width candidates must be positive")
    return widths


class ComponentEvaluator:
    def __init__(self, *, sinc_terms: int) -> None:
        self.sinc_terms = sinc_terms
        self.log_pi = arb.pi().log()
        self.i_unit = acb(0, 1)

    def component_box(
        self,
        *,
        k: int,
        ell: Decimal,
        distance: Decimal,
        anchor: Decimal,
        width: Decimal,
    ) -> dict[str, Any]:
        left = anchor - width
        right = anchor
        if left < 0:
            raise ValueError("left endpoint is negative")
        mid = (left + right) / Decimal(2)
        radius = (right - left) / Decimal(2)
        eta = acb(arb(str(mid), str(radius)))

        z = acb(arb("0.25")) + self.i_unit * eta / acb(2)
        omega = z.digamma().real - self.log_pi

        s_k, c_k = spline_packet_ball(k)
        shape_arg = acb(arb(str(ell))) * eta / (acb(2) * acb(s_k))
        shape_sq = (
            acb(arb(1) / (s_k * c_k))
            * (sinc_acb(shape_arg, self.sinc_terms) ** (2 * k + 2))
        ).real
        cos_value = (eta * acb(arb(str(distance)))).cos().real

        return {
            "a": left,
            "b": right,
            "omegaLower": arb_lower_decimal(omega),
            "omegaUpper": arb_upper_decimal(omega),
            "shapeSqLower": arb_lower_decimal(shape_sq),
            "shapeSqUpper": arb_upper_decimal(shape_sq),
            "cosLower": arb_lower_decimal(cos_value),
            "cosUpper": arb_upper_decimal(cos_value),
        }


def scale_bounds(
    ell: Decimal,
    *,
    scale_lower: Decimal,
    scale_upper: Decimal,
    pad: Decimal | None,
) -> tuple[dict[str, Decimal], str]:
    if pad is not None:
        scale = arb(str(ell)) / arb.pi()
        center = arb_lower_decimal(scale)
        return (
            {
                "scaleLower": center - pad,
                "scaleUpper": center + pad,
                "scaleCenter": center,
                "scalePad": pad,
                "scaleWidth": pad * Decimal(2),
            },
            "arb_center_plus_scale_pad_diagnostic",
        )
    if scale_lower > scale_upper:
        raise ValueError("scale-lower must be <= scale-upper")
    return (
        {
            "scaleLower": scale_lower,
            "scaleUpper": scale_upper,
            "scaleWidth": scale_upper - scale_lower,
        },
        DEFAULT_SCALE_MODE,
    )


def corner_stats(
    *,
    scale: dict[str, Decimal],
    component: dict[str, Decimal],
    raw_lower: Decimal,
    raw_upper: Decimal,
) -> dict[str, Decimal]:
    corners = [
        scale_value * omega * shape_sq * cos_value
        for scale_value in (scale["scaleLower"], scale["scaleUpper"])
        for omega in (component["omegaLower"], component["omegaUpper"])
        for shape_sq in (component["shapeSqLower"], component["shapeSqUpper"])
        for cos_value in (component["cosLower"], component["cosUpper"])
    ]
    product_lower = min(corners)
    product_upper = max(corners)
    lower_margin = product_lower - raw_lower
    upper_margin = raw_upper - product_upper
    return {
        "productLower": product_lower,
        "productUpper": product_upper,
        "lowerMargin": lower_margin,
        "upperMargin": upper_margin,
        "minMargin": min(lower_margin, upper_margin),
        "excess": max(-lower_margin, -upper_margin, Decimal(0)),
        "productWidth": product_upper - product_lower,
        "targetWidth": raw_upper - raw_lower,
    }


def probe_entry(
    *,
    entry: dict[str, Any],
    distances: dict[str, dict[int, Decimal]],
    k_by_family: dict[str, int],
    widths: list[Decimal],
    scale_lower: Decimal,
    scale_upper: Decimal,
    scale_pad: Decimal | None,
    evaluator: ComponentEvaluator,
) -> dict[str, Any]:
    family = str(entry["family"])
    row_index = int(entry["row"])
    k = family_k(family, k_by_family)
    ell = family_ell(family)
    distance = distances[family][row_index]
    anchor = Decimal(str(entry["anchor"]))
    raw_lower = decimal_of_fraction(parse_fraction(entry["rawLower"]))
    raw_upper = decimal_of_fraction(parse_fraction(entry["rawUpper"]))
    scale, scale_mode = scale_bounds(
        ell,
        scale_lower=scale_lower,
        scale_upper=scale_upper,
        pad=scale_pad,
    )

    attempts: list[dict[str, Any]] = []
    pass_attempts: list[dict[str, Any]] = []
    for width in widths:
        if anchor - width < 0:
            attempts.append(
                {
                    "width": decimal_text(width),
                    "status": "skipped_left_negative",
                }
            )
            continue
        try:
            component = evaluator.component_box(
                k=k, ell=ell, distance=distance, anchor=anchor, width=width
            )
            stats = corner_stats(
                scale=scale,
                component=component,
                raw_lower=raw_lower,
                raw_upper=raw_upper,
            )
            status = "passes" if stats["excess"] == 0 else "fails"
            attempt = {
                "width": decimal_text(width),
                "status": status,
                "a": decimal_text(component["a"]),
                "b": decimal_text(component["b"]),
                "productLowerDecimal": decimal_sci(stats["productLower"]),
                "productUpperDecimal": decimal_sci(stats["productUpper"]),
                "lowerMarginDecimal": decimal_sci(stats["lowerMargin"]),
                "upperMarginDecimal": decimal_sci(stats["upperMargin"]),
                "minMarginDecimal": decimal_sci(stats["minMargin"]),
                "excessDecimal": decimal_sci(stats["excess"]),
                "productWidthDecimal": decimal_sci(stats["productWidth"]),
                "targetWidthDecimal": decimal_sci(stats["targetWidth"]),
            }
            if status == "passes":
                pass_attempts.append(
                    {
                        **attempt,
                        "component": {
                            "omegaLower": decimal_payload(component["omegaLower"]),
                            "omegaUpper": decimal_payload(component["omegaUpper"]),
                            "shapeSqLower": decimal_payload(component["shapeSqLower"]),
                            "shapeSqUpper": decimal_payload(component["shapeSqUpper"]),
                            "cosLower": decimal_payload(component["cosLower"]),
                            "cosUpper": decimal_payload(component["cosUpper"]),
                        },
                    }
                )
            attempts.append(attempt)
        except (InvalidOperation, ValueError) as exc:
            attempts.append(
                {
                    "width": decimal_text(width),
                    "status": "arb_invalid",
                    "error": str(exc) or exc.__class__.__name__,
                }
            )

    chosen = max(pass_attempts, key=lambda item: Decimal(item["width"])) if pass_attempts else None
    first = min(pass_attempts, key=lambda item: Decimal(item["width"])) if pass_attempts else None
    best_failure = None
    if chosen is None:
        failures = [item for item in attempts if item.get("status") == "fails"]
        if failures:
            best_failure = min(
                failures, key=lambda item: Decimal(item["excessDecimal"])
            )

    return {
        "family": family,
        "row": row_index,
        "distance": decimal_text(distance),
        "parentChunk": entry["parentChunk"],
        "split": entry["split"],
        "subchunk": entry["subchunk"],
        "anchor": decimal_text(anchor),
        "rawLowerDecimal": entry["rawLowerDecimal"],
        "rawUpperDecimal": entry["rawUpperDecimal"],
        "sampleRadiusDecimal": entry["sampleRadiusDecimal"],
        "k": k,
        "ell": decimal_text(ell),
        "receiver": RECEIVER,
        "scaleMode": scale_mode,
        "scale": {
            name: decimal_text(value)
            if name in {"scaleLower", "scaleUpper"}
            else decimal_sci(value)
            for name, value in scale.items()
        },
        "scaleProofs": scale_proof_names(family),
        "status": "passes" if chosen is not None else "fails",
        "firstPassingWidth": first["width"] if first else None,
        "largestPassingWidth": chosen["width"] if chosen else None,
        "chosen": chosen,
        "bestFailure": best_failure,
        "attempts": attempts,
    }


def flatten_entries(worklist: dict[str, Any]) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for parent in worklist.get("parents") or []:
        for entry in parent.get("entries") or []:
            enriched = dict(entry)
            enriched.setdefault("row", parent.get("row"))
            enriched.setdefault("split", parent.get("split"))
            entries.append(enriched)
    return entries


def build_probe(args: argparse.Namespace) -> dict[str, Any]:
    worklist = load_json(args.worklist)
    validate_schema(worklist, path=args.worklist, schema=WORKLIST_SCHEMA)
    proof_data = load_json(args.proof_data)
    distances, k_by_family = distance_maps(proof_data)
    widths = parse_widths(args.widths)
    set_precision(args.arb_prec)
    getcontext().prec = max(120, args.arb_prec // 4)
    evaluator = ComponentEvaluator(sinc_terms=args.sinc_terms)

    entries = flatten_entries(worklist)
    scale_pad = Decimal(args.scale_pad) if args.scale_pad is not None else None
    scale_lower = Decimal(args.scale_lower)
    scale_upper = Decimal(args.scale_upper)
    rows = [
        probe_entry(
            entry=entry,
            distances=distances,
            k_by_family=k_by_family,
            widths=widths,
            scale_lower=scale_lower,
            scale_upper=scale_upper,
            scale_pad=scale_pad,
            evaluator=evaluator,
        )
        for entry in entries
    ]
    failures = [row for row in rows if row["status"] != "passes"]
    distribution = Counter(row["largestPassingWidth"] or "FAIL" for row in rows)
    worst_pass = None
    passing = [row for row in rows if row["chosen"] is not None]
    if passing:
        worst_pass = min(
            passing,
            key=lambda row: Decimal(row["chosen"]["minMarginDecimal"]),
        )
    worst_failure = None
    if failures:
        worst_failure = max(
            failures,
            key=lambda row: Decimal(row["bestFailure"]["excessDecimal"])
            if row["bestFailure"]
            else Decimal("Infinity"),
        )

    return {
        "schema": OUTPUT_SCHEMA,
        "status": (
            "local_component_interval_probe_passed_not_lean_proof"
            if not failures
            else "local_component_interval_probe_has_failures_not_lean_proof"
        ),
        "meaning": (
            "Diagnostic Arb/acb probe for local component boxes around refined "
            "subchunk anchors.  This records candidate payload targets but does "
            "not prove the analytic component bounds in Lean."
        ),
        "worklist": str(args.worklist),
        "worklistSchema": worklist.get("schema"),
        "proofData": str(args.proof_data),
        "receiver": RECEIVER,
        "arbPrec": args.arb_prec,
        "sincTerms": args.sinc_terms,
        "widthCandidates": [decimal_text(width) for width in widths],
        "scaleMode": (
            "arb_center_plus_scale_pad_diagnostic"
            if scale_pad is not None
            else DEFAULT_SCALE_MODE
        ),
        "scaleLower": decimal_text(scale_lower),
        "scaleUpper": decimal_text(scale_upper),
        "scalePad": args.scale_pad,
        "totals": {
            "entries": len(rows),
            "passedAnyWidth": len(rows) - len(failures),
            "failedAnyWidth": len(failures),
            "widthDistribution": dict(sorted(distribution.items())),
            "cornerArithmeticInputsPerEntry": 32,
            "componentAnalyticInputsPerEntry": 6,
            "scaleBoundInputsPerEntry": 2,
            "coeffComparisonInputsPerEntry": 2,
            "proofSafeClosedFields": 0,
        },
        "worstPassingEntry": worst_pass,
        "worstFailureEntry": worst_failure,
        "rows": rows,
        "routeGuard": [
            "diagnostic only, not Lean proof data",
            "uses local auxiliary intervals (a,b] around anchors",
            "uses tight rational scale interval, not coarse [9/100,1/10]",
            "requires later Lean hScaleLower/hScaleUpper facts",
            "requires later Lean omega/shape/cos interval proofs",
            "does not emit RefinedPayloadFin",
            "does not mutate CSV, ARadius, radius-floor, LDL, Q3.Main, H1, or PO3",
        ],
    }


def render_md(probe: dict[str, Any]) -> str:
    totals = probe["totals"]
    lines = [
        "# Step33A.1-A Local Component Interval Probe",
        "",
        "Diagnostic only.  This is not Lean proof data.",
        "",
        "## Summary",
        "",
        f"- schema: `{probe['schema']}`",
        f"- status: `{probe['status']}`",
        f"- receiver: `{probe['receiver']}`",
        f"- Arb precision: `{probe['arbPrec']}`",
        f"- sinc terms: `{probe['sincTerms']}`",
        f"- scale mode: `{probe['scaleMode']}`",
        f"- scale lower: `{probe['scaleLower']}`",
        f"- scale upper: `{probe['scaleUpper']}`",
        f"- scale pad override: `{probe['scalePad']}`",
        f"- entries: `{totals['entries']}`",
        f"- passed at some width: `{totals['passedAnyWidth']}`",
        f"- failed at all widths: `{totals['failedAnyWidth']}`",
        f"- proof-safe closed fields: `{totals['proofSafeClosedFields']}`",
        "",
        "## Width Distribution",
        "",
        "| largest passing width | entries |",
        "| ---: | ---: |",
    ]
    for width, count in totals["widthDistribution"].items():
        lines.append(f"| `{width}` | `{count}` |")

    worst = probe.get("worstPassingEntry")
    if worst:
        chosen = worst["chosen"]
        lines.extend(
            [
                "",
                "## Worst Passing Margin",
                "",
                f"- family: `{worst['family']}`",
                f"- row: `{worst['row']}`",
                f"- parent chunk: `{worst['parentChunk']}`",
                f"- subchunk: `{worst['subchunk']}`",
                f"- largest passing width: `{worst['largestPassingWidth']}`",
                f"- min margin: `{chosen['minMarginDecimal']}`",
                f"- product width: `{chosen['productWidthDecimal']}`",
                f"- target width: `{chosen['targetWidthDecimal']}`",
            ]
        )

    lines.extend(
        [
            "",
            "## Next Lean Payload Contract",
            "",
            "Each selected row still needs Lean proofs for:",
            "",
            "```text",
            "anchor ∈ Set.Ioc a b",
            "∀ eta ∈ Set.Ioc a b, omegaLower <= step22OmegaArchWeight eta",
            "∀ eta ∈ Set.Ioc a b, step22OmegaArchWeight eta <= omegaUpper",
            "∀ eta ∈ Set.Ioc a b, shapeSqLower <= centeredBSplineImagTransformRealClosedForm k ell eta ^ 2",
            "∀ eta ∈ Set.Ioc a b, centeredBSplineImagTransformRealClosedForm k ell eta ^ 2 <= shapeSqUpper",
            "∀ eta ∈ Set.Ioc a b, cosLower <= Real.cos (eta * x)",
            "∀ eta ∈ Set.Ioc a b, Real.cos (eta * x) <= cosUpper",
            "scaleLower <= ell / Real.pi",
            "ell / Real.pi <= scaleUpper",
            "32 scale-interval product corner comparisons",
            "2 coeff0 comparisons",
            "```",
            "",
            "## Guard",
            "",
        ]
    )
    for item in probe["routeGuard"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worklist", type=Path, default=DEFAULT_WORKLIST)
    parser.add_argument("--proof-data", type=Path, default=DEFAULT_PROOF_DATA)
    parser.add_argument("--out-json", type=Path, default=DEFAULT_OUT_JSON)
    parser.add_argument("--out-md", type=Path, default=DEFAULT_OUT_MD)
    parser.add_argument("--arb-prec", type=int, default=1024)
    parser.add_argument("--sinc-terms", type=int, default=128)
    parser.add_argument("--scale-lower", type=str, default=DEFAULT_SCALE_LOWER)
    parser.add_argument("--scale-upper", type=str, default=DEFAULT_SCALE_UPPER)
    parser.add_argument("--scale-pad", type=str, default=None)
    parser.add_argument("--widths", type=str, default=DEFAULT_WIDTHS)
    args = parser.parse_args()

    probe = build_probe(args)
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(
        json.dumps(probe, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.out_md.write_text(render_md(probe), encoding="utf-8")
    print(
        "local_component_interval_probe: "
        f"entries={probe['totals']['entries']} "
        f"passed={probe['totals']['passedAnyWidth']} "
        f"failed={probe['totals']['failedAnyWidth']} "
        f"out={args.out_json}"
    )


if __name__ == "__main__":
    main()
