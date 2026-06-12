#!/usr/bin/env python3
"""Audit refreshed refined-row A recenter containment.

This is a non-mutating Step33A.1-A diagnostic.  It checks whether a refreshed
finite-row target interval, together with the existing tail radius, still fits
the imported A midpoint/radius payload through the interval-recenter receiver.
"""

from __future__ import annotations

import argparse
import json
import re
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
PAYLOAD_IMPORT = ROOT / "Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean"
DEFAULT_ROW_REFRESH = (
    REQUEST_DIR / "a_chunk_taylor_payload_refined_row_target_refresh_audit_primary_finite_row0.json"
)

BLOCKS = {
    "primary_finite": {
        "block": "primary",
        "components": REQUEST_DIR / "a_finite_tail_components_k11.json",
        "entry_rat": "primaryK11AAbsDistanceEntryRat",
        "radius_rat": "primaryK11ARadiusAbsDistanceEntryRat",
    },
    "control_finite": {
        "block": "control",
        "components": REQUEST_DIR / "a_finite_tail_components_k9.json",
        "entry_rat": "controlK9AAbsDistanceEntryRat",
        "radius_rat": "controlK9ARadiusAbsDistanceEntryRat",
    },
}


def dec(value: Any) -> Decimal:
    return Decimal(str(value))


def dstr(value: Decimal) -> str:
    if value == 0:
        return "0.000000000000000000E+0"
    return format(value, ".18E")


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def rat_fraction_to_decimal(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def parse_nat_rat_function(path: Path, name: str, count: int = 23) -> list[Decimal]:
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next((idx for idx, line in enumerate(lines) if line.startswith(f"def {name} ")), None)
    if start is None:
        raise ValueError(f"{path}: missing def {name}")

    values: dict[int, Decimal] = {}
    for line in lines[start + 1 :]:
        stripped = line.strip()
        if not stripped:
            break
        if not stripped.startswith("|"):
            continue
        if stripped.startswith("| _"):
            break
        left, right = stripped.split("=>", 1)
        idx = int(left.replace("|", "").strip())
        numerator_match = re.search(r"\(\(\s*(-?\d+)\s*:\s*Rat\s*\)", right)
        if numerator_match is None:
            raise ValueError(f"{path}: cannot parse numerator in {name} row {idx}: {right!r}")
        numerator = int(numerator_match.group(1))
        denominator = 1
        if "/" in right:
            denominator_part = right.split("/", 1)[1]
            denominator_match = re.search(r"-?\d+", denominator_part)
            if denominator_match is None:
                raise ValueError(f"{path}: cannot parse denominator in {name} row {idx}: {right!r}")
            denominator = int(denominator_match.group(0))
        values[idx] = rat_fraction_to_decimal(Fraction(numerator, denominator))

    missing = [idx for idx in range(count) if idx not in values]
    if missing:
        raise ValueError(f"{path}: {name} missing rows {missing}")
    return [values[idx] for idx in range(count)]


def interval_mid_radius(lower: Decimal, upper: Decimal) -> tuple[Decimal, Decimal]:
    if lower > upper:
        raise ValueError(f"invalid interval: lower {lower} > upper {upper}")
    two = Decimal(2)
    return (lower + upper) / two, (upper - lower) / two


def required_recenter_margin(
    *,
    finite_mid: Decimal,
    finite_radius: Decimal,
    tail_radius: Decimal,
    imported_mid: Decimal,
    imported_radius: Decimal,
) -> dict[str, Decimal]:
    center_error = abs(finite_mid - imported_mid)
    required = finite_radius + tail_radius + center_error
    margin = imported_radius - required
    return {
        "finite_mid": finite_mid,
        "finite_radius": finite_radius,
        "tail_radius": tail_radius,
        "imported_mid": imported_mid,
        "imported_radius": imported_radius,
        "center_error": center_error,
        "required_radius": required,
        "margin": margin,
        "excess": max(Decimal("0"), -margin),
    }


def audit(row_refresh: Path, payload_import: Path) -> dict[str, Any]:
    refresh = load_json(row_refresh)
    family = refresh.get("family")
    if family not in BLOCKS:
        raise ValueError(f"{row_refresh}: unsupported family {family!r}")
    config = BLOCKS[family]
    row = int(refresh["row"])
    if row < 0 or row >= 23:
        raise ValueError(f"{row_refresh}: row must be in [0, 22], got {row}")

    components = load_json(config["components"])
    distances = components.get("distances", [])
    if len(distances) != 23:
        raise ValueError(f"{config['components']}: expected 23 distances, got {len(distances)}")
    component_row = distances[row]
    accounting = refresh["rowAccounting"]

    imported_mid = parse_nat_rat_function(payload_import, config["entry_rat"])[row]
    imported_radius = parse_nat_rat_function(payload_import, config["radius_rat"])[row]
    tail_radius = dec(component_row["tail_radius"])

    before_lower = dec(accounting["targetLowerBefore"])
    before_upper = dec(accounting["targetUpperBefore"])
    before_mid, before_radius = interval_mid_radius(before_lower, before_upper)

    refreshed_lower = dec(accounting["minimalRefreshedTargetLower"])
    refreshed_upper = dec(accounting["minimalRefreshedTargetUpper"])
    refreshed_mid, refreshed_radius = interval_mid_radius(refreshed_lower, refreshed_upper)

    component_finite_mid = dec(component_row["finite_mid"])
    component_finite_radius = dec(component_row["finite_radius"])
    component_lower = component_finite_mid - component_finite_radius
    component_upper = component_finite_mid + component_finite_radius

    before = required_recenter_margin(
        finite_mid=before_mid,
        finite_radius=before_radius,
        tail_radius=tail_radius,
        imported_mid=imported_mid,
        imported_radius=imported_radius,
    )
    refreshed = required_recenter_margin(
        finite_mid=refreshed_mid,
        finite_radius=refreshed_radius,
        tail_radius=tail_radius,
        imported_mid=imported_mid,
        imported_radius=imported_radius,
    )

    status = "pass" if refreshed["margin"] >= 0 else "fail"
    return {
        "schema": "q3_psdpd_step33_a_refined_row_recenter_containment_audit.v1",
        "meaning": (
            "Fail-closed check of refreshed finite-row interval containment through "
            "the interval-recenter A hbox receiver. No Lean payload is emitted."
        ),
        "source_row_refresh": str(row_refresh),
        "source_components": str(config["components"]),
        "source_payload_import": str(payload_import),
        "family": family,
        "block": config["block"],
        "row": row,
        "distance": component_row["distance"],
        "status": status,
        "route_guard": [
            "Do not mutate A CSV, ARadius, radius-floor, LDL, or global payload radii.",
            "This artifact checks only the refreshed finite row target plus existing tail radius.",
            "A pass here is not a full A hbox proof; it only clears this refreshed row.",
            "A fail reports the exact excess and should not be patched by widening global ARadius.",
        ],
        "componentFiniteInterval": {
            "lower": dstr(component_lower),
            "upper": dstr(component_upper),
            "mid": dstr(component_finite_mid),
            "radius": dstr(component_finite_radius),
        },
        "targetBefore": {
            "lower": dstr(before_lower),
            "upper": dstr(before_upper),
            **{key: dstr(value) for key, value in before.items()},
        },
        "targetRefreshed": {
            "lower": dstr(refreshed_lower),
            "upper": dstr(refreshed_upper),
            **{key: dstr(value) for key, value in refreshed.items()},
        },
        "deltas": {
            "lower_decrease": dstr(before_lower - refreshed_lower),
            "upper_increase": dstr(refreshed_upper - before_upper),
            "mid_shift": dstr(refreshed_mid - before_mid),
            "radius_increase": dstr(refreshed_radius - before_radius),
            "component_lower_minus_before_lower": dstr(component_lower - before_lower),
            "component_upper_minus_before_upper": dstr(component_upper - before_upper),
        },
    }


def render_md(result: dict[str, Any]) -> str:
    refreshed = result["targetRefreshed"]
    before = result["targetBefore"]
    lines = [
        "# Step33 A refined row recenter containment audit",
        "",
        "Diagnostic only: refreshed finite-row target checked against imported A recenter containment.",
        "No A CSV, ARadius, radius-floor, LDL, or global payload radius data is mutated.",
        "",
        "## Summary",
        "",
        f"- block: `{result['block']}`",
        f"- family: `{result['family']}`",
        f"- row: `{result['row']}`",
        f"- distance: `{result['distance']}`",
        f"- status: `{result['status']}`",
        "",
        "## Recenter inequality",
        "",
        "```text",
        "finiteRadius + tailRadius + |finiteMid - importedA| <= importedARadius",
        "```",
        "",
        "| target | finite mid | finite radius | tail radius | center error | required radius | imported radius | margin | excess |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
        (
            f"| before | `{before['finite_mid']}` | `{before['finite_radius']}` | "
            f"`{before['tail_radius']}` | `{before['center_error']}` | "
            f"`{before['required_radius']}` | `{before['imported_radius']}` | "
            f"`{before['margin']}` | `{before['excess']}` |"
        ),
        (
            f"| refreshed | `{refreshed['finite_mid']}` | `{refreshed['finite_radius']}` | "
            f"`{refreshed['tail_radius']}` | `{refreshed['center_error']}` | "
            f"`{refreshed['required_radius']}` | `{refreshed['imported_radius']}` | "
            f"`{refreshed['margin']}` | `{refreshed['excess']}` |"
        ),
        "",
        "## Route conclusion",
        "",
    ]
    if result["status"] == "pass":
        lines.extend(
            [
                "The refreshed finite-row interval still fits the existing imported A radius.",
                "This row can use the interval-recenter receiver without global radius mutation.",
                "This is not full A hbox closure; remaining rows/families still need the same check and Lean payload.",
            ]
        )
    else:
        lines.extend(
            [
                "The refreshed finite-row interval does not fit the existing imported A radius.",
                "Do not widen global ARadius as a proof patch.",
                "Report this row as the next exact refreshed-row containment blocker.",
            ]
        )
    return "\n".join(lines) + "\n"


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--row-refresh", type=Path, default=DEFAULT_ROW_REFRESH)
    parser.add_argument("--payload-import", type=Path, default=PAYLOAD_IMPORT)
    parser.add_argument(
        "--out-json",
        type=Path,
        default=REQUEST_DIR / "a_chunk_taylor_payload_refined_row_recenter_containment_primary_finite_row0.json",
    )
    parser.add_argument(
        "--out-md",
        type=Path,
        default=REQUEST_DIR / "a_chunk_taylor_payload_refined_row_recenter_containment_primary_finite_row0.md",
    )
    args = parser.parse_args()

    getcontext().prec = 120
    result = audit(args.row_refresh, args.payload_import)

    print(
        f"{result['block']} {result['family']} row={result['row']} "
        f"status={result['status']} "
        f"margin={result['targetRefreshed']['margin']} "
        f"excess={result['targetRefreshed']['excess']}"
    )

    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote {args.out_json}")
    args.out_md.write_text(render_md(result), encoding="utf-8")
    print(f"Wrote {args.out_md}")


if __name__ == "__main__":
    run()
