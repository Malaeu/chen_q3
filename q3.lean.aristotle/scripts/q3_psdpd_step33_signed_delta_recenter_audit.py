#!/usr/bin/env python3
"""Audit whether current A payload radii can contain the signed-A receiver.

The existing finite-tail arithmetic data bounds the current
`centeredBSplineArchKernelProfile`.  The route-B signed receiver needs the
same imported A payload to contain `-centeredBSplineArchKernelProfile`.

For each distance row this checks the necessary recenter inequalities:

  positive: finiteRad + tailRad + | finiteMid - importedA| <= importedARadius
  signed:   finiteRad + tailRad + |-finiteMid - importedA| <= importedARadius

No payload or radius data is mutated.
"""

from __future__ import annotations

import json
import re
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REQUEST_DIR = ROOT / "ACTIVE/requests/step33_bootstrap"
PAYLOAD_IMPORT = ROOT / "Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean"
OUT_JSON = REQUEST_DIR / "a_signed_delta_recenter_audit.json"
OUT_MD = REQUEST_DIR / "a_signed_delta_recenter_audit.md"

getcontext().prec = 80

BLOCKS = [
    {
        "name": "primary",
        "label": "primary k=11",
        "components": REQUEST_DIR / "a_finite_tail_components_k11.json",
        "entry": "primaryK11AAbsDistanceEntryRat",
        "radius": "primaryK11ARadiusAbsDistanceEntryRat",
    },
    {
        "name": "control",
        "label": "control k=9",
        "components": REQUEST_DIR / "a_finite_tail_components_k9.json",
        "entry": "controlK9AAbsDistanceEntryRat",
        "radius": "controlK9ARadiusAbsDistanceEntryRat",
    },
]


def frac_from_decimal(text: str) -> Fraction:
    return Fraction(Decimal(text))


def decimal_string(value: Fraction, digits: int = 34) -> str:
    dec = Decimal(value.numerator) / Decimal(value.denominator)
    return f"{dec:.{digits}E}"


def parse_lean_rat_expr(expr: str) -> Fraction:
    nums = [int(item) for item in re.findall(r"-?\d+", expr)]
    if len(nums) == 1:
        return Fraction(nums[0], 1)
    if len(nums) == 2:
        return Fraction(nums[0], nums[1])
    raise ValueError(f"cannot parse Lean Rat expression: {expr!r}")


def extract_nat_rat_function(source: str, name: str) -> dict[int, Fraction]:
    pattern = re.compile(
        rf"def\s+{re.escape(name)}\s*:\s*Nat\s*->\s*Rat\s*\n"
        rf"(?P<body>(?:\s*\|\s+.*\n)+)",
        re.MULTILINE,
    )
    match = pattern.search(source)
    if not match:
        raise ValueError(f"missing Lean Nat -> Rat function {name}")

    rows: dict[int, Fraction] = {}
    for line in match.group("body").splitlines():
        row_match = re.match(r"\s*\|\s+(\d+)\s*=>\s*(.*)\s*$", line)
        if not row_match:
            continue
        rows[int(row_match.group(1))] = parse_lean_rat_expr(row_match.group(2))

    missing = sorted(set(range(23)) - set(rows))
    if missing:
        raise ValueError(f"{name}: missing rows {missing}")
    return rows


def audit_block(block: dict[str, object], payload_source: str) -> dict[str, object]:
    entry_rows = extract_nat_rat_function(payload_source, str(block["entry"]))
    radius_rows = extract_nat_rat_function(payload_source, str(block["radius"]))

    with Path(block["components"]).open() as handle:
        components = json.load(handle)
    if components.get("schema") != "q3_psdpd_step22_arch_finite_tail_components.v1":
        raise ValueError(f"{block['components']}: unexpected schema")

    rows = []
    for idx, row in enumerate(components["distances"]):
        finite_mid = frac_from_decimal(row["finite_mid"])
        finite_radius = frac_from_decimal(row["finite_radius"])
        tail_radius = frac_from_decimal(row["tail_radius"])
        imported = entry_rows[idx]
        imported_radius = radius_rows[idx]
        local_radius = finite_radius + tail_radius

        positive_required = local_radius + abs(finite_mid - imported)
        signed_required = local_radius + abs(-finite_mid - imported)
        rows.append(
            {
                "index": idx,
                "distance": row["distance"],
                "finite_mid": finite_mid,
                "importedA": imported,
                "finite_radius": finite_radius,
                "tail_radius": tail_radius,
                "imported_radius": imported_radius,
                "positive_required": positive_required,
                "positive_excess": positive_required - imported_radius,
                "positive_pass": positive_required <= imported_radius,
                "signed_required": signed_required,
                "signed_excess": signed_required - imported_radius,
                "signed_pass": signed_required <= imported_radius,
            }
        )

    worst_signed = max(rows, key=lambda item: item["signed_excess"])
    worst_positive = max(rows, key=lambda item: item["positive_excess"])
    return {
        "name": block["name"],
        "label": block["label"],
        "positive_pass_count": sum(1 for row in rows if row["positive_pass"]),
        "signed_pass_count": sum(1 for row in rows if row["signed_pass"]),
        "row_count": len(rows),
        "worst_positive": serialize_row(worst_positive),
        "worst_signed": serialize_row(worst_signed),
        "rows": [serialize_row(row) for row in rows],
    }


def serialize_row(row: dict[str, object]) -> dict[str, object]:
    out: dict[str, object] = {}
    for key, value in row.items():
        if isinstance(value, Fraction):
            out[key] = decimal_string(value)
        else:
            out[key] = value
    return out


def write_markdown(payload: dict[str, object]) -> None:
    lines = [
        "# Signed Delta Recenter Audit",
        "",
        "Non-mutating audit for Step33A.1-A route-B signed finite-Weil `A`.",
        "",
        "Checked inequalities:",
        "",
        "```text",
        "positive: finiteRad + tailRad + | finiteMid - importedA| <= importedARadius",
        "signed:   finiteRad + tailRad + |-finiteMid - importedA| <= importedARadius",
        "```",
        "",
        "## Summary",
        "",
    ]
    for block in payload["blocks"]:
        lines.extend(
            [
                f"### {block['label']}",
                "",
                f"- positive containment: {block['positive_pass_count']}/{block['row_count']}",
                f"- signed containment: {block['signed_pass_count']}/{block['row_count']}",
                f"- worst signed row: d={block['worst_signed']['distance']}, "
                f"excess={block['worst_signed']['signed_excess']}",
                "",
                "| d | finiteMid | importedA | importedRadius | signedRequired | signedExcess |",
                "|---:|---:|---:|---:|---:|---:|",
            ]
        )
        worst_rows = sorted(
            block["rows"], key=lambda row: Decimal(row["signed_excess"]), reverse=True
        )[:6]
        for row in worst_rows:
            lines.append(
                f"| {row['distance']} | {row['finite_mid']} | {row['importedA']} | "
                f"{row['imported_radius']} | {row['signed_required']} | "
                f"{row['signed_excess']} |"
            )
        lines.append("")

    lines.extend(
        [
            "## Conclusion",
            "",
            "The current imported A midpoint/radius payload is compatible with the",
            "old positive-profile receiver, not with the route-B signed receiver.",
            "The signed-delta cert cannot be closed against the current A payload",
            "without either changing the semantic adapter or performing a real",
            "signed-A payload/certificate migration.",
            "",
            "No CSV, `ARadius`, radius-floor, LDL, or Lean payload file was mutated.",
            "",
        ]
    )
    OUT_MD.write_text("\n".join(lines))


def main() -> None:
    payload_source = PAYLOAD_IMPORT.read_text()
    blocks = [audit_block(block, payload_source) for block in BLOCKS]
    payload = {
        "schema": "q3_psdpd_step33_signed_delta_recenter_audit.v1",
        "source": {
            "payload_import": str(PAYLOAD_IMPORT.relative_to(ROOT)),
            "primary_components": str(BLOCKS[0]["components"].relative_to(ROOT)),
            "control_components": str(BLOCKS[1]["components"].relative_to(ROOT)),
        },
        "blocks": blocks,
        "overall_signed_pass": all(
            block["signed_pass_count"] == block["row_count"] for block in blocks
        ),
        "overall_positive_pass": all(
            block["positive_pass_count"] == block["row_count"] for block in blocks
        ),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True))
    write_markdown(payload)
    print(f"wrote {OUT_JSON.relative_to(ROOT)}")
    print(f"wrote {OUT_MD.relative_to(ROOT)}")
    for block in blocks:
        print(
            f"{block['label']}: positive "
            f"{block['positive_pass_count']}/{block['row_count']}, signed "
            f"{block['signed_pass_count']}/{block['row_count']}, worst signed "
            f"excess {block['worst_signed']['signed_excess']} at d="
            f"{block['worst_signed']['distance']}"
        )


if __name__ == "__main__":
    main()
