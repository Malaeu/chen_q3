#!/usr/bin/env python3
"""Audit local A-window slack against the existing imported A radii.

This is a non-mutating Step33A.1-A diagnostic.  It consumes the exact-integrand
chunk probe, computes the minimal outward local slack needed by the finite and
positive-tail window targets, and checks whether the resulting local recenter
containment still fits the current imported A midpoint/radius payload.
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
DEFAULT_PROBE = REQUEST_DIR / "a_chunk_integral_probe.json"
DEFAULT_WINDOW_CONTRACT = REQUEST_DIR / "a_window_contract.json"

BLOCKS = {
    "primary": {
        "finite_family": "primary_finite",
        "tail_family": "primary_tail",
        "entry_rat": "primaryK11AAbsDistanceEntryRat",
        "radius_rat": "primaryK11ARadiusAbsDistanceEntryRat",
    },
    "control": {
        "finite_family": "control_finite",
        "tail_family": "control_tail",
        "entry_rat": "controlK9AAbsDistanceEntryRat",
        "radius_rat": "controlK9ARadiusAbsDistanceEntryRat",
    },
}


def dec(text: str) -> Decimal:
    return Decimal(str(text))


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


def family_rows(probe: dict[str, Any], family_id: str) -> list[dict[str, Any]]:
    for family in probe.get("families", []):
        if family.get("family") == family_id:
            rows = family.get("rows", [])
            if len(rows) != 23:
                raise ValueError(f"{family_id}: expected 23 rows, got {len(rows)}")
            return sorted(rows, key=lambda row: int(row["distance_index"]))
    raise ValueError(f"probe missing family {family_id}")


def window_block(contract: dict[str, Any], block_id: str) -> dict[str, Any]:
    for block in contract.get("blocks", []):
        if block.get("block") == block_id:
            rows = block.get("distances", [])
            if len(rows) != 23:
                raise ValueError(f"{block_id}: expected 23 window rows, got {len(rows)}")
            return block
    raise ValueError(f"window contract missing block {block_id}")


def directional_slack(row: dict[str, Any]) -> tuple[Decimal, Decimal]:
    return dec(row["lower_excess"]), dec(row["upper_excess"])


def audit_block(
    *,
    block_id: str,
    config: dict[str, str],
    probe: dict[str, Any],
    contract: dict[str, Any],
    payload_import: Path,
) -> dict[str, Any]:
    finite_probe = family_rows(probe, config["finite_family"])
    tail_probe = family_rows(probe, config["tail_family"])
    window = window_block(contract, block_id)
    window_rows = sorted(window["distances"], key=lambda row: int(row["index"]))
    imported_mid = parse_nat_rat_function(payload_import, config["entry_rat"])
    imported_radius = parse_nat_rat_function(payload_import, config["radius_rat"])

    rows = []
    finite_failures = 0
    tail_failures = 0
    min_base_margin: Decimal | None = None
    min_slack_margin: Decimal | None = None
    worst_finite_excess = Decimal("0")
    worst_tail_excess = Decimal("0")

    for idx in range(23):
        finite_lower_slack, finite_upper_slack = directional_slack(finite_probe[idx])
        tail_lower_slack, tail_upper_slack = directional_slack(tail_probe[idx])
        row = window_rows[idx]
        if int(row["index"]) != idx:
            raise ValueError(f"{block_id}: window row index mismatch at {idx}")

        finite_mid = dec(row["finite_mid"])
        finite_radius = dec(row["finite_radius"])
        tail_radius = dec(row["generated_tail_radius"])
        base_required = finite_radius + tail_radius + abs(finite_mid - imported_mid[idx])
        base_margin = imported_radius[idx] - base_required

        slack_finite_mid = finite_mid + (finite_upper_slack - finite_lower_slack) / Decimal(2)
        slack_finite_radius = finite_radius + (finite_lower_slack + finite_upper_slack) / Decimal(2)
        slack_required = slack_finite_radius + tail_radius + abs(slack_finite_mid - imported_mid[idx])
        slack_margin = imported_radius[idx] - slack_required
        finite_recenter_excess = max(Decimal("0"), -slack_margin)

        positive_tail_lower = dec(row["positive_window_lower"]) - tail_lower_slack
        positive_tail_upper = dec(row["positive_window_upper"]) + tail_upper_slack
        proof_remainder_radius = dec(row["proof_remainder_radius"])
        signed_tail_lower = Decimal(2) * (positive_tail_lower - proof_remainder_radius)
        signed_tail_upper = Decimal(2) * (positive_tail_upper + proof_remainder_radius)
        tail_lower_excess = max(Decimal("0"), -tail_radius - signed_tail_lower)
        tail_upper_excess = max(Decimal("0"), signed_tail_upper - tail_radius)
        tail_interval_excess = max(tail_lower_excess, tail_upper_excess)

        min_base_margin = base_margin if min_base_margin is None else min(min_base_margin, base_margin)
        min_slack_margin = (
            slack_margin if min_slack_margin is None else min(min_slack_margin, slack_margin)
        )
        worst_finite_excess = max(worst_finite_excess, finite_recenter_excess)
        worst_tail_excess = max(worst_tail_excess, tail_interval_excess)
        finite_failures += int(finite_recenter_excess > 0)
        tail_failures += int(tail_interval_excess > 0)

        rows.append(
            {
                "index": idx,
                "distance": row["distance"],
                "finite_lower_slack": dstr(finite_lower_slack),
                "finite_upper_slack": dstr(finite_upper_slack),
                "tail_lower_slack": dstr(tail_lower_slack),
                "tail_upper_slack": dstr(tail_upper_slack),
                "base_recenter_margin": dstr(base_margin),
                "slack_recenter_margin": dstr(slack_margin),
                "finite_recenter_excess": dstr(finite_recenter_excess),
                "signed_tail_lower_after_slack": dstr(signed_tail_lower),
                "signed_tail_upper_after_slack": dstr(signed_tail_upper),
                "tail_interval_excess": dstr(tail_interval_excess),
                "imported_mid": dstr(imported_mid[idx]),
                "imported_radius": dstr(imported_radius[idx]),
                "slack_finite_mid": dstr(slack_finite_mid),
                "slack_finite_radius": dstr(slack_finite_radius),
            }
        )

    return {
        "block": block_id,
        "finite_family": config["finite_family"],
        "tail_family": config["tail_family"],
        "summary": {
            "rows": len(rows),
            "finite_recenter_failures_after_minimal_slack": finite_failures,
            "tail_interval_failures_after_minimal_slack": tail_failures,
            "min_base_recenter_margin": dstr(min_base_margin or Decimal("0")),
            "min_slack_recenter_margin": dstr(min_slack_margin or Decimal("0")),
            "worst_finite_recenter_excess": dstr(worst_finite_excess),
            "worst_tail_interval_excess": dstr(worst_tail_excess),
            "max_finite_lower_slack": dstr(max(dec(row["finite_lower_slack"]) for row in rows)),
            "max_finite_upper_slack": dstr(max(dec(row["finite_upper_slack"]) for row in rows)),
            "max_tail_lower_slack": dstr(max(dec(row["tail_lower_slack"]) for row in rows)),
            "max_tail_upper_slack": dstr(max(dec(row["tail_upper_slack"]) for row in rows)),
        },
        "rows": rows,
    }


def render_md(result: dict[str, Any]) -> str:
    lines = [
        "# Step33 A local slack recenter audit",
        "",
        "Diagnostic only: local outward-slack and recenter containment audit.",
        "No ARadius, CSV, radius-floor, or global payload radius mutation is performed.",
        "",
        "## Summary",
        "",
        "| block | finite recenter failures | tail interval failures | min base margin | min slack margin | worst finite excess | worst tail excess |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for block in result["blocks"]:
        summary = block["summary"]
        lines.append(
            f"| `{block['block']}` | "
            f"{summary['finite_recenter_failures_after_minimal_slack']} | "
            f"{summary['tail_interval_failures_after_minimal_slack']} | "
            f"`{summary['min_base_recenter_margin']}` | "
            f"`{summary['min_slack_recenter_margin']}` | "
            f"`{summary['worst_finite_recenter_excess']}` | "
            f"`{summary['worst_tail_interval_excess']}` |"
        )
    lines.extend(
        [
            "",
            "## Max local slack",
            "",
            "| block | finite lower | finite upper | tail lower | tail upper |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for block in result["blocks"]:
        summary = block["summary"]
        lines.append(
            f"| `{block['block']}` | `{summary['max_finite_lower_slack']}` | "
            f"`{summary['max_finite_upper_slack']}` | `{summary['max_tail_lower_slack']}` | "
            f"`{summary['max_tail_upper_slack']}` |"
        )
    lines.extend(
        [
            "",
            "## Finite recenter failures",
            "",
            "| block | index | distance | finite excess | slack margin | base margin | finite lower slack | finite upper slack |",
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    failure_count = 0
    for block in result["blocks"]:
        for row in block["rows"]:
            if Decimal(row["finite_recenter_excess"]) <= 0:
                continue
            failure_count += 1
            lines.append(
                f"| `{block['block']}` | {row['index']} | `{row['distance']}` | "
                f"`{row['finite_recenter_excess']}` | `{row['slack_recenter_margin']}` | "
                f"`{row['base_recenter_margin']}` | `{row['finite_lower_slack']}` | "
                f"`{row['finite_upper_slack']}` |"
            )
    if failure_count == 0:
        lines.append("| none |  |  |  |  |  |  |  |")
    worst_finite = max(
        Decimal(block["summary"]["worst_finite_recenter_excess"]) for block in result["blocks"]
    )
    lines.extend(["", "## Route conclusion", ""])
    if worst_finite > Decimal("1e-3"):
        lines.extend(
            [
                "Tail local slack fits the existing generated tail radii in both blocks.",
                "The direct finite full-window route fails at scale: full-window chunks are not",
                "compatible with the current finite target values.",
                "This points to a finite normalization/scale mismatch, not to an `ARadius` issue.",
                "Keep `ARadius`, CSV files, radius-floor, and global payload radii unchanged.",
                "Next local route: resolve the finite positive-half/full-window convention before",
                "trying to prove the direct finite receiver.",
            ]
        )
    else:
        lines.extend(
            [
                "Tail local slack fits the existing generated tail radii in both blocks.",
                "Finite local outward slack does not fit the current imported A radius in the rows above.",
                "Keep `ARadius`, CSV files, radius-floor, and global payload radii unchanged.",
                "Next local route: prefer the existing direct finite-comparison receiver for the finite window,",
                "while keeping the positive-tail-window/proof-remainder route for the tail side.",
            ]
        )
    return "\n".join(lines) + "\n"


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--probe", type=Path, default=DEFAULT_PROBE)
    parser.add_argument("--window-contract", type=Path, default=DEFAULT_WINDOW_CONTRACT)
    parser.add_argument("--payload-import", type=Path, default=PAYLOAD_IMPORT)
    parser.add_argument("--out-json", type=Path, default=REQUEST_DIR / "a_local_slack_recenter_audit.json")
    parser.add_argument("--out-md", type=Path, default=REQUEST_DIR / "a_local_slack_recenter_audit.md")
    args = parser.parse_args()

    getcontext().prec = 100
    probe = load_json(args.probe)
    if probe.get("schema") != "q3_psdpd_step33_a_chunk_integral_probe.v1":
        raise ValueError(f"{args.probe}: unexpected schema {probe.get('schema')!r}")
    contract = load_json(args.window_contract)
    if contract.get("schema") != "q3_psdpd_step33_a_window_contract.v1":
        raise ValueError(f"{args.window_contract}: unexpected schema {contract.get('schema')!r}")

    blocks = [
        audit_block(
            block_id=block_id,
            config=config,
            probe=probe,
            contract=contract,
            payload_import=args.payload_import,
        )
        for block_id, config in BLOCKS.items()
    ]
    result = {
        "schema": "q3_psdpd_step33_a_local_slack_recenter_audit.v1",
        "meaning": (
            "Non-mutating audit of the minimal local outward slack needed by "
            "the exact-integrand A chunk probe, checked against the existing "
            "imported A midpoint/radius recenter containment."
        ),
        "source_probe": str(args.probe),
        "source_window_contract": str(args.window_contract),
        "source_payload_import": str(args.payload_import),
        "blocks": blocks,
    }

    for block in blocks:
        summary = block["summary"]
        print(
            f"{block['block']}: finite_recenter_failures="
            f"{summary['finite_recenter_failures_after_minimal_slack']} "
            f"tail_interval_failures="
            f"{summary['tail_interval_failures_after_minimal_slack']} "
            f"min_slack_margin={summary['min_slack_recenter_margin']} "
            f"worst_tail_excess={summary['worst_tail_interval_excess']}"
        )

    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Wrote {args.out_json}")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_md(result), encoding="utf-8")
        print(f"Wrote {args.out_md}")


if __name__ == "__main__":
    run()
