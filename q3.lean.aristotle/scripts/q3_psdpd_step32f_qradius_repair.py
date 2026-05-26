#!/usr/bin/env python3
"""
Repair and audit the active Step32F Q-radius payloads.

The Step22 midpoint CSVs serialize Q midpoints with .18e.  Older generators
computed Q radii around Decimal(str(float_midpoint)), which can differ from the
serialized CSV rational that Lean imports.  This script recomputes the required
analytic boundary-row radius around the exact CSV midpoint decimal and enlarges
only the Q rows in the active Step22 radius CSVs.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from dataclasses import dataclass
from decimal import Decimal, getcontext
from pathlib import Path
from typing import Any

try:
    from flint import arb
except ImportError as exc:
    raise SystemExit(
        "python-flint is required.\n"
        "Install with:\n"
        "  uv add python-flint\n"
    ) from exc

from q3_psdpd_step19_entry_radii import (
    arb_lower_decimal,
    arb_upper_decimal,
    decimal_grid_centers,
    set_precision,
)


@dataclass(frozen=True)
class ActiveBlock:
    name: str
    midpoint_csv: str
    radius_csv: str


ACTIVE_BLOCKS = [
    ActiveBlock(
        name="primary_k11",
        midpoint_csv="docs/insights/q3_psdpd_step22_midpoints_k11.csv",
        radius_csv="docs/insights/q3_psdpd_step22_radii_k11.csv",
    ),
    ActiveBlock(
        name="control_k9",
        midpoint_csv="docs/insights/q3_psdpd_step22_midpoints_k9.csv",
        radius_csv="docs/insights/q3_psdpd_step22_radii_k9.csv",
    ),
]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_midpoints(path: Path) -> dict[tuple[str, int, int], Decimal]:
    out: dict[tuple[str, int, int], Decimal] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            key = (row["matrix"].strip(), int(row["i"]), int(row["j"]))
            out[key] = Decimal(row["mid"].strip())
    return out


def analytic_q_ball(row: int, center: Decimal) -> arb:
    z = arb(str(center)) / arb(2)
    if row == 0:
        return z.exp()
    if row == 1:
        return (-z).exp()
    raise ValueError(f"Q row out of range: {row}")


def required_radius(midpoint: Decimal, x: arb) -> Decimal:
    lo = arb_lower_decimal(x)
    hi = arb_upper_decimal(x)
    return max(abs(midpoint - lo), abs(hi - midpoint))


def format_decimal(value: Decimal) -> str:
    if value < 0:
        raise ValueError(f"radius must be nonnegative: {value}")
    x = float(value)
    text = f"{x:.18e}"
    while Decimal(text) < value:
        x = math.nextafter(x, math.inf)
        text = f"{x:.18e}"
    return text


def repair_block(
    *,
    repo_dir: Path,
    block: ActiveBlock,
    centers: list[Decimal],
    slack_rel: Decimal,
    slack_abs: Decimal,
    dry_run: bool,
) -> dict[str, Any]:
    midpoint_path = repo_dir / block.midpoint_csv
    radius_path = repo_dir / block.radius_csv
    if not midpoint_path.exists():
        raise SystemExit(f"missing midpoint CSV: {midpoint_path}")
    if not radius_path.exists():
        raise SystemExit(f"missing radius CSV: {radius_path}")

    midpoint_sha_before = sha256_file(midpoint_path)
    radius_sha_before = sha256_file(radius_path)
    midpoints = read_midpoints(midpoint_path)

    with radius_path.open() as f:
        reader = csv.DictReader(f)
        if reader.fieldnames != ["matrix", "i", "j", "rad"]:
            raise SystemExit(f"unexpected radius CSV header in {radius_path}: {reader.fieldnames}")
        rows = list(reader)

    updates: list[dict[str, Any]] = []
    failures_before = 0
    failures_after = 0
    q_rows_seen = 0

    for row in rows:
        matrix = row["matrix"].strip()
        if matrix != "Q":
            continue

        i = int(row["i"])
        j = int(row["j"])
        if j < 0 or j >= len(centers):
            raise SystemExit(f"{block.name}: Q column out of center range: {j}")

        q_rows_seen += 1
        key = ("Q", i, j)
        if key not in midpoints:
            raise SystemExit(f"{block.name}: missing Q midpoint row {key}")

        mid = midpoints[key]
        old_rad = Decimal(row["rad"].strip())
        req = required_radius(mid, analytic_q_ball(i, centers[j]))
        inflated = req * slack_rel + slack_abs
        new_rad = max(old_rad, inflated)
        new_rad_text = format_decimal(new_rad)
        new_rad_dec = Decimal(new_rad_text)

        if old_rad < req:
            failures_before += 1
        if new_rad_dec < req:
            failures_after += 1

        if new_rad_text != row["rad"].strip():
            row["rad"] = new_rad_text
            updates.append(
                {
                    "row": i,
                    "col": j,
                    "center": str(centers[j]),
                    "midpoint_csv": str(mid),
                    "old_radius": str(old_rad),
                    "required_radius": str(req),
                    "new_radius": str(new_rad_dec),
                    "shortfall": str(max(Decimal(0), req - old_rad)),
                }
            )

    if q_rows_seen != 2 * len(centers):
        raise SystemExit(
            f"{block.name}: expected {2 * len(centers)} Q rows, saw {q_rows_seen}"
        )

    if not dry_run:
        with radius_path.open("w", newline="") as f:
            writer = csv.DictWriter(
                f,
                fieldnames=["matrix", "i", "j", "rad"],
                lineterminator="\n",
            )
            writer.writeheader()
            writer.writerows(rows)

    radius_sha_after = sha256_file(radius_path) if not dry_run else radius_sha_before
    return {
        "block": block.name,
        "midpoint_csv": block.midpoint_csv,
        "radius_csv": block.radius_csv,
        "midpoint_sha256": midpoint_sha_before,
        "radius_sha256_before": radius_sha_before,
        "radius_sha256_after": radius_sha_after,
        "q_rows_seen": q_rows_seen,
        "updates": len(updates),
        "failures_before": failures_before,
        "failures_after": failures_after,
        "max_shortfall": max((Decimal(u["shortfall"]) for u in updates), default=Decimal(0)).to_eng_string(),
        "updated_entries": updates,
    }


def write_reports(repo_dir: Path, report_json: Path, report_md: Path, payload: dict[str, Any]) -> None:
    report_json.parent.mkdir(parents=True, exist_ok=True)
    report_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    lines = [
        "# Step32F Q-radius serialization repair",
        "",
        "Purpose: enlarge the active Step22 Q radii around the exact midpoint CSV",
        "decimals imported by Lean.",
        "",
        f"- dry_run: {payload['dry_run']}",
        f"- L/ell/delta: {payload['params']['L']} / {payload['params']['ell']} / {payload['params']['delta']}",
        f"- arb_prec: {payload['params']['arb_prec']}",
        f"- slack_rel: {payload['params']['slack_rel']}",
        f"- slack_abs: {payload['params']['slack_abs']}",
        "",
        "## Blocks",
        "",
    ]
    for block in payload["blocks"]:
        lines.extend(
            [
                f"### {block['block']}",
                "",
                f"- radius CSV: `{block['radius_csv']}`",
                f"- Q rows audited: {block['q_rows_seen']}",
                f"- entries rewritten: {block['updates']}",
                f"- failures before: {block['failures_before']}",
                f"- failures after: {block['failures_after']}",
                f"- max shortfall: {block['max_shortfall']}",
                f"- radius sha256 before: `{block['radius_sha256_before']}`",
                f"- radius sha256 after: `{block['radius_sha256_after']}`",
                "",
            ]
        )

    report_md.write_text("\n".join(lines) + "\n")


def run() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-dir", type=str, default=".")
    parser.add_argument("--L", type=str, default="3.0")
    parser.add_argument("--ell", type=str, default="0.30")
    parser.add_argument("--delta", type=str, default="0.25")
    parser.add_argument("--arb-prec", type=int, default=256)
    parser.add_argument("--slack-rel", type=str, default="1.000000001")
    parser.add_argument("--slack-abs", type=str, default="1e-60")
    parser.add_argument(
        "--report-json",
        type=str,
        default="docs/insights/q3_psdpd_step32f_qradius_repair_2026_05_26.json",
    )
    parser.add_argument(
        "--report-md",
        type=str,
        default="docs/insights/q3_psdpd_step32f_qradius_repair_2026_05_26.md",
    )
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    repo_dir = Path(args.repo_dir).resolve()
    set_precision(args.arb_prec)
    getcontext().prec = max(120, args.arb_prec // 2)

    centers = decimal_grid_centers(args.L, args.ell, args.delta)
    slack_rel = Decimal(args.slack_rel)
    slack_abs = Decimal(args.slack_abs)

    blocks = [
        repair_block(
            repo_dir=repo_dir,
            block=block,
            centers=centers,
            slack_rel=slack_rel,
            slack_abs=slack_abs,
            dry_run=args.dry_run,
        )
        for block in ACTIVE_BLOCKS
    ]

    payload = {
        "schema": "q3_psdpd_step32f_qradius_repair_v1",
        "dry_run": args.dry_run,
        "params": {
            "L": args.L,
            "ell": args.ell,
            "delta": args.delta,
            "arb_prec": args.arb_prec,
            "slack_rel": args.slack_rel,
            "slack_abs": args.slack_abs,
        },
        "blocks": blocks,
    }

    write_reports(repo_dir, repo_dir / args.report_json, repo_dir / args.report_md, payload)

    print("== Step32F Q-radius serialization repair ==")
    for block in blocks:
        print(
            f"{block['block']}: updates={block['updates']}, "
            f"failures_before={block['failures_before']}, "
            f"failures_after={block['failures_after']}"
        )

    total_failures_after = sum(block["failures_after"] for block in blocks)
    if total_failures_after:
        raise SystemExit(f"Q-radius repair still has failures: {total_failures_after}")


if __name__ == "__main__":
    run()
