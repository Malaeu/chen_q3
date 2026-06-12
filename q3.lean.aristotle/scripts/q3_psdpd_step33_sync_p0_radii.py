#!/usr/bin/env python3
"""Synchronize Step21/Step22 P0 radii with the current Arb P0 replay.

This is a proof-data maintenance helper for the PSD Step33 bootstrap route.
It updates only `matrix=P0` rows in the active Step21/Step22 radius CSVs,
preserving all other A/P/Q rows.  For conservatism it writes
`max(old_radius, replay_radius)` instead of shrinking existing radii.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from dataclasses import asdict, dataclass
from decimal import Decimal
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class SyncStats:
    block: str
    target_csv: str
    source_csv: str
    target_sha256_before: str
    target_sha256_after: str
    p0_rows: int
    changed_rows: int
    enlarged_rows: int
    preserved_old_rows: int
    max_old_radius: str
    max_source_radius: str
    max_new_radius: str


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_p0_radii(path: Path) -> dict[tuple[str, str], tuple[Decimal, str]]:
    out: dict[tuple[str, str], tuple[Decimal, str]] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        required = {"matrix", "i", "j", "rad"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise SystemExit(f"{path}: missing columns {sorted(missing)}")
        for row in reader:
            if row["matrix"].strip() != "P0":
                continue
            raw = row["rad"].strip()
            out[(row["i"], row["j"])] = (Decimal(raw), raw)
    return out


def sync_one(block: str, target_csv: Path, source_csv: Path) -> SyncStats:
    if not target_csv.exists():
        raise SystemExit(f"target CSV not found: {target_csv}")
    if not source_csv.exists():
        raise SystemExit(f"source CSV not found: {source_csv}")

    source_p0 = load_p0_radii(source_csv)
    before = sha256_file(target_csv)

    with target_csv.open() as f:
        reader = csv.DictReader(f)
        if reader.fieldnames is None:
            raise SystemExit(f"{target_csv}: missing header")
        fields = reader.fieldnames
        rows = list(reader)

    p0_rows = 0
    changed = 0
    enlarged = 0
    preserved = 0
    max_old = Decimal(0)
    max_source = Decimal(0)
    max_new = Decimal(0)
    missing: list[tuple[str, str]] = []

    for row in rows:
        if row["matrix"].strip() != "P0":
            continue
        p0_rows += 1
        key = (row["i"], row["j"])
        if key not in source_p0:
            missing.append(key)
            continue
        old_raw = row["rad"].strip()
        old = Decimal(old_raw)
        source, source_raw = source_p0[key]
        max_old = max(max_old, old)
        max_source = max(max_source, source)
        if source > old:
            row["rad"] = source_raw
            changed += 1
            enlarged += 1
            max_new = max(max_new, source)
        else:
            preserved += 1
            max_new = max(max_new, old)

    if missing:
        raise SystemExit(f"{target_csv}: missing P0 source rows: {missing[:5]}")
    if p0_rows != len(source_p0):
        raise SystemExit(
            f"{target_csv}: P0 row count mismatch, target={p0_rows}, source={len(source_p0)}"
        )

    with target_csv.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

    return SyncStats(
        block=block,
        target_csv=str(target_csv),
        source_csv=str(source_csv),
        target_sha256_before=before,
        target_sha256_after=sha256_file(target_csv),
        p0_rows=p0_rows,
        changed_rows=changed,
        enlarged_rows=enlarged,
        preserved_old_rows=preserved,
        max_old_radius=str(max_old),
        max_source_radius=str(max_source),
        max_new_radius=str(max_new),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--primary-source",
        type=Path,
        required=True,
        help="Current Arb replay k=11 radius CSV.",
    )
    parser.add_argument(
        "--control-source",
        type=Path,
        required=True,
        help="Current Arb replay k=9 radius CSV.",
    )
    parser.add_argument(
        "--primary-step21-target",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step21_radii_k11.csv",
    )
    parser.add_argument(
        "--primary-step22-target",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step22_radii_k11.csv",
    )
    parser.add_argument(
        "--control-step21-target",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step21_radii_k9.csv",
    )
    parser.add_argument(
        "--control-step22-target",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step22_radii_k9.csv",
    )
    parser.add_argument(
        "--summary",
        type=Path,
        default=ROOT
        / "ACTIVE/requests/step33_bootstrap/p0_radius_sync_summary.json",
    )
    args = parser.parse_args()

    results = [
        sync_one("primary_step21", args.primary_step21_target, args.primary_source),
        sync_one("primary_step22", args.primary_step22_target, args.primary_source),
        sync_one("control_step21", args.control_step21_target, args.control_source),
        sync_one("control_step22", args.control_step22_target, args.control_source),
    ]
    payload: dict[str, Any] = {
        "schema": "q3_psdpd_step33_sync_p0_radii_v1",
        "meaning": (
            "Only matrix=P0 radius rows were synchronized with the current Arb "
            "P0 replay using max(old, replay)."
        ),
        "blocks": [asdict(item) for item in results],
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    for item in results:
        print(
            f"{item.block}: changed={item.changed_rows}/{item.p0_rows} "
            f"max_new={item.max_new_radius}"
        )
    print(f"wrote {args.summary}")


if __name__ == "__main__":
    main()
