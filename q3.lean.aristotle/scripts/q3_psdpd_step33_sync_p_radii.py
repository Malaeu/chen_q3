#!/usr/bin/env python3
"""Synchronize Step22 P radii with the current Step20 direct-profile replay.

This is a proof-data maintenance helper for the PSD Step33 bootstrap route.
It updates only `matrix=P` rows in the active Step22 radius CSVs, preserving all
other A/P0/Q rows.  For conservatism it writes `max(old_radius, replay_radius)`
instead of shrinking existing radii.
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
    p_rows: int
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


def load_p_radii(path: Path) -> dict[tuple[str, str], Decimal]:
    out: dict[tuple[str, str], Decimal] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        required = {"matrix", "i", "j", "rad"}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise SystemExit(f"{path}: missing columns {sorted(missing)}")
        for row in reader:
            if row["matrix"].strip() != "P":
                continue
            out[(row["i"], row["j"])] = Decimal(row["rad"])
    return out


def sync_one(block: str, target_csv: Path, source_csv: Path) -> SyncStats:
    if not target_csv.exists():
        raise SystemExit(f"target CSV not found: {target_csv}")
    if not source_csv.exists():
        raise SystemExit(f"source CSV not found: {source_csv}")

    source_p = load_p_radii(source_csv)
    before = sha256_file(target_csv)

    with target_csv.open() as f:
        reader = csv.DictReader(f)
        if reader.fieldnames is None:
            raise SystemExit(f"{target_csv}: missing header")
        fields = reader.fieldnames
        rows = list(reader)

    p_rows = 0
    changed = 0
    enlarged = 0
    preserved = 0
    max_old = Decimal(0)
    max_source = Decimal(0)
    max_new = Decimal(0)
    missing: list[tuple[str, str]] = []

    for row in rows:
        if row["matrix"].strip() != "P":
            continue
        p_rows += 1
        key = (row["i"], row["j"])
        if key not in source_p:
            missing.append(key)
            continue
        old = Decimal(row["rad"])
        source = source_p[key]
        new = max(old, source)
        max_old = max(max_old, old)
        max_source = max(max_source, source)
        max_new = max(max_new, new)
        if new != old:
            row["rad"] = str(new)
            changed += 1
            enlarged += 1
        else:
            preserved += 1

    if missing:
        raise SystemExit(f"{target_csv}: missing P source rows: {missing[:5]}")

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
        p_rows=p_rows,
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
        "--primary-target",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step22_radii_k11.csv",
    )
    parser.add_argument(
        "--primary-source",
        type=Path,
        required=True,
        help="Current Step20 k=11 radius CSV.",
    )
    parser.add_argument(
        "--control-target",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step22_radii_k9.csv",
    )
    parser.add_argument(
        "--control-source",
        type=Path,
        required=True,
        help="Current Step20 k=9 radius CSV.",
    )
    parser.add_argument(
        "--summary",
        type=Path,
        default=ROOT
        / "ACTIVE/requests/step33_bootstrap/p_radius_sync_summary.json",
    )
    args = parser.parse_args()

    results = [
        sync_one("primary", args.primary_target, args.primary_source),
        sync_one("control", args.control_target, args.control_source),
    ]
    payload: dict[str, Any] = {
        "schema": "q3_psdpd_step33_sync_p_radii_v1",
        "meaning": (
            "Only Step22 matrix=P radius rows were synchronized with the "
            "current Step20 direct-profile replay using max(old, replay)."
        ),
        "blocks": [asdict(item) for item in results],
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    for item in results:
        print(
            f"{item.block}: changed={item.changed_rows}/{item.p_rows} "
            f"max_new={item.max_new_radius}"
        )
    print(f"wrote {args.summary}")


if __name__ == "__main__":
    main()
