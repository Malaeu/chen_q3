#!/usr/bin/env python3
"""Synchronize Step22 A radii with finite/tail Arch manifests.

This helper updates only `matrix=A` rows in the active Step22 radius CSVs.
For conservatism it writes
`max(old_radius, abs(payload_mid - finite_mid) + manifest_total_radius)`,
preserving all already-wider rows and every non-A row.
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
    midpoint_csv: str
    source_manifest: str
    target_sha256_before: str
    target_sha256_after: str
    a_rows: int
    changed_rows: int
    enlarged_rows: int
    preserved_old_rows: int
    max_old_radius: str
    max_source_radius: str
    max_midpoint_offset: str
    max_new_radius: str


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def load_manifest(path: Path) -> dict[int, tuple[Decimal, Decimal]]:
    payload = json.loads(path.read_text())
    if payload.get("schema") != "q3_psdpd_step22_arch_finite_tail_components.v1":
        raise SystemExit(f"{path}: unexpected schema {payload.get('schema')!r}")
    out: dict[int, tuple[Decimal, Decimal]] = {}
    for row in payload.get("distances", []):
        distance = Decimal(row["distance"])
        scaled = distance * Decimal(4)
        if scaled != scaled.to_integral_value():
            raise SystemExit(f"{path}: distance is not a quarter-grid value: {distance}")
        out[int(scaled)] = (Decimal(row["finite_mid"]), Decimal(row["total_radius"]))
    missing = sorted(set(range(23)).difference(out))
    if missing:
        raise SystemExit(f"{path}: missing distance indices {missing}")
    return out


def load_a_midpoints(path: Path) -> dict[tuple[int, int], Decimal]:
    if not path.exists():
        raise SystemExit(f"midpoint CSV not found: {path}")
    out: dict[tuple[int, int], Decimal] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["matrix"].strip() != "A":
                continue
            key = (int(row["i"]), int(row["j"]))
            out[key] = Decimal(row["mid"])
    if len(out) != 23 * 23:
        raise SystemExit(f"{path}: expected 529 A midpoint rows, saw {len(out)}")
    return out


def sync_one(
    block: str,
    target_csv: Path,
    midpoint_csv: Path,
    source_manifest: Path,
) -> SyncStats:
    if not target_csv.exists():
        raise SystemExit(f"target CSV not found: {target_csv}")
    if not source_manifest.exists():
        raise SystemExit(f"source manifest not found: {source_manifest}")

    source = load_manifest(source_manifest)
    midpoints = load_a_midpoints(midpoint_csv)
    before = sha256_file(target_csv)

    with target_csv.open() as f:
        reader = csv.DictReader(f)
        if reader.fieldnames is None:
            raise SystemExit(f"{target_csv}: missing header")
        fields = reader.fieldnames
        rows = list(reader)

    a_rows = 0
    changed = 0
    enlarged = 0
    preserved = 0
    max_old = Decimal(0)
    max_source = Decimal(0)
    max_midpoint_offset = Decimal(0)
    max_new = Decimal(0)

    for row in rows:
        if row["matrix"].strip() != "A":
            continue
        a_rows += 1
        i = int(row["i"])
        j = int(row["j"])
        dist = abs(j - i)
        old = Decimal(row["rad"])
        finite_mid, total_radius = source[dist]
        midpoint_offset = abs(midpoints[(i, j)] - finite_mid)
        src = midpoint_offset + total_radius
        new = max(old, src)
        max_old = max(max_old, old)
        max_source = max(max_source, src)
        max_midpoint_offset = max(max_midpoint_offset, midpoint_offset)
        max_new = max(max_new, new)
        if new != old:
            row["rad"] = str(new)
            changed += 1
            enlarged += 1
        else:
            preserved += 1

    if a_rows != 23 * 23:
        raise SystemExit(f"{target_csv}: expected 529 A rows, saw {a_rows}")

    with target_csv.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

    return SyncStats(
        block=block,
        target_csv=str(target_csv),
        midpoint_csv=str(midpoint_csv),
        source_manifest=str(source_manifest),
        target_sha256_before=before,
        target_sha256_after=sha256_file(target_csv),
        a_rows=a_rows,
        changed_rows=changed,
        enlarged_rows=enlarged,
        preserved_old_rows=preserved,
        max_old_radius=str(max_old),
        max_source_radius=str(max_source),
        max_midpoint_offset=str(max_midpoint_offset),
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
        "--primary-midpoints",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step22_midpoints_k11.csv",
    )
    parser.add_argument(
        "--primary-source-manifest",
        type=Path,
        default=ROOT / "ACTIVE/requests/step33_bootstrap/a_finite_tail_components_k11.json",
    )
    parser.add_argument(
        "--control-target",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step22_radii_k9.csv",
    )
    parser.add_argument(
        "--control-midpoints",
        type=Path,
        default=ROOT / "docs/insights/q3_psdpd_step22_midpoints_k9.csv",
    )
    parser.add_argument(
        "--control-source-manifest",
        type=Path,
        default=ROOT / "ACTIVE/requests/step33_bootstrap/a_finite_tail_components_k9.json",
    )
    parser.add_argument(
        "--summary",
        type=Path,
        default=ROOT / "ACTIVE/requests/step33_bootstrap/a_radius_sync_summary.json",
    )
    args = parser.parse_args()

    results = [
        sync_one(
            "primary",
            args.primary_target,
            args.primary_midpoints,
            args.primary_source_manifest,
        ),
        sync_one(
            "control",
            args.control_target,
            args.control_midpoints,
            args.control_source_manifest,
        ),
    ]
    payload: dict[str, Any] = {
        "schema": "q3_psdpd_step33_sync_a_radii_v1",
        "meaning": (
            "Only Step22 matrix=A radius rows were synchronized with the "
            "finite/tail Arch manifests using max(old, abs(payload_mid - "
            "finite_mid) + manifest_total_radius)."
        ),
        "blocks": [asdict(item) for item in results],
    }
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    for item in results:
        print(
            f"{item.block}: changed={item.changed_rows}/{item.a_rows} "
            f"max_new={item.max_new_radius}"
        )
    print(f"wrote {args.summary}")


if __name__ == "__main__":
    main()
