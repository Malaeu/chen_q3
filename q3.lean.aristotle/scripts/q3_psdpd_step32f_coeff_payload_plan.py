#!/usr/bin/env python3
"""
Step 32F coefficient payload import plan.

This script is deliberately not a proof generator.  It validates the accepted
Step 27 seed rows and records the exact Lean payload that a later import layer
must produce:

  Step22 midpoint/radius artifacts
  -> D/R/Q/theta/split data
  -> CertifiedCenteredBSplineCoeffBlock
  -> active manifest label adapter

The goal is to make the next generator node machine-checkable instead of a
manual interpretation of CSV/JSON files.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


EXPECTED_MATRICES = ("A", "P", "P0", "Q")
SQUARE_MATRICES = ("A", "P", "P0")


@dataclass(frozen=True)
class MatrixCsvStats:
    path: str
    value_column: str
    sha256: str
    row_count: int
    matrix_counts: dict[str, int]
    dimensions: dict[str, list[int]]
    duplicate_entries: dict[str, int]
    missing_entries: dict[str, int]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def resolve_existing_path(repo_dir: Path, raw: str) -> Path:
    candidates = [
        repo_dir / raw,
        repo_dir.parent / raw,
    ]
    prefix = "q3.lean.aristotle/"
    if raw.startswith(prefix):
        candidates.append(repo_dir / raw[len(prefix):])

    for path in candidates:
        if path.exists():
            return path

    return candidates[-1]


def output_path(repo_dir: Path, raw: str) -> Path:
    path = Path(raw)
    if path.is_absolute():
        return path
    return repo_dir / path


def inspect_matrix_csv(path: Path, value_column: str) -> MatrixCsvStats:
    seen: dict[str, set[tuple[int, int]]] = {name: set() for name in EXPECTED_MATRICES}
    duplicates: dict[str, int] = {name: 0 for name in EXPECTED_MATRICES}
    max_i: dict[str, int] = {name: -1 for name in EXPECTED_MATRICES}
    max_j: dict[str, int] = {name: -1 for name in EXPECTED_MATRICES}
    row_count = 0

    with path.open() as f:
        reader = csv.DictReader(f)
        required = {"matrix", "i", "j", value_column}
        missing = required.difference(reader.fieldnames or [])
        if missing:
            raise SystemExit(f"{path}: missing columns {sorted(missing)}")

        for row in reader:
            row_count += 1
            matrix = row["matrix"].strip()
            if matrix not in EXPECTED_MATRICES:
                raise SystemExit(f"{path}: unexpected matrix name {matrix!r}")

            i = int(row["i"])
            j = int(row["j"])
            if i < 0 or j < 0:
                raise SystemExit(f"{path}: negative index in row {row_count}")

            key = (i, j)
            if key in seen[matrix]:
                duplicates[matrix] += 1
            seen[matrix].add(key)
            max_i[matrix] = max(max_i[matrix], i)
            max_j[matrix] = max(max_j[matrix], j)

            # Parse the value now so malformed numeric cells fail early.
            float(row[value_column])

    dimensions: dict[str, list[int]] = {}
    missing_entries: dict[str, int] = {}
    matrix_counts: dict[str, int] = {}

    n = max(max_i[name] + 1 for name in SQUARE_MATRICES)
    q_rank = max_i["Q"] + 1

    for name in EXPECTED_MATRICES:
        rows = max_i[name] + 1
        cols = max_j[name] + 1
        dimensions[name] = [rows, cols]
        matrix_counts[name] = len(seen[name])

        expected = q_rank * n if name == "Q" else n * n
        missing_entries[name] = expected - len(seen[name])

    for name in SQUARE_MATRICES:
        if dimensions[name] != [n, n]:
            raise SystemExit(f"{path}: {name} has dimensions {dimensions[name]}, expected {[n, n]}")
    if dimensions["Q"] != [q_rank, n]:
        raise SystemExit(f"{path}: Q has dimensions {dimensions['Q']}, expected {[q_rank, n]}")

    return MatrixCsvStats(
        path=str(path),
        value_column=value_column,
        sha256=sha256_file(path),
        row_count=row_count,
        matrix_counts=matrix_counts,
        dimensions=dimensions,
        duplicate_entries=duplicates,
        missing_entries=missing_entries,
    )


def label_payload(block: dict[str, Any]) -> dict[str, str]:
    k = int(block["k_spline"])
    if k == 11:
        return {
            "label": "CenteredBSplineCoeffManifestLabel.primaryK11L3Ell030Delta025Theta1e4",
            "finite_block_adapter": "CertifiedCenteredBSplineCoeffBlock.toPrimaryK11FiniteBlock",
            "singleton_family_adapter": (
                "CertifiedCenteredBSplineCoeffBlock."
                "toPrimaryK11SingletonDirectedCertFamily"
            ),
            "lean_k": "11",
            "lean_ell": "((3 : ℝ) / 10)",
            "lean_theta": "((1 : ℝ) / 10000)",
            "lean_kappa": "((13 : ℝ) / 4)",
        }
    if k == 9:
        return {
            "label": "CenteredBSplineCoeffManifestLabel.controlK9L3Ell030Delta025Theta1e5",
            "finite_block_adapter": "CertifiedCenteredBSplineCoeffBlock.toControlK9FiniteBlock",
            "singleton_family_adapter": (
                "CertifiedCenteredBSplineCoeffBlock."
                "toControlK9SingletonDirectedCertFamily"
            ),
            "lean_k": "9",
            "lean_ell": "((3 : ℝ) / 10)",
            "lean_theta": "((1 : ℝ) / 100000)",
            "lean_kappa": "((123 : ℝ) / 40)",
        }
    raise SystemExit(f"unsupported active block k_spline={k}")


def validate_block(repo_dir: Path, block: dict[str, Any]) -> dict[str, Any]:
    midpoint_path = resolve_existing_path(repo_dir, block["midpoint_csv"])
    radius_path = resolve_existing_path(repo_dir, block["radius_csv"])
    if not midpoint_path.exists():
        raise SystemExit(f"missing midpoint CSV: {block['midpoint_csv']}")
    if not radius_path.exists():
        raise SystemExit(f"missing radius CSV: {block['radius_csv']}")

    midpoint = inspect_matrix_csv(midpoint_path, "mid")
    radius = inspect_matrix_csv(radius_path, "rad")

    if midpoint.sha256 != block["midpoint_sha256"]:
        raise SystemExit(f"{block['block_id']}: midpoint hash mismatch")
    if radius.sha256 != block["radius_sha256"]:
        raise SystemExit(f"{block['block_id']}: radius hash mismatch")
    if midpoint.dimensions != radius.dimensions:
        raise SystemExit(f"{block['block_id']}: midpoint/radius dimensions differ")
    if any(midpoint.duplicate_entries.values()) or any(radius.duplicate_entries.values()):
        raise SystemExit(f"{block['block_id']}: duplicate CSV entries detected")
    if any(midpoint.missing_entries.values()) or any(radius.missing_entries.values()):
        raise SystemExit(f"{block['block_id']}: missing CSV entries detected")

    n_centers = midpoint.dimensions["A"][0]
    q_rank = midpoint.dimensions["Q"][0]
    if q_rank != 2:
        raise SystemExit(f"{block['block_id']}: expected q_rank=2, got {q_rank}")

    labels = label_payload(block)

    return {
        "block_id": block["block_id"],
        "cert_id": block["cert_id"],
        "family_id": block["family_id"],
        "role": block["role"],
        "status": "validated_import_plan",
        "parameters": {
            "L": block["L"],
            "k_spline": block["k_spline"],
            "ell": block["ell"],
            "delta": block["delta"],
            "kappa": block["kappa"],
            "theta": block["theta"],
            "tau_grid": block["tau_grid"],
        },
        "finite_dimensions": {
            "iota": f"Fin {n_centers}",
            "rho": f"Fin {q_rank}",
            "n_centers": n_centers,
            "q_rank": q_rank,
            "dim_boundary_null": n_centers - q_rank,
        },
        "lean_bindings": labels,
        "artifacts": {
            "midpoint_csv": block["midpoint_csv"],
            "radius_csv": block["radius_csv"],
            "midpoint_sha256": midpoint.sha256,
            "radius_sha256": radius.sha256,
            "step18_stdout": block["step18_stdout"],
        },
        "csv_stats": {
            "midpoint": midpoint.__dict__,
            "radius": radius.__dict__,
        },
        "required_lean_payload": {
            "center_type": f"Fin {n_centers}",
            "prime_shift_type": "generator-defined finite prime-shift index",
            "D": "Dtheta = (1 - theta) * A - P + theta * kappa * P0",
            "R": "Rkappa = A - kappa * P0",
            "Q": "boundary rows from the analytic coefficient contract; CSV Q is the interval-backed numerical row data",
            "theta": labels["lean_theta"],
            "cert": "FinitePenaltyCert D R Q, from Step18 penalty guards",
            "split": "quadForm C v = quadForm D v + theta * quadForm R v, since C = A - P",
        },
        "next_generator_obligations": [
            "emit Lean matrices D and R over the declared center index type",
            "emit or prove equality between CSV Q rows and the analytic contract boundary rows",
            "emit theta_nonneg",
            "emit FinitePenaltyCert penalty positivity proofs from interval guards",
            "emit the quadratic-form split proof C = D + theta R",
            "package the result as CertifiedCenteredBSplineCoeffBlock",
        ],
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True))


def write_markdown(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Step32F coefficient payload import plan",
        "",
        "## Status",
        "",
        payload["status"],
        "",
        "## Meaning",
        "",
        "This is a machine-checkable import plan, not a proof generator.",
        "It validates the Step22/Step27 artifacts and records the exact Lean",
        "payload that must be generated next.",
        "",
        "## Blocks",
        "",
        "| block | role | iota | rho | label |",
        "|---|---:|---:|---:|---|",
    ]

    for block in payload["blocks"]:
        lines.append(
            "| "
            f"`{block['block_id']}` | "
            f"{block['role']} | "
            f"`{block['finite_dimensions']['iota']}` | "
            f"`{block['finite_dimensions']['rho']}` | "
            f"`{block['lean_bindings']['label']}` |"
        )

    lines.extend(
        [
            "",
            "## Required Lean payload",
            "",
            "For each block, the next generator must emit:",
            "",
            "```text",
            "D      = Dtheta = (1 - theta) * A - P + theta * kappa * P0",
            "R      = Rkappa = A - kappa * P0",
            "Q      = boundary rows matching the analytic coefficient contract",
            "theta  = active manifest theta",
            "cert   = FinitePenaltyCert D R Q",
            "split  = quadForm C v = quadForm D v + theta * quadForm R v",
            "block  = CertifiedCenteredBSplineCoeffBlock",
            "```",
            "",
            "## Validation",
            "",
        ]
    )

    for block in payload["blocks"]:
        mid = block["csv_stats"]["midpoint"]
        rad = block["csv_stats"]["radius"]
        lines.extend(
            [
                f"### `{block['block_id']}`",
                "",
                f"- midpoint sha256: `{mid['sha256']}`",
                f"- radius sha256: `{rad['sha256']}`",
                f"- matrix dimensions: `{mid['dimensions']}`",
                f"- row counts: midpoint `{mid['row_count']}`, radius `{rad['row_count']}`",
                "",
            ]
        )

    lines.extend(
        [
            "## Next node",
            "",
            "Build the checked Lean generator/import layer that turns this payload plan",
            "into actual `CertifiedCenteredBSplineCoeffBlock` values for the active",
            "primary/control manifest labels.",
            "",
        ]
    )

    path.write_text("\n".join(lines))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--seed",
        default="docs/insights/q3_psdpd_directed_family_seed.json",
    )
    parser.add_argument(
        "--out-json",
        default="docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json",
    )
    parser.add_argument(
        "--out-md",
        default="docs/insights/q3_psdpd_step32f_coeff_payload_import_plan_2026_05_24.md",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_dir = Path.cwd()
    seed_path = resolve_existing_path(repo_dir, args.seed)
    if not seed_path.exists():
        raise SystemExit(f"seed JSON not found: {args.seed}")

    seed = json.loads(seed_path.read_text())
    blocks = [validate_block(repo_dir, block) for block in seed.get("blocks", [])]
    if not blocks:
        raise SystemExit("seed JSON contains no blocks")

    payload = {
        "schema": "q3_psdpd_step32f_coeff_payload_import_plan_v1",
        "status": "validated_import_plan_not_proof",
        "source_seed": args.seed,
        "accepted_blocks": len(blocks),
        "blocks": blocks,
    }

    out_json = output_path(repo_dir, args.out_json)
    out_md = output_path(repo_dir, args.out_md)
    write_json(out_json, payload)
    write_markdown(out_md, payload)

    print("== Step32F coefficient payload import plan ==")
    print(f"blocks validated: {len(blocks)}")
    for block in blocks:
        dims = block["finite_dimensions"]
        print(f"PASS {block['block_id']}: {dims['iota']} with {dims['rho']}")
    print(f"wrote: {out_json}")
    print(f"wrote: {out_md}")


if __name__ == "__main__":
    main()
