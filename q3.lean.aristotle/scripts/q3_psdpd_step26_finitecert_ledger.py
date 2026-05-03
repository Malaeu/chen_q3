#!/usr/bin/env python3
"""
Step 26 PSD-pd FiniteCert ledger consumer.

Purpose:
  Consume the Step 25 certificate-family manifest and emit a compact
  theorem-facing ledger of PASS rows.

This script does not create or re-check matrices.  Step 25 already runs the
Step 18 radius guard and records stdout.  Step 26 verifies artifact hashes,
checks PASS/safe-lower fields, and writes a JSON ledger whose rows correspond
to finite `FinitePenaltyCert` predicates.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class ManifestRow:
    block_id: str
    family_id: str
    role: str
    L: float
    k_spline: int
    ell: float
    delta: float
    kappa: float
    theta: float
    tau_grid: str
    midpoint_csv: str
    radius_csv: str
    midpoint_sha256: str
    radius_sha256: str
    dtheta_safe_lower: float
    rkappa_safe_lower: float
    dtheta_pass: bool
    rkappa_pass: bool
    status: str
    stdout_path: str
    notes: str


def parse_bool(text: str) -> bool:
    return text.strip().lower() in {"true", "1", "yes", "pass"}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_manifest(path: Path) -> list[ManifestRow]:
    rows: list[ManifestRow] = []
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(
                ManifestRow(
                    block_id=row["block_id"],
                    family_id=row["family_id"],
                    role=row["role"],
                    L=float(row["L"]),
                    k_spline=int(row["k_spline"]),
                    ell=float(row["ell"]),
                    delta=float(row["delta"]),
                    kappa=float(row["kappa"]),
                    theta=float(row["theta"]),
                    tau_grid=row["tau_grid"],
                    midpoint_csv=row["midpoint_csv"],
                    radius_csv=row["radius_csv"],
                    midpoint_sha256=row["midpoint_sha256"],
                    radius_sha256=row["radius_sha256"],
                    dtheta_safe_lower=float(row["dtheta_safe_lower"]),
                    rkappa_safe_lower=float(row["rkappa_safe_lower"]),
                    dtheta_pass=parse_bool(row["dtheta_pass"]),
                    rkappa_pass=parse_bool(row["rkappa_pass"]),
                    status=row["status"],
                    stdout_path=row["stdout_path"],
                    notes=row.get("notes", ""),
                )
            )
    return rows


def validate_row(row: ManifestRow, repo_root: Path, min_safe: float) -> tuple[bool, list[str]]:
    errors: list[str] = []

    if row.status != "PASS":
        errors.append(f"status is {row.status}, expected PASS")
    if not row.dtheta_pass:
        errors.append("dtheta_pass is false")
    if not row.rkappa_pass:
        errors.append("rkappa_pass is false")
    if row.dtheta_safe_lower <= min_safe:
        errors.append(f"dtheta_safe_lower <= {min_safe}")
    if row.rkappa_safe_lower <= min_safe:
        errors.append(f"rkappa_safe_lower <= {min_safe}")

    midpoint_path = repo_root / row.midpoint_csv
    radius_path = repo_root / row.radius_csv
    stdout_path = repo_root / row.stdout_path

    if not midpoint_path.exists():
        errors.append(f"missing midpoint_csv: {row.midpoint_csv}")
    elif sha256_file(midpoint_path) != row.midpoint_sha256:
        errors.append("midpoint_sha256 mismatch")

    if not radius_path.exists():
        errors.append(f"missing radius_csv: {row.radius_csv}")
    elif sha256_file(radius_path) != row.radius_sha256:
        errors.append("radius_sha256 mismatch")

    if not stdout_path.exists():
        errors.append(f"missing stdout_path: {row.stdout_path}")
    else:
        text = stdout_path.read_text()
        if "PASS: penalty certificate proves" not in text:
            errors.append("stdout does not contain final Step 18 PASS line")

    return not errors, errors


def row_to_cert(row: ManifestRow) -> dict[str, Any]:
    cert_id = f"{row.family_id}:{row.block_id}"
    return {
        "cert_id": cert_id,
        "predicate": "FinitePenaltyCert(Dtheta, Rkappa, Q)",
        "family_id": row.family_id,
        "block_id": row.block_id,
        "role": row.role,
        "parameters": {
            "L": row.L,
            "k_spline": row.k_spline,
            "ell": row.ell,
            "delta": row.delta,
            "kappa": row.kappa,
            "theta": row.theta,
            "tau_grid": row.tau_grid,
        },
        "artifacts": {
            "midpoint_csv": row.midpoint_csv,
            "midpoint_sha256": row.midpoint_sha256,
            "radius_csv": row.radius_csv,
            "radius_sha256": row.radius_sha256,
            "step18_stdout": row.stdout_path,
        },
        "guards": {
            "Dtheta_safe_lower": row.dtheta_safe_lower,
            "Rkappa_safe_lower": row.rkappa_safe_lower,
            "Dtheta_pass": row.dtheta_pass,
            "Rkappa_pass": row.rkappa_pass,
        },
        "theorem_payload": {
            "boundary_predicate": "Qv = 0",
            "finite_guard": "Dtheta + tau_D Q^T Q > 0 and Rkappa + tau_R Q^T Q > 0",
            "boundary_conclusion": "C^circ >= theta Rkappa^circ and Rkappa^circ > 0",
            "lean_receiver": "Q3.Proofs.FinitePenaltyCert",
        },
        "notes": row.notes,
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True))


def write_markdown(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Step 26 -- FiniteCert ledger",
        "",
        "## Summary",
        "",
        f"- source manifest: `{payload['source_manifest']}`",
        f"- total manifest rows: `{payload['total_rows']}`",
        f"- accepted finite certs: `{payload['accepted_rows']}`",
        f"- rejected rows: `{payload['rejected_rows']}`",
        "",
        "## Accepted certificates",
        "",
        "| cert_id | role | k | ell | theta | Dtheta safe | Rkappa safe |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]

    for cert in payload["finite_certs"]:
        p = cert["parameters"]
        g = cert["guards"]
        lines.append(
            "| "
            f"`{cert['cert_id']}` | "
            f"{cert['role']} | "
            f"{p['k_spline']} | "
            f"{p['ell']} | "
            f"`{p['theta']}` | "
            f"`{g['Dtheta_safe_lower']:.16e}` | "
            f"`{g['Rkappa_safe_lower']:.16e}` |"
        )

    lines.extend(
        [
            "",
            "## Theorem payload",
            "",
            "Each accepted row is treated as a concrete finite predicate:",
            "",
            "```text",
            "FinitePenaltyCert(Dtheta, Rkappa, Q)",
            "```",
            "",
            "Through the Lean receiver `Q3.Proofs.FinitePenaltyCert`, this gives",
            "finite boundary-null positivity:",
            "",
            "\\[",
            "C^\\circ\\succeq \\theta R_\\kappa^\\circ,",
            "\\qquad",
            "R_\\kappa^\\circ\\succ0.",
            "\\]",
            "",
            "This ledger still does not prove the exhaustion theorem.  It supplies",
            "the finite predicates that the Step 23 family/exhaustion contract will",
            "quantify over.",
            "",
        ]
    )

    if payload["rejections"]:
        lines.extend(["## Rejections", ""])
        for item in payload["rejections"]:
            lines.append(f"- `{item['block_id']}`: {', '.join(item['errors'])}")
        lines.append("")

    path.write_text("\n".join(lines))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_certificate_family_manifest.csv",
    )
    parser.add_argument(
        "--out-json",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_finitecert_ledger.json",
    )
    parser.add_argument(
        "--out-md",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step26_finitecert_ledger_2026_05_03.md",
    )
    parser.add_argument("--min-safe", type=float, default=0.0)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path.cwd()
    manifest_path = repo_root / args.manifest

    rows = read_manifest(manifest_path)
    finite_certs: list[dict[str, Any]] = []
    rejections: list[dict[str, Any]] = []

    for row in rows:
        ok, errors = validate_row(row, repo_root, args.min_safe)
        if ok:
            finite_certs.append(row_to_cert(row))
        else:
            rejections.append({"block_id": row.block_id, "errors": errors})

    payload = {
        "source_manifest": args.manifest,
        "total_rows": len(rows),
        "accepted_rows": len(finite_certs),
        "rejected_rows": len(rejections),
        "finite_certs": finite_certs,
        "rejections": rejections,
    }

    write_json(repo_root / args.out_json, payload)
    write_markdown(repo_root / args.out_md, payload)

    print("== Step 26 FiniteCert ledger ==")
    print(f"source_manifest={args.manifest}")
    print(f"accepted={len(finite_certs)} rejected={len(rejections)}")
    for cert in finite_certs:
        print(f"PASS {cert['cert_id']}")
    for item in rejections:
        print(f"REJECT {item['block_id']}: {', '.join(item['errors'])}")

    if rejections:
        raise SystemExit("Some manifest rows failed FiniteCert ledger validation.")


if __name__ == "__main__":
    main()
