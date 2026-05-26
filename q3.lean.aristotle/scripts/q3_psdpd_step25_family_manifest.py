#!/usr/bin/env python3
"""
Step 25 PSD-pd certificate-family manifest.

Purpose:
  Build a registry of interval-backed finite certificate blocks.

For each block:
  - verify midpoint/radius CSV paths
  - compute SHA256 hashes
  - run Step 18 penalty guard in --mode radius
  - parse Dtheta/Rkappa safe lower bounds
  - write manifest CSV + JSON summary

This does NOT create new certificates.
It organizes already-created finite proof blocks into a family/ledger.

Notation:
  k_spline = B-spline degree
  ell      = bump scale
  delta    = grid spacing
  kappa    = kappa-split parameter
  theta    = strengthened certificate parameter
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Optional


@dataclass(frozen=True)
class BlockConfig:
    block_id: str
    family_id: str
    L: float
    k_spline: int
    ell: float
    delta: float
    kappa: float
    theta: float
    midpoint_csv: str
    radius_csv: str
    tau_grid: str = "log:-8:8:161"
    role: str = "candidate"
    notes: str = ""


@dataclass
class BlockResult:
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
    dtheta_safe_lower: Optional[float]
    rkappa_safe_lower: Optional[float]
    dtheta_pass: Optional[bool]
    rkappa_pass: Optional[bool]
    status: str
    stdout_path: str
    notes: str


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_float_maybe(text: str) -> Optional[float]:
    try:
        return float(text)
    except Exception:
        return None


def parse_step18_output(stdout: str) -> tuple[Optional[float], Optional[float], Optional[bool], Optional[bool]]:
    """
    Parse Step 18 output.

    Returns:
      dtheta_safe_lower, rkappa_safe_lower, dtheta_pass, rkappa_pass
    """
    dtheta_safe: Optional[float] = None
    rkappa_safe: Optional[float] = None
    dtheta_pass: Optional[bool] = None
    rkappa_pass: Optional[bool] = None

    current = None
    safe_re = re.compile(r"safe_lower\s*=\s*([-+0-9.eE]+)")
    pass_re = re.compile(r"PASS\s*=\s*(True|False)")

    for raw_line in stdout.splitlines():
        line = raw_line.strip()

        if line.startswith("==") and "Dtheta" in line:
            current = "Dtheta"
        elif line.startswith("==") and ("R_kappa" in line or "Rkappa" in line):
            current = "Rkappa"

        m_safe = safe_re.search(line)
        if m_safe and current:
            val = parse_float_maybe(m_safe.group(1))
            if current == "Dtheta":
                dtheta_safe = val
            elif current == "Rkappa":
                rkappa_safe = val

        m_pass = pass_re.search(line)
        if m_pass and current:
            val = m_pass.group(1) == "True"
            if current == "Dtheta":
                dtheta_pass = val
            elif current == "Rkappa":
                rkappa_pass = val

    if dtheta_pass is None and dtheta_safe is not None:
        dtheta_pass = dtheta_safe > 0.0
    if rkappa_pass is None and rkappa_safe is not None:
        rkappa_pass = rkappa_safe > 0.0

    return dtheta_safe, rkappa_safe, dtheta_pass, rkappa_pass


def read_blocks_csv(path: Path) -> list[BlockConfig]:
    blocks: list[BlockConfig] = []
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            blocks.append(
                BlockConfig(
                    block_id=row["block_id"],
                    family_id=row.get("family_id", "psdpd_family_v1"),
                    L=float(row["L"]),
                    k_spline=int(row["k_spline"]),
                    ell=float(row["ell"]),
                    delta=float(row["delta"]),
                    kappa=float(row["kappa"]),
                    theta=float(row["theta"]),
                    midpoint_csv=row["midpoint_csv"],
                    radius_csv=row["radius_csv"],
                    tau_grid=row.get("tau_grid", "log:-8:8:161"),
                    role=row.get("role", "candidate"),
                    notes=row.get("notes", ""),
                )
            )
    return blocks


def write_default_blocks_csv(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    rows = [
        {
            "block_id": "psdpd_L3_k11_ell030_delta025_theta1e4",
            "family_id": "psdpd_family_v1",
            "L": "3.0",
            "k_spline": "11",
            "ell": "0.30",
            "delta": "0.25",
            "kappa": "3.25",
            "theta": "1e-4",
            "midpoint_csv": "q3.lean.aristotle/docs/insights/q3_psdpd_step22_midpoints_k11.csv",
            "radius_csv": "q3.lean.aristotle/docs/insights/q3_psdpd_step22_radii_k11.csv",
            "tau_grid": "log:-8:8:161",
            "role": "primary",
            "notes": "Primary interval-backed finite block after Step 22.",
        },
        {
            "block_id": "psdpd_L3_k9_ell030_delta025_theta1e5",
            "family_id": "psdpd_family_v1",
            "L": "3.0",
            "k_spline": "9",
            "ell": "0.30",
            "delta": "0.25",
            "kappa": "3.075",
            "theta": "1e-5",
            "midpoint_csv": "q3.lean.aristotle/docs/insights/q3_psdpd_step22_midpoints_k9.csv",
            "radius_csv": "q3.lean.aristotle/docs/insights/q3_psdpd_step22_radii_k9.csv",
            "tau_grid": "log:-8:8:161",
            "role": "control",
            "notes": "Control interval-backed finite block after Step 22.",
        },
    ]

    with path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            lineterminator="\n",
            fieldnames=[
                "block_id",
                "family_id",
                "L",
                "k_spline",
                "ell",
                "delta",
                "kappa",
                "theta",
                "midpoint_csv",
                "radius_csv",
                "tau_grid",
                "role",
                "notes",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)


def run_step18(
    repo_root: Path,
    step18_script: Path,
    block: BlockConfig,
    stdout_dir: Path,
) -> BlockResult:
    mid_path = repo_root / block.midpoint_csv
    rad_path = repo_root / block.radius_csv
    stdout_dir.mkdir(parents=True, exist_ok=True)
    stdout_path = stdout_dir / f"{block.block_id}.step18.txt"

    if not mid_path.exists() or not rad_path.exists():
        missing = []
        if not mid_path.exists():
            missing.append(str(mid_path))
        if not rad_path.exists():
            missing.append(str(rad_path))
        stdout_path.write_text("Missing files:\n" + "\n".join(missing) + "\n")
        return BlockResult(
            block_id=block.block_id,
            family_id=block.family_id,
            role=block.role,
            L=block.L,
            k_spline=block.k_spline,
            ell=block.ell,
            delta=block.delta,
            kappa=block.kappa,
            theta=block.theta,
            tau_grid=block.tau_grid,
            midpoint_csv=block.midpoint_csv,
            radius_csv=block.radius_csv,
            midpoint_sha256="MISSING",
            radius_sha256="MISSING",
            dtheta_safe_lower=None,
            rkappa_safe_lower=None,
            dtheta_pass=None,
            rkappa_pass=None,
            status="MISSING_FILES",
            stdout_path=str(stdout_path.relative_to(repo_root)),
            notes=block.notes,
        )

    cmd = [
        sys.executable,
        str(step18_script),
        "--L",
        str(block.L),
        "--k-spline",
        str(block.k_spline),
        "--ell",
        str(block.ell),
        "--delta",
        str(block.delta),
        "--kappa",
        str(block.kappa),
        "--theta",
        str(block.theta),
        "--mode",
        "radius",
        "--midpoint-csv",
        block.midpoint_csv,
        "--radius-csv",
        block.radius_csv,
        "--tau-grid",
        block.tau_grid,
    ]

    proc = subprocess.run(
        cmd,
        cwd=repo_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    stdout_path.write_text(proc.stdout)

    dtheta_safe, rkappa_safe, dtheta_pass, rkappa_pass = parse_step18_output(proc.stdout)

    if proc.returncode != 0:
        status = "RUN_ERROR"
    elif dtheta_pass and rkappa_pass:
        status = "PASS"
    else:
        status = "FAIL"

    return BlockResult(
        block_id=block.block_id,
        family_id=block.family_id,
        role=block.role,
        L=block.L,
        k_spline=block.k_spline,
        ell=block.ell,
        delta=block.delta,
        kappa=block.kappa,
        theta=block.theta,
        tau_grid=block.tau_grid,
        midpoint_csv=block.midpoint_csv,
        radius_csv=block.radius_csv,
        midpoint_sha256=sha256_file(mid_path),
        radius_sha256=sha256_file(rad_path),
        dtheta_safe_lower=dtheta_safe,
        rkappa_safe_lower=rkappa_safe,
        dtheta_pass=dtheta_pass,
        rkappa_pass=rkappa_pass,
        status=status,
        stdout_path=str(stdout_path.relative_to(repo_root)),
        notes=block.notes,
    )


def write_manifest_csv(path: Path, results: list[BlockResult]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=list(asdict(results[0]).keys()),
            lineterminator="\n",
        )
        writer.writeheader()
        for result in results:
            writer.writerow(asdict(result))


def write_summary_json(path: Path, results: list[BlockResult]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    summary = {
        "total_blocks": len(results),
        "pass_blocks": sum(1 for r in results if r.status == "PASS"),
        "fail_blocks": sum(1 for r in results if r.status == "FAIL"),
        "missing_blocks": sum(1 for r in results if r.status == "MISSING_FILES"),
        "run_error_blocks": sum(1 for r in results if r.status == "RUN_ERROR"),
        "primary_pass": [r.block_id for r in results if r.role == "primary" and r.status == "PASS"],
        "control_pass": [r.block_id for r in results if r.role == "control" and r.status == "PASS"],
        "blocks": [asdict(r) for r in results],
    }
    path.write_text(json.dumps(summary, indent=2, sort_keys=True))


def print_results(results: list[BlockResult]) -> None:
    print("\nCertificate-family manifest")
    print("status        role       block_id                                      Dtheta_safe        Rkappa_safe")
    for result in results:
        d = "NA" if result.dtheta_safe_lower is None else f"{result.dtheta_safe_lower:.6e}"
        r = "NA" if result.rkappa_safe_lower is None else f"{result.rkappa_safe_lower:.6e}"
        print(f"{result.status:<13} {result.role:<10} {result.block_id:<45} {d:>14} {r:>14}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--blocks-csv",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_family_blocks_seed.csv",
        help="Input CSV describing finite certificate blocks.",
    )
    parser.add_argument(
        "--write-default-blocks",
        action="store_true",
        help="Write a default blocks CSV for current k=11 primary and k=9 control.",
    )
    parser.add_argument(
        "--out-manifest",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_certificate_family_manifest.csv",
    )
    parser.add_argument(
        "--out-summary",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_certificate_family_manifest.json",
    )
    parser.add_argument(
        "--stdout-dir",
        default="q3.lean.aristotle/docs/insights/q3_psdpd_family_step18_outputs",
    )
    args = parser.parse_args()

    repo_root = Path.cwd()
    blocks_csv = repo_root / args.blocks_csv

    if args.write_default_blocks:
        write_default_blocks_csv(blocks_csv)
        print(f"Wrote default blocks CSV: {blocks_csv}")

    if not blocks_csv.exists():
        raise SystemExit(
            f"Blocks CSV does not exist: {blocks_csv}\n"
            "Run with --write-default-blocks first or provide --blocks-csv."
        )

    step18_script = repo_root / "q3.lean.aristotle/scripts/q3_psdpd_step18_interval_guard.py"
    if not step18_script.exists():
        raise SystemExit(f"Step 18 script not found: {step18_script}")

    blocks = read_blocks_csv(blocks_csv)
    print("== Step 25 certificate-family manifest ==")
    print(f"repo_root={repo_root}")
    print(f"blocks_csv={blocks_csv}")
    print(f"blocks={len(blocks)}")

    results = [
        run_step18(
            repo_root=repo_root,
            step18_script=step18_script,
            block=block,
            stdout_dir=repo_root / args.stdout_dir,
        )
        for block in blocks
    ]

    out_manifest = repo_root / args.out_manifest
    out_summary = repo_root / args.out_summary
    write_manifest_csv(out_manifest, results)
    write_summary_json(out_summary, results)

    print_results(results)
    print(f"\nWrote manifest: {out_manifest}")
    print(f"Wrote summary:  {out_summary}")

    if any(r.status != "PASS" for r in results):
        raise SystemExit("Some blocks did not PASS.")


if __name__ == "__main__":
    main()
