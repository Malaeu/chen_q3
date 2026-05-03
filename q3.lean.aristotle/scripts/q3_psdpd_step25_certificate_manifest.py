#!/usr/bin/env python3
"""
Step 25 PSD-pd certificate-family manifest.

Purpose:
  Turn interval-backed finite certificate blocks into manifest rows.

Each row records:
  - family/block parameters
  - midpoint/radius CSV paths and SHA256 hashes
  - penalty-guard taus
  - Dtheta/Rkappa safe lower bounds
  - pass/fail status

This is not a new sweep.  It is the registry layer needed before a directed
certificate family / exhaustion theorem can talk about finite blocks.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import numpy as np

from q3_psdpd_step18_interval_guard import (
    D_radius,
    D_theta,
    RadiusPack,
    R_kappa,
    R_radius,
    eig_min,
    make_tau_grid,
    qTq_radius,
    q_penalty,
    spectral_norm_nonnegative_radius,
)
from q3_psdpd_step13_pilot import sym


DEFAULT_MID_K11 = "q3.lean.aristotle/docs/insights/q3_psdpd_step22_midpoints_k11.csv"
DEFAULT_RAD_K11 = "q3.lean.aristotle/docs/insights/q3_psdpd_step22_radii_k11.csv"
DEFAULT_MID_K9 = "q3.lean.aristotle/docs/insights/q3_psdpd_step22_midpoints_k9.csv"
DEFAULT_RAD_K9 = "q3.lean.aristotle/docs/insights/q3_psdpd_step22_radii_k9.csv"


@dataclass(frozen=True)
class Candidate:
    family_id: str
    block_id: str
    L: float
    ell: float
    delta: float
    k_spline: int
    kappa: float
    theta: float
    arch_tmax: float
    arch_nt: int
    p0_na: int
    midpoint_csv: str
    radius_csv: str
    source_step: str
    notes: str = ""


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_matrix_csv(path: Path, value_col: str) -> dict[str, np.ndarray]:
    raw: dict[str, dict[tuple[int, int], float]] = {}
    shapes: dict[str, tuple[int, int]] = {}

    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row["matrix"].strip()
            i = int(row["i"])
            j = int(row["j"])
            value = float(row[value_col])

            raw.setdefault(name, {})[(i, j)] = value
            n_old, m_old = shapes.get(name, (0, 0))
            shapes[name] = (max(n_old, i + 1), max(m_old, j + 1))

    out: dict[str, np.ndarray] = {}
    for name, entries in raw.items():
        n, m = shapes[name]
        M = np.zeros((n, m), dtype=float)
        for (i, j), value in entries.items():
            M[i, j] = value
        if name != "Q":
            M = sym(M)
        out[name] = M

    return out


def require_matrices(pack: dict[str, np.ndarray], path: Path, value_col: str) -> None:
    missing = [name for name in ["A", "P", "P0", "Q"] if name not in pack]
    if missing:
        raise ValueError(f"{path} missing {value_col} rows for: {', '.join(missing)}")


def default_candidates() -> list[Candidate]:
    return [
        Candidate(
            family_id="psdpd_step22_interval",
            block_id="k11_L3_ell030_delta025",
            L=3.0,
            ell=0.30,
            delta=0.25,
            k_spline=11,
            kappa=3.25,
            theta=1e-4,
            arch_tmax=260.0,
            arch_nt=48001,
            p0_na=24001,
            midpoint_csv=DEFAULT_MID_K11,
            radius_csv=DEFAULT_RAD_K11,
            source_step="Step22",
            notes="primary interval-backed finite block",
        ),
        Candidate(
            family_id="psdpd_step22_interval",
            block_id="k9_L3_ell030_delta025_control",
            L=3.0,
            ell=0.30,
            delta=0.25,
            k_spline=9,
            kappa=3.075,
            theta=1e-5,
            arch_tmax=260.0,
            arch_nt=48001,
            p0_na=24001,
            midpoint_csv=DEFAULT_MID_K9,
            radius_csv=DEFAULT_RAD_K9,
            source_step="Step22",
            notes="control interval-backed finite block",
        ),
    ]


def read_candidates_csv(path: Path) -> list[Candidate]:
    rows: list[Candidate] = []
    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(
                Candidate(
                    family_id=row["family_id"],
                    block_id=row["block_id"],
                    L=float(row["L"]),
                    ell=float(row["ell"]),
                    delta=float(row["delta"]),
                    k_spline=int(row["k_spline"]),
                    kappa=float(row["kappa"]),
                    theta=float(row["theta"]),
                    arch_tmax=float(row.get("arch_tmax", 260.0)),
                    arch_nt=int(row.get("arch_nt", 48001)),
                    p0_na=int(row.get("p0_na", 24001)),
                    midpoint_csv=row["midpoint_csv"],
                    radius_csv=row["radius_csv"],
                    source_step=row.get("source_step", ""),
                    notes=row.get("notes", ""),
                )
            )
    return rows


def best_penalty(
    M_mid: np.ndarray,
    M_rad: np.ndarray,
    QTQ_mid: np.ndarray,
    QTQ_rad: np.ndarray,
    taus: list[float],
) -> dict[str, float]:
    best = {
        "tau": float("nan"),
        "lambda_mid": -math.inf,
        "err_norm": math.inf,
        "safe_lower": -math.inf,
    }

    for tau in taus:
        Mid = sym(M_mid + tau * QTQ_mid)
        Rad = np.maximum(M_rad + abs(tau) * QTQ_rad, 0.0)

        lam = eig_min(Mid)
        err = spectral_norm_nonnegative_radius(Rad)
        safe = lam - err

        if safe > best["safe_lower"]:
            best = {
                "tau": float(tau),
                "lambda_mid": float(lam),
                "err_norm": float(err),
                "safe_lower": float(safe),
            }

    return best


def matrix_norms(rp: RadiusPack) -> dict[str, float]:
    return {
        "rad_A_norm2": spectral_norm_nonnegative_radius(rp.A),
        "rad_P_norm2": spectral_norm_nonnegative_radius(rp.P),
        "rad_P0_norm2": spectral_norm_nonnegative_radius(rp.P0),
        "rad_Q_norm2": spectral_norm_nonnegative_radius(rp.Q),
        "rad_A_max": float(np.max(np.abs(rp.A))),
        "rad_P_max": float(np.max(np.abs(rp.P))),
        "rad_P0_max": float(np.max(np.abs(rp.P0))),
        "rad_Q_max": float(np.max(np.abs(rp.Q))),
    }


def certify_candidate(candidate: Candidate, tau_grid: str, repo_root: Path) -> dict[str, Any]:
    mid_path = repo_root / candidate.midpoint_csv
    rad_path = repo_root / candidate.radius_csv

    mids = read_matrix_csv(mid_path, value_col="mid")
    rads = read_matrix_csv(rad_path, value_col="rad")
    require_matrices(mids, mid_path, "mid")
    require_matrices(rads, rad_path, "rad")

    A = mids["A"]
    P = mids["P"]
    P0 = mids["P0"]
    Q = mids["Q"]
    QTQ = q_penalty(Q)

    rp = RadiusPack(A=rads["A"], P=rads["P"], P0=rads["P0"], Q=rads["Q"])

    Dmid = D_theta(A, P, P0, candidate.kappa, candidate.theta)
    Rmid = R_kappa(A, P0, candidate.kappa)
    QTQrad = qTq_radius(Q, rp.Q)
    Drad = D_radius(rp, candidate.kappa, candidate.theta)
    Rrad = R_radius(rp, candidate.kappa)

    taus = make_tau_grid(tau_grid)
    d_cert = best_penalty(Dmid, Drad, QTQ, QTQrad, taus)
    r_cert = best_penalty(Rmid, Rrad, QTQ, QTQrad, taus)

    n_centers = Q.shape[1]
    q_rank = int(np.linalg.matrix_rank(Q))
    dim_boundary_null = n_centers - q_rank
    status = "pass" if d_cert["safe_lower"] > 0.0 and r_cert["safe_lower"] > 0.0 else "fail"

    row: dict[str, Any] = {
        "family_id": candidate.family_id,
        "block_id": candidate.block_id,
        "status": status,
        "source_step": candidate.source_step,
        "L": candidate.L,
        "ell": candidate.ell,
        "delta": candidate.delta,
        "k_spline": candidate.k_spline,
        "kappa": candidate.kappa,
        "theta": candidate.theta,
        "arch_tmax": candidate.arch_tmax,
        "arch_nt": candidate.arch_nt,
        "p0_na": candidate.p0_na,
        "n_centers": n_centers,
        "q_rank": q_rank,
        "dim_boundary_null": dim_boundary_null,
        "midpoint_csv": candidate.midpoint_csv,
        "radius_csv": candidate.radius_csv,
        "midpoint_sha256": sha256_file(mid_path),
        "radius_sha256": sha256_file(rad_path),
        "tau_grid": tau_grid,
        "Dtheta_tau": d_cert["tau"],
        "Dtheta_lambda_mid": d_cert["lambda_mid"],
        "Dtheta_err_norm": d_cert["err_norm"],
        "Dtheta_safe_lower": d_cert["safe_lower"],
        "Rkappa_tau": r_cert["tau"],
        "Rkappa_lambda_mid": r_cert["lambda_mid"],
        "Rkappa_err_norm": r_cert["err_norm"],
        "Rkappa_safe_lower": r_cert["safe_lower"],
        "notes": candidate.notes,
    }
    row.update(matrix_norms(rp))
    return row


def write_manifest(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        raise ValueError("No manifest rows to write.")

    fields = list(rows[0].keys())
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def print_summary(rows: list[dict[str, Any]]) -> None:
    print("\n== Step 25 certificate manifest ==")
    print("block_id                         status  k   ell    theta      D_safe        R_safe")
    for row in rows:
        print(
            f"{row['block_id']:<32} "
            f"{row['status']:<6} "
            f"{int(row['k_spline']):2d}  "
            f"{float(row['ell']):5.3f}  "
            f"{float(row['theta']):.1e}  "
            f"{float(row['Dtheta_safe_lower']): .6e}  "
            f"{float(row['Rkappa_safe_lower']): .6e}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--candidates-csv",
        type=str,
        default="",
        help="Optional candidate rows. If omitted, uses the Step 22 k=11 and k=9 blocks.",
    )
    parser.add_argument(
        "--tau-grid",
        type=str,
        default="log:-8:8:161",
        help="Tau search grid, same format as Step 18.",
    )
    parser.add_argument(
        "--out",
        type=str,
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step25_certificate_manifest.csv",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    repo_root = Path.cwd()

    if args.candidates_csv:
        candidates = read_candidates_csv(repo_root / args.candidates_csv)
    else:
        candidates = default_candidates()

    rows = [certify_candidate(c, args.tau_grid, repo_root) for c in candidates]
    write_manifest(repo_root / args.out, rows)
    print_summary(rows)
    print(f"\nWrote manifest: {args.out}")


if __name__ == "__main__":
    main()
