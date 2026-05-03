#!/usr/bin/env python3
"""
Step 17 PSD-pd finite certificate extraction.

Goal:
  Turn the kappa-split numerical plateau into a finite certificate target.

For chosen parameters:
  C = A - P
  R_k = A - kappa P0
  S_k = P - kappa P0
  C = R_k - S_k

Checks:
  1. R_k^circ > 0
  2. D_theta^circ = C^circ - theta R_k^circ >= 0
     equivalently C^circ >= theta R_k^circ
  3. quadrature drift of R_k and D_theta across variants

This is still numerical drift-guard certification, not final interval proof.
Step 18 should replace quadrature drift by rigorous interval bounds.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from scipy import linalg

from q3_psdpd_step13_pilot import (
    PilotParams,
    SplinePacket,
    boundary_null_basis,
    build_A,
    build_G,
    build_P,
    build_P0,
    build_Q,
    build_centers,
    sym,
)


@dataclass(frozen=True)
class ReducedRaw:
    params: PilotParams
    Gc: np.ndarray
    Ac: np.ndarray
    Pc: np.ndarray
    P0c: np.ndarray
    N: np.ndarray
    q_resid: float


@dataclass(frozen=True)
class CertMatrices:
    params: PilotParams
    kappa: float
    theta: float
    Gc: np.ndarray
    Cc: np.ndarray
    Rkc: np.ndarray
    Skc: np.ndarray
    Dtc: np.ndarray
    eig_CG_min: float
    eig_RG_min: float
    eig_DG_min: float
    rel_max: float | None
    rel_margin: float | None
    q_resid: float
    split_err: float


def parse_quad_variants(text: str) -> list[tuple[float, int, int]]:
    variants = []
    for raw in text.split(","):
        raw = raw.strip()
        if not raw:
            continue
        a, b, c = raw.split(":")
        variants.append((float(a), int(b), int(c)))
    return variants


def frange(start: float, stop: float, step: float) -> list[float]:
    out = []
    x = start
    while x <= stop + 0.5 * step:
        out.append(float(x))
        x += step
    return out


def safe_eigh(A: np.ndarray, B: np.ndarray | None = None) -> np.ndarray:
    if B is None:
        return np.linalg.eigvalsh(sym(A))
    return linalg.eigh(sym(A), sym(B), eigvals_only=True)


def whitened(M: np.ndarray, G: np.ndarray) -> np.ndarray:
    """
    Return W = L^{-1} M L^{-T}, where G = L L^T.

    Eigenvalues of W equal generalized eigenvalues of (M,G).
    """
    L = linalg.cholesky(sym(G), lower=True)
    temp = linalg.solve_triangular(L, sym(M), lower=True)
    W = linalg.solve_triangular(L, temp.T, lower=True).T
    return sym(W)


def op_norm_relative(M: np.ndarray, G: np.ndarray) -> float:
    """Operator norm of M in G-whitened coordinates."""
    W = whitened(M, G)
    eig = np.linalg.eigvalsh(W)
    return float(np.max(np.abs(eig)))


def build_reduced_raw(params: PilotParams, N_override: np.ndarray | None = None) -> ReducedRaw:
    packet = SplinePacket.build(params.k_spline)

    centers = build_centers(params)
    D = centers[:, None] - centers[None, :]

    G = build_G(D, params, packet)
    A = build_A(D, params, packet)
    P, _shifts = build_P(D, params, packet)
    P0 = build_P0(D, params, packet)

    if N_override is None:
        Q = build_Q(centers)
        N = boundary_null_basis(Q)
    else:
        Q = build_Q(centers)
        N = N_override

    q_resid = float(np.linalg.norm(Q @ N, ord="fro"))

    return ReducedRaw(
        params=params,
        Gc=sym(N.T @ G @ N),
        Ac=sym(N.T @ A @ N),
        Pc=sym(N.T @ P @ N),
        P0c=sym(N.T @ P0 @ N),
        N=N,
        q_resid=q_resid,
    )


def cert_from_raw(raw: ReducedRaw, kappa: float, theta: float) -> CertMatrices:
    Cc = sym(raw.Ac - raw.Pc)
    Rkc = sym(raw.Ac - kappa * raw.P0c)
    Skc = sym(raw.Pc - kappa * raw.P0c)
    Dtc = sym(Cc - theta * Rkc)

    split_err = float(np.linalg.norm(Cc - sym(Rkc - Skc), ord="fro"))

    eig_CG = safe_eigh(Cc, raw.Gc)
    eig_RG = safe_eigh(Rkc, raw.Gc)
    eig_DG = safe_eigh(Dtc, raw.Gc)

    rel_max = None
    rel_margin = None
    if np.linalg.eigvalsh(Rkc)[0] > 1e-12:
        eig_rel = safe_eigh(Skc, Rkc)
        rel_max = float(eig_rel[-1])
        rel_margin = 1.0 - rel_max

    return CertMatrices(
        params=raw.params,
        kappa=kappa,
        theta=theta,
        Gc=raw.Gc,
        Cc=Cc,
        Rkc=Rkc,
        Skc=Skc,
        Dtc=Dtc,
        eig_CG_min=float(eig_CG[0]),
        eig_RG_min=float(eig_RG[0]),
        eig_DG_min=float(eig_DG[0]),
        rel_max=rel_max,
        rel_margin=rel_margin,
        q_resid=raw.q_resid,
        split_err=split_err,
    )


def build_cert_matrices(params: PilotParams, kappa: float, theta: float) -> CertMatrices:
    return cert_from_raw(build_reduced_raw(params), kappa=kappa, theta=theta)


def print_cert(label: str, cm: CertMatrices) -> None:
    p = cm.params
    print("\n" + "=" * 88)
    print(label)
    print("=" * 88)
    print(
        f"k_spline={p.k_spline}, ell={p.ell}, delta={p.delta}, "
        f"L={p.L}, kappa={cm.kappa}, theta={cm.theta}"
    )
    print(f"arch_tmax={p.arch_tmax}, arch_nt={p.arch_nt}, p0_na={p.p0_na}")
    print(f"eig_min(C,G)          = {cm.eig_CG_min:.16e}")
    print(f"eig_min(R_k,G)        = {cm.eig_RG_min:.16e}")
    print(f"eig_min(D_theta,G)    = {cm.eig_DG_min:.16e}")
    print(f"rel_max(S_k,R_k)      = {cm.rel_max}")
    print(f"rel_margin            = {cm.rel_margin}")
    print(f"||Q N||_F             = {cm.q_resid:.3e}")
    print(f"||C-(R-S)||_F         = {cm.split_err:.3e}")


def scan_kappa(
    raw: ReducedRaw,
    theta: float,
    kappa_start: float,
    kappa_stop: float,
    kappa_step: float,
) -> list[dict]:
    rows = []
    for kappa in frange(kappa_start, kappa_stop, kappa_step):
        cm = cert_from_raw(raw, kappa=kappa, theta=theta)
        rows.append(
            {
                "kappa": kappa,
                "theta": theta,
                "eig_CG_min": cm.eig_CG_min,
                "eig_RG_min": cm.eig_RG_min,
                "eig_DG_min": cm.eig_DG_min,
                "rel_max": cm.rel_max,
                "rel_margin": cm.rel_margin,
                "pass_Dtheta": cm.eig_DG_min > 0,
                "pass_R": cm.eig_RG_min > 0,
            }
        )
    return rows


def write_csv(path: Path, rows: list[dict]) -> None:
    if not rows:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0].keys()), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def run() -> None:
    parser = argparse.ArgumentParser()

    parser.add_argument("--L", type=float, default=3.0)
    parser.add_argument("--ell", type=float, default=0.30)
    parser.add_argument("--delta", type=float, default=0.25)
    parser.add_argument("--k-spline", type=int, default=11)

    parser.add_argument("--kappa", type=float, default=3.25)
    parser.add_argument("--theta", type=float, default=1e-4)

    parser.add_argument("--arch-tmax", type=float, default=260.0)
    parser.add_argument("--arch-nt", type=int, default=48001)
    parser.add_argument("--p0-na", type=int, default=24001)

    parser.add_argument(
        "--quad-variants",
        type=str,
        default="220:36001:18001,260:48001:24001,320:64001:32001",
    )

    parser.add_argument("--scan-kappa", action="store_true")
    parser.add_argument("--kappa-start", type=float, default=2.50)
    parser.add_argument("--kappa-stop", type=float, default=4.25)
    parser.add_argument("--kappa-step", type=float, default=0.025)

    parser.add_argument(
        "--csv",
        type=str,
        default="q3.lean.aristotle/docs/insights/q3_psdpd_step17_certificate_scan.csv",
    )

    args = parser.parse_args()

    base_params = PilotParams(
        L=args.L,
        ell=args.ell,
        delta=args.delta,
        k_spline=args.k_spline,
        arch_tmax=args.arch_tmax,
        arch_nt=args.arch_nt,
        p0_na=args.p0_na,
    )

    print("== Step 17 finite certificate extraction ==")
    print("[WARN] This is drift-guard numerical certification, not interval proof.")

    base_raw = build_reduced_raw(base_params)
    base = cert_from_raw(base_raw, kappa=args.kappa, theta=args.theta)
    print_cert("Base quadrature", base)

    if args.scan_kappa:
        rows = scan_kappa(
            raw=base_raw,
            theta=args.theta,
            kappa_start=args.kappa_start,
            kappa_stop=args.kappa_stop,
            kappa_step=args.kappa_step,
        )

        print("\n== Kappa scan for D_theta = C - theta R_k ==")
        print("kappa      eig_min(R,G)       eig_min(Dtheta,G)  rel_margin          pass")
        for row in rows:
            ok = row["pass_R"] and row["pass_Dtheta"]
            print(
                f"{row['kappa']:8.4f}  "
                f"{row['eig_RG_min']: .10e}  "
                f"{row['eig_DG_min']: .10e}  "
                f"{row['rel_margin']}  "
                f"{ok}"
            )

        write_csv(Path(args.csv), rows)
        print(f"\nWrote kappa scan CSV: {args.csv}")

    print("\n== Quadrature drift guard ==")
    variants = parse_quad_variants(args.quad_variants)

    max_R_drift = 0.0
    max_D_drift = 0.0
    max_C_drift = 0.0

    for arch_tmax, arch_nt, p0_na in variants:
        params = PilotParams(
            L=args.L,
            ell=args.ell,
            delta=args.delta,
            k_spline=args.k_spline,
            arch_tmax=arch_tmax,
            arch_nt=arch_nt,
            p0_na=p0_na,
        )

        raw = build_reduced_raw(params, N_override=base_raw.N)
        cm = cert_from_raw(raw, kappa=args.kappa, theta=args.theta)

        dR = op_norm_relative(cm.Rkc - base.Rkc, base.Gc)
        dD = op_norm_relative(cm.Dtc - base.Dtc, base.Gc)
        dC = op_norm_relative(cm.Cc - base.Cc, base.Gc)

        max_R_drift = max(max_R_drift, dR)
        max_D_drift = max(max_D_drift, dD)
        max_C_drift = max(max_C_drift, dC)

        print(
            f"{arch_tmax:7.1f} {arch_nt:7d} {p0_na:7d}  "
            f"eigD={cm.eig_DG_min:.16e}  "
            f"eigR={cm.eig_RG_min:.16e}  "
            f"margin={cm.rel_margin}  "
            f"dD={dD:.3e} dR={dR:.3e} dC={dC:.3e}"
        )

    safe_R = base.eig_RG_min - max_R_drift
    safe_D = base.eig_DG_min - max_D_drift
    safe_C = base.eig_CG_min - max_C_drift

    print("\n== Drift-guard summary ==")
    print(f"base eig_min(R,G)       = {base.eig_RG_min:.16e}")
    print(f"max R drift             = {max_R_drift:.16e}")
    print(f"safe R lower            = {safe_R:.16e}")
    print(f"base eig_min(Dtheta,G)  = {base.eig_DG_min:.16e}")
    print(f"max Dtheta drift        = {max_D_drift:.16e}")
    print(f"safe Dtheta lower       = {safe_D:.16e}")
    print(f"base eig_min(C,G)       = {base.eig_CG_min:.16e}")
    print(f"max C drift             = {max_C_drift:.16e}")
    print(f"safe C lower            = {safe_C:.16e}")

    print("\nVerdict:")
    if safe_R > 0 and safe_D > 0:
        print("PASS drift-guard: R_k and D_theta remain positive under tested quadrature variants.")
    else:
        print("FAIL/NOISY drift-guard: increase margin, reduce theta, or improve quadrature.")


if __name__ == "__main__":
    run()
