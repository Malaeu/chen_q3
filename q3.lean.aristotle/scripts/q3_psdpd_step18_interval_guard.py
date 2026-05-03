#!/usr/bin/env python3
"""
Step 18 PSD-pd interval/drift guard.

Purpose:
  Certify the finite candidate without explicitly certifying the numerical
  nullspace basis N.

Main trick:
  If M = D_theta + tau Q^T Q is SPD on the full coordinate space,
  then D_theta is PSD on ker(Q).

Similarly:
  If R_kappa + tau Q^T Q is SPD, then R_kappa is positive on ker(Q).

Current modes:
  1. drift-guard mode:
       uses quadrature variants as empirical radius diagnostics.
       Not proof-grade, but checks certificate robustness.

  2. radius-csv mode:
       accepts entrywise radii for A, P, P0, Q from a future Arb/interval
       generator and performs a Weyl-style certified lower bound.

Notation:
  k_spline = B-spline degree
  r_pow    = prime-power exponent p^r_pow
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from q3_psdpd_step13_pilot import (
    PilotParams,
    SplinePacket,
    build_A,
    build_G,
    build_P,
    build_P0,
    build_Q,
    build_centers,
    sym,
)


def parse_quad_variants(text: str) -> list[tuple[float, int, int]]:
    out = []
    for raw in text.split(","):
        raw = raw.strip()
        if not raw:
            continue
        a, b, c = raw.split(":")
        out.append((float(a), int(b), int(c)))
    return out


def parse_float_list(text: str) -> list[float]:
    return [float(x.strip()) for x in text.split(",") if x.strip()]


def spectral_norm_nonnegative_radius(R: np.ndarray) -> float:
    """
    For an entrywise absolute error matrix R >= 0, ||R||_2 bounds
    the perturbation spectral norm.
    """
    if R.size == 0:
        return 0.0
    return float(np.linalg.norm(np.maximum(R, 0.0), ord=2))


def eig_min(M: np.ndarray) -> float:
    return float(np.linalg.eigvalsh(sym(M))[0])


def q_penalty(Q: np.ndarray) -> np.ndarray:
    return sym(Q.T @ Q)


def build_all(params: PilotParams) -> dict[str, np.ndarray]:
    packet = SplinePacket.build(params.k_spline)
    u = build_centers(params)
    D = u[:, None] - u[None, :]

    G = build_G(D, params, packet)
    A = build_A(D, params, packet)
    P, _shifts = build_P(D, params, packet)
    P0 = build_P0(D, params, packet)
    Q = build_Q(u)

    return {
        "G": sym(G),
        "A": sym(A),
        "P": sym(P),
        "P0": sym(P0),
        "Q": Q,
        "QTQ": q_penalty(Q),
    }


def D_theta(A: np.ndarray, P: np.ndarray, P0: np.ndarray, kappa: float, theta: float) -> np.ndarray:
    return sym((1.0 - theta) * A - P + theta * kappa * P0)


def R_kappa(A: np.ndarray, P0: np.ndarray, kappa: float) -> np.ndarray:
    return sym(A - kappa * P0)


def scan_tau(M: np.ndarray, QTQ: np.ndarray, taus: list[float]) -> tuple[float, float]:
    """Return tau with largest full-space min eigenvalue of M + tau Q^T Q."""
    best_tau = taus[0]
    best_lam = -math.inf
    for tau in taus:
        lam = eig_min(M + tau * QTQ)
        if lam > best_lam:
            best_tau = tau
            best_lam = lam
    return best_tau, best_lam


def make_tau_grid(text: str) -> list[float]:
    """
    Accept either:
      comma list: "0,1,2,4,8"
    or log grid:
      "log:-8:8:161"
    """
    text = text.strip()
    if text.startswith("log:"):
        _, a, b, n = text.split(":")
        return np.logspace(float(a), float(b), int(n)).tolist()
    return parse_float_list(text)


@dataclass
class RadiusPack:
    A: np.ndarray
    P: np.ndarray
    P0: np.ndarray
    Q: np.ndarray


def empty_radii_like(base: dict[str, np.ndarray]) -> RadiusPack:
    return RadiusPack(
        A=np.zeros_like(base["A"]),
        P=np.zeros_like(base["P"]),
        P0=np.zeros_like(base["P0"]),
        Q=np.zeros_like(base["Q"]),
    )


def load_radius_csv(path: Path, base: dict[str, np.ndarray]) -> RadiusPack:
    """
    Expected CSV rows:
      matrix,i,j,rad

    matrix in:
      A, P, P0, Q

    Indices are zero-based.
    """
    rp = empty_radii_like(base)

    if not path.exists():
        raise FileNotFoundError(path)
    if path.is_dir():
        raise IsADirectoryError(path)

    targets = {
        "A": rp.A,
        "P": rp.P,
        "P0": rp.P0,
        "Q": rp.Q,
    }

    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row["matrix"].strip()
            i = int(row["i"])
            j = int(row["j"])
            rad = float(row["rad"])

            if name not in targets:
                raise ValueError(f"Bad matrix name in radii CSV: {name}")

            M = targets[name]
            M[i, j] = max(M[i, j], abs(rad))

            if name != "Q" and i != j:
                M[j, i] = max(M[j, i], abs(rad))

    return rp


def load_midpoint_csv(path: Path, base: dict[str, np.ndarray]) -> None:
    """
    Optional midpoint override.

    Expected CSV rows:
      matrix,i,j,mid

    matrix in:
      A, P, P0, Q

    This mutates base in-place and recomputes QTQ if Q is changed.
    """
    if not path.exists():
        raise FileNotFoundError(path)
    if path.is_dir():
        raise IsADirectoryError(path)

    targets = {
        "A": base["A"],
        "P": base["P"],
        "P0": base["P0"],
        "Q": base["Q"],
    }

    touched_Q = False

    with path.open() as f:
        reader = csv.DictReader(f)
        for row in reader:
            name = row["matrix"].strip()
            i = int(row["i"])
            j = int(row["j"])
            mid = float(row["mid"])

            if name not in targets:
                raise ValueError(f"Bad matrix name in midpoint CSV: {name}")

            M = targets[name]
            M[i, j] = mid

            if name != "Q" and i != j:
                M[j, i] = mid

            if name == "Q":
                touched_Q = True

    base["A"] = sym(base["A"])
    base["P"] = sym(base["P"])
    base["P0"] = sym(base["P0"])

    if touched_Q:
        base["QTQ"] = q_penalty(base["Q"])


def qTq_radius(Q_mid: np.ndarray, Q_rad: np.ndarray) -> np.ndarray:
    """
    Entrywise radius bound for Q^T Q.

    For each entry:
      sum_k (q_ki +/- r_ki)(q_kj +/- r_kj)

    radius contribution:
      |q_ki| r_kj + |q_kj| r_ki + r_ki r_kj
    """
    n = Q_mid.shape[1]
    R = np.zeros((n, n), dtype=float)

    for i in range(n):
        for j in range(n):
            s = 0.0
            for k in range(Q_mid.shape[0]):
                qi = Q_mid[k, i]
                qj = Q_mid[k, j]
                ri = Q_rad[k, i]
                rj = Q_rad[k, j]
                s += abs(qi) * rj + abs(qj) * ri + ri * rj
            R[i, j] = s

    return sym(R)


def D_radius(rp: RadiusPack, kappa: float, theta: float) -> np.ndarray:
    return sym((1.0 - theta) * rp.A + rp.P + theta * abs(kappa) * rp.P0)


def R_radius(rp: RadiusPack, kappa: float) -> np.ndarray:
    return sym(rp.A + abs(kappa) * rp.P0)


def drift_radius_from_variants(
    base_params: PilotParams,
    variants: list[tuple[float, int, int]],
    base: dict[str, np.ndarray],
) -> RadiusPack:
    """
    Empirical max-entry drift across quadrature variants.
    Not proof-grade. Useful for sanity before real Arb radius CSV.
    """
    rp = empty_radii_like(base)

    for arch_tmax, arch_nt, p0_na in variants:
        params = PilotParams(
            L=base_params.L,
            ell=base_params.ell,
            delta=base_params.delta,
            k_spline=base_params.k_spline,
            arch_tmax=arch_tmax,
            arch_nt=arch_nt,
            p0_na=p0_na,
        )
        b = build_all(params)

        rp.A = np.maximum(rp.A, np.abs(b["A"] - base["A"]))
        rp.P = np.maximum(rp.P, np.abs(b["P"] - base["P"]))
        rp.P0 = np.maximum(rp.P0, np.abs(b["P0"] - base["P0"]))
        rp.Q = np.maximum(rp.Q, np.abs(b["Q"] - base["Q"]))

    return rp


def certify_full_space(
    name: str,
    M_mid: np.ndarray,
    M_rad: np.ndarray,
    QTQ_mid: np.ndarray,
    QTQ_rad: np.ndarray,
    taus: list[float],
) -> dict[str, float]:
    """
    Find best tau and compute:
      lambda_min(M_mid + tau QTQ_mid) - ||M_rad + tau QTQ_rad||_2
    """
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
                "tau": tau,
                "lambda_mid": lam,
                "err_norm": err,
                "safe_lower": safe,
            }

    print(f"\n== {name} penalty certificate ==")
    print(f"best_tau      = {best['tau']:.16e}")
    print(f"lambda_mid    = {best['lambda_mid']:.16e}")
    print(f"err_norm      = {best['err_norm']:.16e}")
    print(f"safe_lower    = {best['safe_lower']:.16e}")
    print(f"PASS          = {best['safe_lower'] > 0.0}")

    return best


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

    parser.add_argument(
        "--tau-grid",
        type=str,
        default="log:-8:8:161",
        help="Either comma list or log:start_exp:stop_exp:n, e.g. log:-8:8:161",
    )

    parser.add_argument(
        "--radius-csv",
        type=str,
        default="",
        help="Optional proof-grade entry radius CSV from Arb/interval generator.",
    )

    parser.add_argument(
        "--midpoint-csv",
        type=str,
        default="",
        help="Optional midpoint CSV with rows matrix,i,j,mid. Overrides internal float midpoints.",
    )

    parser.add_argument(
        "--mode",
        type=str,
        choices=["drift", "radius"],
        default="drift",
        help="drift = empirical quadrature drift; radius = use radius CSV.",
    )

    args = parser.parse_args()

    if args.mode == "radius" and not args.radius_csv:
        raise SystemExit("--radius-csv is required in radius mode")

    params = PilotParams(
        L=args.L,
        ell=args.ell,
        delta=args.delta,
        k_spline=args.k_spline,
        arch_tmax=args.arch_tmax,
        arch_nt=args.arch_nt,
        p0_na=args.p0_na,
    )

    print("== Step 18 interval/drift penalty guard ==")
    print(f"L={args.L}, ell={args.ell}, delta={args.delta}, k_spline={args.k_spline}")
    print(f"kappa={args.kappa}, theta={args.theta}")
    print(f"mode={args.mode}")
    if args.mode == "drift":
        print("[WARN] drift mode is not proof-grade. Use radius mode with Arb intervals for proof.")
    else:
        print("[INFO] radius mode uses the provided midpoint/radius CSV contract.")

    base = build_all(params)

    if args.midpoint_csv:
        load_midpoint_csv(Path(args.midpoint_csv), base)

    A = base["A"]
    P = base["P"]
    P0 = base["P0"]
    Q = base["Q"]
    QTQ = base["QTQ"]

    Dmid = D_theta(A, P, P0, args.kappa, args.theta)
    Rmid = R_kappa(A, P0, args.kappa)

    taus = make_tau_grid(args.tau_grid)

    tau_D_mid, lam_D_mid = scan_tau(Dmid, QTQ, taus)
    tau_R_mid, lam_R_mid = scan_tau(Rmid, QTQ, taus)

    print("\n== Midpoint tau scan ==")
    print(f"Dtheta best tau midpoint = {tau_D_mid:.16e}, lambda_min={lam_D_mid:.16e}")
    print(f"Rkappa best tau midpoint = {tau_R_mid:.16e}, lambda_min={lam_R_mid:.16e}")

    if args.mode == "drift":
        variants = parse_quad_variants(args.quad_variants)
        rp = drift_radius_from_variants(params, variants, base)
    else:
        rp = load_radius_csv(Path(args.radius_csv), base)

    QTQrad = qTq_radius(Q, rp.Q)
    Drad = D_radius(rp, args.kappa, args.theta)
    Rrad = R_radius(rp, args.kappa)

    print("\n== Radius diagnostics ==")
    print(f"||rad(A)||_2      = {spectral_norm_nonnegative_radius(rp.A):.16e}")
    print(f"||rad(P)||_2      = {spectral_norm_nonnegative_radius(rp.P):.16e}")
    print(f"||rad(P0)||_2     = {spectral_norm_nonnegative_radius(rp.P0):.16e}")
    print(f"||rad(QTQ)||_2    = {spectral_norm_nonnegative_radius(QTQrad):.16e}")
    print(f"||rad(Dtheta)||_2 = {spectral_norm_nonnegative_radius(Drad):.16e}")
    print(f"||rad(Rkappa)||_2 = {spectral_norm_nonnegative_radius(Rrad):.16e}")

    d_cert = certify_full_space(
        name="Dtheta = C - theta R_kappa",
        M_mid=Dmid,
        M_rad=Drad,
        QTQ_mid=QTQ,
        QTQ_rad=QTQrad,
        taus=taus,
    )

    r_cert = certify_full_space(
        name="R_kappa",
        M_mid=Rmid,
        M_rad=Rrad,
        QTQ_mid=QTQ,
        QTQ_rad=QTQrad,
        taus=taus,
    )

    print("\n== Final verdict ==")
    ok = d_cert["safe_lower"] > 0.0 and r_cert["safe_lower"] > 0.0
    if ok:
        print("PASS: penalty certificate proves Dtheta >= 0 and Rkappa > 0 on ker(Q).")
    else:
        print("FAIL/NOISY: need tighter intervals, better tau grid, or larger margin candidate.")


if __name__ == "__main__":
    run()
