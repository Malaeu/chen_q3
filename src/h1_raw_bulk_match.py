#!/usr/bin/env python3
r"""
Numerical raw-bulk check for the H1 Suzuki--Q3 bridge.

We compare the raw Suzuki/Weil entries

    w_rs(a) = (2/a) (-1)^(r+s) \sum_\gamma
              sin(a gamma)^2 / ((gamma - alpha_r)(gamma + alpha_s)),
    alpha_n = pi n / a,

against the raw Section 8 entries

    q_rs = A_{r-s} - \sum_{|\xi_n| <= B} lambda_n exp(2 pi i (s-r) xi_n),
    lambda_n = (2 Lambda(n) / sqrt(n)) Phi_{B,t}(xi_n),

on the two primary bulk families:

    (+,+): (r,s) = (m,n)
    (+,-): (r,s) = (m,-n)

The script estimates the best-fit scalar kappa(a) and reports residuals.
This is a fast numerical stress test of the remaining exact H1 brick.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np

from h1_raw_operator_sanity import active_prime_nodes, arch_coefficients


@dataclass(frozen=True)
class EntrySample:
    family: str
    r: int
    s: int
    q: complex
    w: complex


def q_rs(r: int, s: int, A: dict[int, complex], nodes) -> complex:
    return A[r - s] - sum(node.lam * np.exp(2j * np.pi * (s - r) * node.xi) for node in nodes)


def w_rs(a: float, r: int, s: int, zeros: int) -> complex:
    alpha_r = mp.pi * r / a
    alpha_s = mp.pi * s / a
    total = mp.mpc(0)
    for k in range(1, zeros + 1):
        gamma = mp.im(mp.zetazero(k))
        for ordinate in (gamma, -gamma):
            total += (mp.sin(a * ordinate) ** 2) / ((ordinate - alpha_r) * (ordinate + alpha_s))
    return complex((2 / a) * ((-1) ** (r + s)) * total)


def fit_kappa(samples: list[EntrySample]) -> complex:
    numer = sum(np.conjugate(sample.q) * sample.w for sample in samples)
    denom = sum(abs(sample.q) ** 2 for sample in samples)
    if denom == 0:
        raise ZeroDivisionError("Cannot fit kappa because all q entries vanish.")
    return numer / denom


def residual_metrics(samples: list[EntrySample], kappa: complex) -> dict[str, float]:
    residuals = [sample.w - kappa * sample.q for sample in samples]
    q_vals = [sample.q for sample in samples]
    w_vals = [sample.w for sample in samples]
    max_abs_res = max(abs(z) for z in residuals) if residuals else 0.0
    rms_res = math.sqrt(sum(abs(z) ** 2 for z in residuals) / len(residuals)) if residuals else 0.0
    scale = max(max((abs(z) for z in q_vals), default=0.0), max((abs(z) for z in w_vals), default=0.0), 1.0)
    return {
        "max_abs_residual": float(max_abs_res),
        "rms_residual": float(rms_res),
        "relative_max_residual": float(max_abs_res / scale),
    }


def collect_samples(M: int, a: float, A: dict[int, complex], nodes, zeros: int) -> list[EntrySample]:
    samples: list[EntrySample] = []
    for m in range(1, M + 1):
        for n in range(1, M + 1):
            samples.append(EntrySample("++", m, n, q_rs(m, n, A, nodes), w_rs(a, m, n, zeros)))
            samples.append(EntrySample("+-", m, -n, q_rs(m, -n, A, nodes), w_rs(a, m, -n, zeros)))
    return samples


def print_family_report(samples: list[EntrySample], family: str) -> None:
    family_samples = [sample for sample in samples if sample.family == family]
    kappa = fit_kappa(family_samples)
    metrics = residual_metrics(family_samples, kappa)
    print(f"[{family}]")
    print(f"  fitted kappa:           {kappa.real:.12e}  + {kappa.imag:.12e}i")
    print(f"  max |residual|:         {metrics['max_abs_residual']:.3e}")
    print(f"  RMS residual:           {metrics['rms_residual']:.3e}")
    print(f"  relative max residual:  {metrics['relative_max_residual']:.3e}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Numerically test the raw H1 bulk identity.")
    parser.add_argument("--a", type=float, default=1.0, help="Suzuki interval parameter a > 0.")
    parser.add_argument("--M", type=int, default=3, help="Use indices m,n in {1,...,M}.")
    parser.add_argument("--B", type=float, default=0.2, help="Compact prime window parameter B.")
    parser.add_argument("--t", type=float, default=0.15, help="Heat parameter t.")
    parser.add_argument("--zeros", type=int, default=50, help="Number of positive zeta zeros to use.")
    parser.add_argument("--grid-size", type=int, default=20001, help="Integration grid size for A_k.")
    parser.add_argument("--dps", type=int, default=80, help="mpmath precision in decimal digits.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.a <= 0 or args.M <= 0 or args.B <= 0 or args.t <= 0 or args.zeros <= 0:
        raise SystemExit("Need a, M, B, t, and zeros to be positive.")

    mp.mp.dps = args.dps
    nodes = active_prime_nodes(args.B, args.t)
    A = arch_coefficients(args.B, args.t, max_k=2 * args.M, grid_size=args.grid_size)
    samples = collect_samples(args.M, args.a, A, nodes, args.zeros)

    print("H1 raw-bulk match check")
    print("=======================")
    print(f"a={args.a}  M={args.M}  B={args.B}  t={args.t}  zeros={args.zeros}  dps={args.dps}")
    print(f"active prime nodes: {len(nodes)}")
    print_family_report(samples, "++")
    print_family_report(samples, "+-")

    joint_kappa = fit_kappa(samples)
    joint_metrics = residual_metrics(samples, joint_kappa)
    print("[joint]")
    print(f"  fitted kappa:           {joint_kappa.real:.12e}  + {joint_kappa.imag:.12e}i")
    print(f"  max |residual|:         {joint_metrics['max_abs_residual']:.3e}")
    print(f"  RMS residual:           {joint_metrics['rms_residual']:.3e}")
    print(f"  relative max residual:  {joint_metrics['relative_max_residual']:.3e}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
