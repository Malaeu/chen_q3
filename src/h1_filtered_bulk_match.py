#!/usr/bin/env python3
r"""
Numerical filtered-bulk check for the direct H1^f bridge.

We compare the filtered Suzuki blocks

    M_{mn}^{σ τ}(a)
      = w_{eps_σ m, eps_τ n}(a)
      + w_{eps_σ (m+1), eps_τ n}(a)
      + w_{eps_σ m, eps_τ (n+1)}(a)
      + w_{eps_σ (m+1), eps_τ (n+1)}(a)

against the filtered Q3 blocks

    \tilde q_{mn}^{σ τ}
      = q_{eps_σ m, eps_τ n}
      + q_{eps_σ (m+1), eps_τ n}
      + q_{eps_σ m, eps_τ (n+1)}
      + q_{eps_σ (m+1), eps_τ (n+1)}.

The live H1^f target is the direct filtered bulk match on the two primary
families:

    (++): M_{mn}^{++}(a) = kappa(a) \tilde q_{mn}^{++}
    (+-): M_{mn}^{+-}(a) = kappa(a) \tilde q_{mn}^{+-}

The remaining filtered blocks are formal Hermitian consequences.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

from h1_raw_bulk_match import (
    QConvention,
    WConvention,
    fit_kappa,
    q_conventions,
    q_rs,
    residual_metrics,
    w_conventions,
    w_rs,
)
from h1_raw_operator_sanity import active_prime_nodes, arch_coefficients
import mpmath as mp
import numpy as np


EPSILON = {"+": +1, "-": -1}


@dataclass(frozen=True)
class FilteredSample:
    family: str
    m: int
    n: int
    q: complex
    w: complex


def filtered_block_q(
    m: int,
    n: int,
    sigma: str,
    tau: str,
    A: dict[int, complex],
    nodes,
    q_convention: QConvention,
) -> complex:
    eps_sigma = EPSILON[sigma]
    eps_tau = EPSILON[tau]
    return (
        q_rs(eps_sigma * m, eps_tau * n, A, nodes, q_convention)
        + q_rs(eps_sigma * (m + 1), eps_tau * n, A, nodes, q_convention)
        + q_rs(eps_sigma * m, eps_tau * (n + 1), A, nodes, q_convention)
        + q_rs(eps_sigma * (m + 1), eps_tau * (n + 1), A, nodes, q_convention)
    )


def filtered_block_w(
    a: float,
    m: int,
    n: int,
    sigma: str,
    tau: str,
    zeros: int,
    w_convention: WConvention,
) -> complex:
    eps_sigma = EPSILON[sigma]
    eps_tau = EPSILON[tau]
    return (
        w_rs(a, eps_sigma * m, eps_tau * n, zeros, w_convention)
        + w_rs(a, eps_sigma * (m + 1), eps_tau * n, zeros, w_convention)
        + w_rs(a, eps_sigma * m, eps_tau * (n + 1), zeros, w_convention)
        + w_rs(a, eps_sigma * (m + 1), eps_tau * (n + 1), zeros, w_convention)
    )


def collect_filtered_samples(
    M: int,
    a: float,
    A: dict[int, complex],
    nodes,
    zeros: int,
    q_convention: QConvention,
    w_convention: WConvention,
) -> list[FilteredSample]:
    samples: list[FilteredSample] = []
    for m in range(1, M + 1):
        for n in range(1, M + 1):
            samples.append(
                FilteredSample(
                    "++",
                    m,
                    n,
                    filtered_block_q(m, n, "+", "+", A, nodes, q_convention),
                    filtered_block_w(a, m, n, "+", "+", zeros, w_convention),
                )
            )
            samples.append(
                FilteredSample(
                    "+-",
                    m,
                    n,
                    filtered_block_q(m, n, "+", "-", A, nodes, q_convention),
                    filtered_block_w(a, m, n, "+", "-", zeros, w_convention),
                )
            )
    return samples


def print_family_report(samples: list[FilteredSample], family: str) -> None:
    family_samples = [sample for sample in samples if sample.family == family]
    proxy = [type("Sample", (), {"q": s.q, "w": s.w}) for s in family_samples]
    kappa = fit_kappa(proxy)
    metrics = residual_metrics(proxy, kappa)
    print(f"[{family}]")
    print(f"  fitted kappa:           {kappa.real:.12e}  + {kappa.imag:.12e}i")
    print(f"  max |residual|:         {metrics['max_abs_residual']:.3e}")
    print(f"  RMS residual:           {metrics['rms_residual']:.3e}")
    print(f"  relative max residual:  {metrics['relative_max_residual']:.3e}")


def search_conventions(
    M: int,
    a: float,
    A: dict[int, complex],
    nodes,
    zeros: int,
) -> list[tuple[float, str, str, complex, dict[str, float]]]:
    results = []
    for q_conv in q_conventions():
        for w_conv in w_conventions():
            samples = collect_filtered_samples(M, a, A, nodes, zeros, q_conv, w_conv)
            proxy = [type("Sample", (), {"q": s.q, "w": s.w}) for s in samples]
            kappa = fit_kappa(proxy)
            metrics = residual_metrics(proxy, kappa)
            results.append((metrics["relative_max_residual"], q_conv.name, w_conv.name, kappa, metrics))
    results.sort(key=lambda item: item[0])
    return results


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Numerically test the filtered H1^f bulk identities.")
    parser.add_argument("--a", type=float, default=1.0, help="Suzuki interval parameter a > 0.")
    parser.add_argument("--M", type=int, default=3, help="Use filtered indices m,n in {1,...,M}.")
    parser.add_argument("--B", type=float, default=0.2, help="Compact prime window parameter B.")
    parser.add_argument("--t", type=float, default=0.15, help="Heat parameter t.")
    parser.add_argument("--zeros", type=int, default=50, help="Number of positive zeta zeros to use.")
    parser.add_argument("--grid-size", type=int, default=20001, help="Integration grid size for A_k.")
    parser.add_argument("--dps", type=int, default=80, help="mpmath precision in decimal digits.")
    parser.add_argument(
        "--search-conventions",
        action="store_true",
        help="Search the lightweight sign/index/conjugation conventions after filtering.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.a <= 0 or args.M <= 0 or args.B <= 0 or args.t <= 0 or args.zeros <= 0:
        raise SystemExit("Need a, M, B, t, and zeros to be positive.")

    mp.mp.dps = args.dps
    nodes = active_prime_nodes(args.B, args.t)
    A = arch_coefficients(args.B, args.t, max_k=2 * args.M + 2, grid_size=args.grid_size)

    print("H1 filtered-bulk match check")
    print("============================")
    print(f"a={args.a}  M={args.M}  B={args.B}  t={args.t}  zeros={args.zeros}  dps={args.dps}")
    print(f"active prime nodes: {len(nodes)}")

    baseline_q = q_conventions()[0]
    baseline_w = w_conventions()[0]
    samples = collect_filtered_samples(args.M, args.a, A, nodes, args.zeros, baseline_q, baseline_w)
    print(f"baseline conventions: {baseline_q.name} vs {baseline_w.name}")
    print_family_report(samples, "++")
    print_family_report(samples, "+-")

    proxy = [type("Sample", (), {"q": s.q, "w": s.w}) for s in samples]
    joint_kappa = fit_kappa(proxy)
    joint_metrics = residual_metrics(proxy, joint_kappa)
    print("[joint]")
    print(f"  fitted kappa:           {joint_kappa.real:.12e}  + {joint_kappa.imag:.12e}i")
    print(f"  max |residual|:         {joint_metrics['max_abs_residual']:.3e}")
    print(f"  RMS residual:           {joint_metrics['rms_residual']:.3e}")
    print(f"  relative max residual:  {joint_metrics['relative_max_residual']:.3e}")

    if args.search_conventions:
        print("\nconvention search")
        print("-----------------")
        for rel_res, q_name, w_name, kappa, metrics in search_conventions(args.M, args.a, A, nodes, args.zeros)[:8]:
            print(
                f"{q_name:18s} vs {w_name:14s}  "
                f"rel={rel_res:.3e}  "
                f"max={metrics['max_abs_residual']:.3e}  "
                f"kappa={kappa.real:.6e}+{kappa.imag:.6e}i"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
