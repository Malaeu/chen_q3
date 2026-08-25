#!/usr/bin/env python3
"""Numerical probe of the four W5 budget components.

Diagnostic only.  Nothing here is a proof and nothing here enters a Lean
statement: the probe exists so that a claim about growth can be reproduced or
refuted by anyone, instead of living in a chat message.

The object probed is the additive-log representative

    rep_k(x) = sqrt(u) * SUM_n H(n * u),      u = e^x / lambda_k,

with the exact CCM limit target

    H(y) = (pi/2) * y^2 * (2*pi*y^2 - 3) * exp(-pi*y^2)

standing in for the production packet, which F72.6 approximates uniformly on
the window.  The active indices are cut by the window: only n with
n * u <= lambda_k contribute, because the packet vanishes outside.

WHY THE SIGN MATTERS
--------------------
On 2026-08-25 this probe was first written with the modulus inside the sum,
SUM_n |H(n*u)|, and reported L1 growing like (k+2)^(1/4).  That was wrong.
E_star carries the modulus outside: |SUM_n H(n*u)|.  The target has zero mass,
so the terms cancel almost entirely and the true L1 is constant.  The judge
caught the error from the shape of the claim before the numbers were rechecked.

The `--wrong-way` flag reproduces the broken variant on purpose, so the size of
the difference stays visible and the mistake stays documented.
"""

from __future__ import annotations

import argparse
import math

PI = math.pi


def target(y: float) -> float:
    """The literal CCM limit packet of Eq. (7.1)."""
    return (PI / 2) * y * y * (2 * PI * y * y - 3) * math.exp(-PI * y * y)


def target_derivative(y: float) -> float:
    poly = (PI / 2) * (2 * PI * y**4 - 3 * y * y)
    dpoly = (PI / 2) * (8 * PI * y**3 - 6 * y)
    return (dpoly - 2 * PI * y * poly) * math.exp(-PI * y * y)


def comb(u: float, lam: float, *, wrong_way: bool, weight_index: bool = False) -> float:
    """Sum the target over the active indices at multiplicative coordinate `u`.

    Returns the signed sum.  Callers take the modulus themselves, after any
    combination — taking it here would destroy the very cancellation being
    measured.  `wrong_way` puts the modulus inside the sum instead, which is the
    documented error.  `weight_index` multiplies each term by `n`, which is what
    the chain rule produces for the derivative budget.
    """
    total = 0.0
    n = 1
    while n * u <= lam:
        term = target_derivative(n * u) * n if weight_index else target(n * u)
        total += abs(term) if wrong_way else term
        n += 1
        if n > 500_000:
            break
    return total


def l1_mass(k: int, steps: int, *, wrong_way: bool) -> float:
    lam = math.sqrt(k + 2)
    length = math.log(k + 2)
    total = 0.0
    for i in range(steps):
        x = length * (i + 0.5) / steps
        u = math.exp(x) / lam
        total += math.sqrt(u) * abs(comb(u, lam, wrong_way=wrong_way)) * (length / steps)
    return total


def derivative_budget(k: int, steps: int, *, wrong_way: bool) -> float:
    lam = math.sqrt(k + 2)
    length = math.log(k + 2)
    total = 0.0
    for i in range(steps):
        x = length * (i + 0.5) / steps
        u = math.exp(x) / lam
        value = comb(u, lam, wrong_way=wrong_way)
        slope = comb(u, lam, wrong_way=wrong_way, weight_index=True)
        total += abs(u * (value / (2 * math.sqrt(u)) + math.sqrt(u) * slope)) * (
            length / steps
        )
    return total


def endpoints(k: int, *, wrong_way: bool) -> tuple[float, float]:
    lam = math.sqrt(k + 2)
    length = math.log(k + 2)
    lower = math.sqrt(1 / lam) * abs(comb(1 / lam, lam, wrong_way=wrong_way))
    upper_u = math.exp(length) / lam
    upper = math.sqrt(upper_u) * abs(comb(upper_u, lam, wrong_way=wrong_way))
    return lower, upper


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--wrong-way",
        action="store_true",
        help="reproduce the 2026-08-25 error: modulus inside the sum",
    )
    parser.add_argument("--steps", type=int, default=800)
    parser.add_argument(
        "--k", type=int, nargs="*", default=[1000, 10000, 100000, 1000000]
    )
    args = parser.parse_args()

    if args.wrong_way:
        print("MODE: broken variant, modulus inside the sum — diagnostic only\n")

    mass = math.fsum(
        target(-6.0 + (12.0 / 200_000) * (i + 0.5)) for i in range(200_000)
    ) * (12.0 / 200_000)
    print(f"target mass  integral H = {mass:.3e}   (zero mass drives the cancellation)")
    print()
    print(f"{'k':>9}  {'L1':>13}  {'Derivative':>13}  {'Endpoint0':>13}  {'EndpointL':>13}")
    for k in args.k:
        low, high = endpoints(k, wrong_way=args.wrong_way)
        print(
            f"{k:>9}  {l1_mass(k, args.steps, wrong_way=args.wrong_way):>13.6e}  "
            f"{derivative_budget(k, args.steps, wrong_way=args.wrong_way):>13.6e}  "
            f"{low:>13.6e}  {high:>13.6e}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
