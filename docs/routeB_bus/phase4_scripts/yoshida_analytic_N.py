#!/usr/bin/env python3
"""Аналитическая оценка N из Yoshida [33, Lemma 3] для нашей ячейки, против измеренного R.

Цепочка констант (Yoshida 1992, стр. 287-288, разбор в
`litreview/YOSHIDA_HERMITIAN_1992_USAGE_CARDS.md`):

    C₁(a)  = (1/2a)·∫_{−2a}^{2a} (e^{x/2} + e^{−x/2}) dx = 4·sinh(a)/a
    C₂(a)  = |{ (p, m) : m·log p ≤ 2a }|                  ← счётчик простых степеней
    C      > µ + C₁(a₀) + 2C₂(a₀)                          при r₁=1, r₂=0, log A_k=0 (поле ℚ)
    t₀     : Re ψ(1/4 + it/2) ≥ C и Re ψ(1/2 + it) ≥ C при |t| ≥ t₀
    C₀     = max_{|t| ≤ t₀} |Re ψ(1/4 + it/2)|
    C₃     = (C₀ + C)·(1/2π)·∫_{|t| ≤ t₀} 2a₀(1 + a₀|t|)² dt
    N      : C₃·Σ_{|n| > N} (1/πn)² < запас над µ

Последнее условие и даёт N, поскольку Σ_{|n|>N} n⁻² ≤ 2/N.

Цель прогона — сравнить это N с измеренным `R(μ=1) = 70` (Phase 4, R1) и увидеть, годится
ли аналитическая граница как рабочая константа или только как доказательство существования.

Read-only diagnostic. Нормализация хвоста визуально сверена с печатной
p. 291 на 2026-08-11. Поиск `t₀`, максимум `C₀` и итоговый `N` не являются
интервальными сертификатами и не могут переноситься в Lean как доказанные границы.
"""
from __future__ import annotations

import argparse
from mpmath import mp, mpf, sinh, log, digamma, mpc, re as mre, quad, exp


def C1(a):
    """(1/2a)·∫_{−2a}^{2a}(e^{x/2}+e^{−x/2})dx = 4·sinh(a)/a — взято аналитически."""
    return 4 * sinh(a) / a


def C2(a, verbose=False):
    """|{(p,m) : m·log p ≤ 2a}| для поля ℚ, то есть число простых степеней p^m ≤ e^{2a}."""
    limit = exp(2 * a)
    pairs = []
    p = 2
    while p <= limit:
        is_prime = all(p % q for q in range(2, int(p ** 0.5) + 1))
        if is_prime:
            m, val = 1, p
            while val <= limit:
                pairs.append((p, m, val))
                m += 1
                val = p ** m
        p += 1
    if verbose:
        print("     пары (p, m, p^m):", ", ".join(f"({p},{m},{v})" for p, m, v in pairs))
    return len(pairs), pairs


def find_t0(C, lo=mpf(1), hi=mpf(10) ** 60):
    """Наименьший t₀, после которого обе Re ψ не ниже C. Re ψ(σ+it) ~ log|t| — растёт."""
    def ok(t):
        return (mre(digamma(mpc(mpf(1) / 4, t / 2))) >= C and
                mre(digamma(mpc(mpf(1) / 2, t))) >= C)
    if ok(lo):
        return lo
    while not ok(hi):
        hi *= 10
    for _ in range(200):
        mid = (lo + hi) / 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=13, help="ячейка")
    ap.add_argument("--mu", type=float, default=1.0)
    ap.add_argument("--dps", type=int, default=40)
    ap.add_argument("--margin", type=float, default=1.0,
                    help="во сколько раз C берётся выше порога")
    args = ap.parse_args()
    mp.dps = args.dps

    a0 = log(args.m) / 2          # centered half-length = log(sqrt(m))
    mu = mpf(args.mu)

    print(f"Yoshida [33, Lemma 3] — аналитическое N для m={args.m}, μ={args.mu}")
    print(f"  a₀ = log(√{args.m}) = {mp.nstr(a0, 12)}")
    print(f"  поле ℚ: r₁ = 1, r₂ = 0, log A_k = 0")
    print()

    c1 = C1(a0)
    c2, pairs = C2(a0, verbose=True)
    print(f"  C₁(a₀) = 4·sinh(a₀)/a₀ = {mp.nstr(c1, 10)}")
    print(f"  C₂(a₀) = {c2}   (простых степеней ≤ {mp.nstr(exp(2*a0), 6)})")

    threshold = mu + c1 + 2 * c2
    C = threshold * mpf(args.margin) if args.margin > 1 else threshold + 1
    print(f"  порог: C > μ + C₁ + 2·C₂ = {mp.nstr(threshold, 10)}")
    print(f"  берём C = {mp.nstr(C, 10)},  запас над μ: {mp.nstr(C - threshold, 6)}")
    print()

    print("  ищу t₀ (Re ψ ≥ C на обеих прямых) …", flush=True)
    t0 = find_t0(C)
    print(f"  t₀ ≈ {mp.nstr(t0, 8)}")

    C0 = mre(digamma(mpc(mpf(1) / 4, t0 / 2)))
    print(f"  C₀ ≈ {mp.nstr(C0, 8)}")

    # Paper p.291: ∫_{|t|≤t₀} 2a₀(1+a₀|t|)²dt
    # = (4/3)·((1+a₀t₀)³ − 1).
    integral = mpf(4) / 3 * ((1 + a0 * t0) ** 3 - 1)
    C3 = (C0 + C) * integral / (2 * mp.pi)
    print(f"  ∫_{{|t|≤t₀}}2a₀(1+a₀|t|)²dt = {mp.nstr(integral, 8)}")
    print(f"  C₃ = {mp.nstr(C3, 8)}")
    print()

    # C₃·π⁻²·(2/N) < запас  →  N > 2·C₃/(π²·запас)
    slack = C - threshold
    N = 2 * C3 / (mp.pi ** 2 * slack)
    print(f"  условие: C₃·Σ_{{|n|>N}}(1/πn)² < {mp.nstr(slack, 6)}")
    print(f"  Σ_{{|n|>N}} n⁻² ≤ 2/N")
    print()
    print(f"  N > {mp.nstr(N, 8)}")
    print()
    print(f"  измерено в Phase 4:  R(μ=1) = 70")
    print(f"  отношение аналитика/замер ≈ {mp.nstr(N / 70, 6)}")
    print()
    print("YOSHIDA_ANALYTIC_N=COMPUTED")
    print("CERTIFICATION=DIAGNOSTIC_ONLY_NOT_INTERVAL_NOT_LEAN")
    print()
    print("Оценка Yoshida доказывает существование N, а не даёт рабочую константу:")
    print("t₀ входит в C₃ кубически, а сам t₀ экспоненциален по C, поскольку Re ψ ~ log|t|.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
