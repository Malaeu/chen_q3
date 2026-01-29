#!/usr/bin/env python3
"""
Prime-term certificate over a B-range at t_critical (single-scale, tau = 0).

We bound:
  prime_term(phi_shift_critical B 0) <= arch_term(phi_shift_critical B 0)
for B in [B_MIN, B_MAX], by a grid+Lipschitz certificate on the margin:
  margin(B) = arch_term(B) - prime_upper_bound(B).

Outputs a timestamped report in output/.
"""

import math
import time
from datetime import datetime

import mpmath as mp

# Parameters
B_MIN = 3.0
B_MAX = 4.9
B_H = 0.1
T_CRITICAL = 3.0 / 20.0  # 0.15
TAU = 0.0
N = 1_000_000

PI = math.pi

# --- Definitions matching Lean ---

def xi_n(n: int) -> float:
    return math.log(n) / (2 * PI)

# a_star via digamma
mp.mp.dps = 50

def a_star(xi: float) -> mp.mpf:
    z = mp.mpf('0.25') + 1j * mp.pi * mp.mpf(xi)
    val = mp.log(mp.pi) - mp.re(mp.digamma(z))
    return 2 * mp.pi * val

# --- Prime sum over prime powers ---

def sieve_primes(limit: int):
    is_prime = bytearray(b"\x01") * (limit + 1)
    is_prime[0:2] = b"\x00\x00"
    for p in range(2, int(limit ** 0.5) + 1):
        if is_prime[p]:
            start = p * p
            step = p
            is_prime[start:limit + 1:step] = b"\x00" * (((limit - start) // step) + 1)
    return [i for i in range(2, limit + 1) if is_prime[i]]


def precompute_prime_powers(N: int):
    primes = sieve_primes(N)
    entries = []
    for p in primes:
        logp = math.log(p)
        pk = p
        while pk <= N:
            xi = xi_n(pk)
            w_q = 2.0 * logp / math.sqrt(pk)
            heat = math.exp(-4 * PI * PI * T_CRITICAL * xi * xi)
            entries.append((xi, w_q, heat))
            pk *= p
    return entries, len(primes)


# Tail bound using Lambda(n) <= log n and phi <= exp(-t (log n)^2)
# Sum_{n>N} 2 log n / sqrt n * exp(-t (log n)^2) <= integral from N to inf.

def tail_bound(N: int) -> mp.mpf:
    u0 = mp.log(N)
    # change of variables: x = e^u
    # integrand: 2*u*exp(-t*u^2 + u/2)
    f = lambda u: 2 * u * mp.e**(-T_CRITICAL * u * u + u / 2)
    return mp.quad(f, [u0, mp.inf])

# Arch term integral

def arch_term_numeric(B: float) -> mp.mpf:
    # integrand is even for tau=0, so integrate [0,B] and double
    f = lambda x: a_star(x) * mp.mpf(phi_shift_critical(B, float(x)))
    return 2 * mp.quad(f, [0, B])


def phi_shift_critical(B: float, xi: float) -> float:
    # tau = 0, so shift is zero; fejer_heat_window
    fejer = max(0.0, 1.0 - abs(xi) / B)
    heat = math.exp(-4 * PI * PI * T_CRITICAL * xi * xi)
    return fejer * heat


def prime_sum_for_B(entries, B: float) -> float:
    total = 0.0
    for xi, w_q, heat in entries:
        if abs(xi) <= B:
            fejer = 1.0 - abs(xi) / B
            total += w_q * (fejer * heat)
    return total


def main():
    t0 = time.time()
    entries, nprimes = precompute_prime_powers(N)
    tb = tail_bound(N)

    # B grid
    B_values = []
    b = B_MIN
    # avoid floating accumulation issues
    steps = int(round((B_MAX - B_MIN) / B_H))
    for i in range(steps + 1):
        B_values.append(B_MIN + i * B_H)

    rows = []
    for B in B_values:
        prime_sum = prime_sum_for_B(entries, B)
        prime_ub = mp.mpf(prime_sum) + tb
        arch_val = arch_term_numeric(B)
        margin = arch_val - prime_ub
        rows.append((B, float(prime_sum), float(prime_ub), float(arch_val), float(margin)))

    # compute margin grid min and Lipschitz estimate
    margin_vals = [r[4] for r in rows]
    min_margin = min(margin_vals)
    # finite-difference Lipschitz estimate
    L_ub = 0.0
    for i in range(1, len(rows)):
        dm = abs(rows[i][4] - rows[i-1][4])
        L_ub = max(L_ub, dm / B_H)
    margin_lb = min_margin - L_ub * B_H / 2.0

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out_path = f"output/prime_cert_brange_tcritical_{ts}.txt"

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("Prime-term B-range certificate at t_critical (tau=0)\n")
        f.write("===============================================\n\n")
        f.write(f"B_min = {B_MIN}\n")
        f.write(f"B_max = {B_MAX}\n")
        f.write(f"B_h = {B_H}\n")
        f.write(f"t_critical = {T_CRITICAL}\n")
        f.write(f"tau = {TAU}\n")
        f.write(f"N = {N}\n\n")
        f.write(f"primes <= N: {nprimes}\n")
        f.write(f"tail_bound (n>N) = {tb}\n\n")
        f.write("B, prime_sum, prime_ub, arch_term, margin\n")
        for B, ps, pub, arch, marg in rows:
            f.write(f"{B:.4f}, {ps:.12f}, {pub:.12f}, {arch:.12f}, {marg:.12f}\n")
        f.write("\n")
        f.write(f"min_margin_grid = {min_margin}\n")
        f.write(f"L_ub (finite-diff) = {L_ub}\n")
        f.write(f"margin_lb = {margin_lb}\n")
        f.write(f"elapsed_sec = {time.time() - t0:.2f}\n")

    print(out_path)


if __name__ == "__main__":
    main()
