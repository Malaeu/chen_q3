#!/usr/bin/env python3
"""
Prime-term certificate at t_critical (single-scale, tau = 0).

We bound:
  prime_term(phi_shift_critical B_min 0) <= arch_term(phi_shift_critical B_min 0)
by computing:
  - exact sum over prime powers n <= N (via sieve)
  - rigorous tail bound using Lambda(n) <= log n and phi <= exp(-t (log n)^2)
  - arch_term by numerical integration (mpmath)

Outputs a timestamped report in output/.
"""

import math
import time
from datetime import datetime

import mpmath as mp

# Parameters
B_MIN = 3.0
T_CRITICAL = 3.0 / 20.0  # 0.15
TAU = 0.0
N = 1_000_000

PI = math.pi

# --- Definitions matching Lean ---

def xi_n(n: int) -> float:
    return math.log(n) / (2 * PI)

def phi_shift_critical(xi: float) -> float:
    # tau = 0, so shift is zero; fejer_heat_window
    fejer = max(0.0, 1.0 - abs(xi) / B_MIN)
    heat = math.exp(-4 * PI * PI * T_CRITICAL * xi * xi)
    return fejer * heat

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

def prime_power_sum(N: int) -> float:
    primes = sieve_primes(N)
    total = 0.0
    terms = 0
    for p in primes:
        logp = math.log(p)
        pk = p
        while pk <= N:
            xi = xi_n(pk)
            if abs(xi) <= B_MIN:
                w_q = 2.0 * logp / math.sqrt(pk)
                total += w_q * phi_shift_critical(xi)
                terms += 1
            pk *= p
    return total, terms, len(primes)

# Tail bound using Lambda(n) <= log n and phi <= exp(-t (log n)^2)
# Sum_{n>N} 2 log n / sqrt n * exp(-t (log n)^2) <= integral from N to inf.

def tail_bound(N: int) -> mp.mpf:
    u0 = mp.log(N)
    # change of variables: x = e^u
    # integrand: 2*u*exp(-t*u^2 + u/2)
    f = lambda u: 2 * u * mp.e**(-T_CRITICAL * u * u + u / 2)
    return mp.quad(f, [u0, mp.inf])

# Arch term integral

def arch_term_numeric() -> mp.mpf:
    # integrand is even for tau=0, so integrate [0,B] and double
    f = lambda x: a_star(x) * mp.mpf(phi_shift_critical(float(x)))
    return 2 * mp.quad(f, [0, B_MIN])


def main():
    t0 = time.time()
    prime_sum, terms, nprimes = prime_power_sum(N)
    tb = tail_bound(N)
    prime_ub = mp.mpf(prime_sum) + tb
    arch_val = arch_term_numeric()

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out_path = f"output/prime_cert_tcritical_{ts}.txt"

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("Prime-term certificate at t_critical (tau=0)\n")
        f.write("=============================================\n\n")
        f.write(f"B_min = {B_MIN}\n")
        f.write(f"t_critical = {T_CRITICAL}\n")
        f.write(f"tau = {TAU}\n")
        f.write(f"N = {N}\n\n")
        f.write(f"primes <= N: {nprimes}\n")
        f.write(f"prime powers counted: {terms}\n")
        f.write(f"prime_sum (n<=N) = {prime_sum}\n")
        f.write(f"tail_bound (n>N) = {tb}\n")
        f.write(f"prime_upper_bound = {prime_ub}\n\n")
        f.write(f"arch_term (numeric) = {arch_val}\n")
        f.write(f"margin (arch - prime_ub) = {arch_val - prime_ub}\n\n")
        f.write(f"elapsed_sec = {time.time() - t0:.2f}\n")

    print(out_path)

if __name__ == "__main__":
    main()
