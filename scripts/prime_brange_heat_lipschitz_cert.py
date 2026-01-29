#!/usr/bin/env python3
"""
Scaffold: compute heat-weighted Lipschitz constants for the prime/arch terms
at t_critical (tau=0) over B in [B_MIN, B_MAX].

This is a NUMERIC certificate helper. It is NOT a formal proof.
Outputs a timestamped report in output/.

We estimate:
  L_prime_heat = sum_n w_Q(n) * exp(-4*pi^2*t*xi_n^2) * |xi_n|
  L_arch_heat  = ∫_{|x|<=B_MAX} |a_star(x)| * exp(-4*pi^2*t*x^2) * |x| dx
Then a candidate Lipschitz constant is:
  L_total = (L_arch_heat + L_prime_heat) / (B_MIN^2)
using the bound from phi_shift_lipschitz_B_exp.
"""

import math
import time
from datetime import datetime

try:
    import mpmath as mp
except Exception as e:
    raise SystemExit("mpmath is required for this script: pip install mpmath") from e

# Parameters
B_MIN = 3.0
B_MAX = 4.9
T_CRITICAL = 3.0 / 20.0  # 0.15
N = 1_000_000

PI = math.pi
mp.mp.dps = 60


def xi_n(n: int) -> float:
    return math.log(n) / (2 * PI)


def a_star(xi: float) -> mp.mpf:
    z = mp.mpf("0.25") + 1j * mp.pi * mp.mpf(xi)
    val = mp.log(mp.pi) - mp.re(mp.digamma(z))
    return 2 * mp.pi * val


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


# Tail bound for L_prime_heat:
# sum_{n>N} (2 log n / sqrt n) * exp(-t (log n)^2) * (log n)/(2π)
# <= integral_{N}^∞ (1/π) (log x)^2 / sqrt x * exp(-t (log x)^2) dx
# Substitute x = e^u, dx = e^u du:
# integrand becomes (1/π) u^2 * exp(-t u^2 + u/2) du

def tail_bound_heat(N: int) -> mp.mpf:
    u0 = mp.log(N)
    f = lambda u: (1 / mp.pi) * (u ** 2) * mp.e ** (-T_CRITICAL * u * u + u / 2)
    return mp.quad(f, [u0, mp.inf])


def prime_L_heat(entries, tail) -> mp.mpf:
    s = mp.mpf("0.0")
    for xi, w_q, heat in entries:
        s += mp.mpf(w_q) * mp.mpf(heat) * mp.mpf(abs(xi))
    return s + tail


def arch_L_heat() -> mp.mpf:
    # Even integrand; integrate [0, B_MAX] and double
    f = lambda x: mp.fabs(a_star(x)) * mp.e ** (-4 * mp.pi ** 2 * T_CRITICAL * x * x) * x
    return 2 * mp.quad(f, [0, B_MAX])


def main():
    t0 = time.time()
    entries, nprimes = precompute_prime_powers(N)
    tail = tail_bound_heat(N)
    Lp = prime_L_heat(entries, tail)
    La = arch_L_heat()
    L_total = (Lp + La) / (B_MIN ** 2)

    ts = datetime.now().strftime("%Y-%m-%d_%H%M")
    out_path = f"output/prime_cert_brange_heat_L_{ts}.txt"

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("Heat-weighted Lipschitz certificate scaffold (t_critical, tau=0)\n")
        f.write("============================================================\n\n")
        f.write(f"B_min = {B_MIN}\n")
        f.write(f"B_max = {B_MAX}\n")
        f.write(f"t_critical = {T_CRITICAL}\n")
        f.write(f"N = {N}\n\n")
        f.write(f"primes <= N: {nprimes}\n")
        f.write(f"tail_bound_heat = {tail}\n")
        f.write(f"L_prime_heat = {Lp}\n")
        f.write(f"L_arch_heat = {La}\n")
        f.write(f"L_total = {L_total}\n")
        f.write(f"elapsed_sec = {time.time() - t0:.2f}\n")

    print(out_path)


if __name__ == "__main__":
    main()
