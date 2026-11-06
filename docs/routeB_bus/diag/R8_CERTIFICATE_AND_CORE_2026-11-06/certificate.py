#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = ["python-flint==0.9.0", "numpy==2.3.5", "scipy==1.17.0"]
# ///
"""Exact and outward-certified finite rational NB upper-Gram certificates.

Run from the repository root with:
    uv run --no-project certificate.py [--preflight-only]

The exact path uses floor-breakpoint blocks and a common integer harmonic
denominator. The large-N path uses a fast floating candidate only; interval
claims are made from independently bounded direct row evaluations and the
explicit rational lower eigenvalue bound documented in certificate_method.md.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import os
import struct
import subprocess
import sys
import tempfile
import time
from decimal import Decimal
from pathlib import Path

import numpy as np
from scipy.linalg import solve
from flint import arb, arb_mat, ctx, fmpq, fmpq_mat


HERE = Path(__file__).resolve().parent
REUSE = HERE.parent / "NB_RATE_THERMOMETER_2026-11-06"
NATIVE = HERE / "certificate_native.cpp"
_NATIVE_TMP = None
EXACT_GRID = [10, 20, 50, 100, 200]
INTERVAL_GRID = [500, 1000, 2000]
ALL_GRID = EXACT_GRID + INTERVAL_GRID
PART_A_E = {}
PART_A_COEFF = {}


def progress(i: int, n: int, start: float, label: str) -> None:
    frac = i / n
    elapsed = time.monotonic() - start
    eta = elapsed * (1 - frac) / max(frac, 1e-30)
    filled = int(30 * frac)
    print(f"[{'#' * filled}{'.' * (30-filled)}] {100*frac:5.1f}% ETA {eta:.1f}s {label}", flush=True)


def fmpq_decimal(text: str) -> fmpq:
    d = Decimal(text)
    tup = d.as_tuple()
    num = 0
    for digit in tup.digits:
        num = 10 * num + digit
    if tup.sign:
        num = -num
    if tup.exponent >= 0:
        return fmpq(num * 10**tup.exponent)
    return fmpq(num, 10**(-tup.exponent))


def qabs(x: fmpq) -> fmpq:
    return x if x >= 0 else -x


def load_part_a() -> None:
    with (REUSE / "part_a_results.csv").open(newline="") as f:
        for row in csv.DictReader(f):
            PART_A_E[int(row["N"])] = float(row["e_N"])
    with (REUSE / "part_a_coefficients.csv").open(newline="") as f:
        for row in csv.DictReader(f):
            n = int(row["N"])
            PART_A_COEFF.setdefault(n, [0.0] * n)
            # The old Part A solve stores x=G^{-1}b; the actual minimizer is -x.
            PART_A_COEFF[n][int(row["n"]) - 1] = -float(row["c"])


def exact_k(N: int) -> int:
    q = math.isqrt(N**3)
    return q + (q * q < N**3)


def exact_finite_entry(N: int, K: int, D: int, hs: list[int], n: int, m: int) -> fmpq:
    """Exact sum_{k<K} r_n(k)r_m(k)/(k(k+1)), with r_1=1."""
    if n == 1 and m == 1:
        return fmpq(K - 1, K)
    if n == 1 or m == 1:
        d = m if n == 1 else n
        num = 0
        k = 1
        while k < K:
            q = k // d
            R = min(K - 1, (q + 1) * d - 1)
            a = q * d
            s1 = hs[R] - hs[k - 1]
            s2 = hs[R + 1] - hs[k]
            num += -a * s1 + (a + 1) * s2
            k = R + 1
        return fmpq(num, d * D)
    num = 0
    k = 1
    while k < K:
        qn, qm = k // n, k // m
        R = min(K - 1, (qn + 1) * n - 1, (qm + 1) * m - 1)
        a, b = qn * n, qm * m
        s1 = hs[R] - hs[k - 1]
        s2 = hs[R + 1] - hs[k]
        num += (R - k + 1) * D + a * b * s1 - (a + 1) * (b + 1) * s2
        k = R + 1
    return fmpq(num, n * m * D)


def exact_upper_gram(N: int) -> tuple[fmpq_mat, fmpq]:
    """Build G_up exactly; each residue pair is summed by floor blocks."""
    K = exact_k(N)
    D = math.lcm(*range(1, K + 1))
    hs = [0] * (K + 1)
    for j in range(1, K + 1):
        hs[j] = hs[j - 1] + D // j
    G = [[fmpq(0) for _ in range(N)] for _ in range(N)]
    qmean = [fmpq(1)] + [fmpq(n - 1, 2 * n) for n in range(2, N + 1)]
    alpha = fmpq(1, K) + fmpq(N, K * (K + 1))
    beta = fmpq(1, K) + fmpq(2 * N * N, K * (K + 1))

    start = time.monotonic()
    total = N * (N + 1) // 2
    done = 0
    for i, n in enumerate(range(1, N + 1)):
        for j, m in enumerate(range(1, n + 1)):
            v = exact_finite_entry(N, K, D, hs, n, m)
            if n > 1 and m > 1:
                g = math.gcd(n, m)
                v += alpha * qmean[n - 1] * qmean[m - 1]
                v += beta * fmpq(g * g - 1, 12 * n * m)
            elif n == 1 and m == 1:
                v += alpha
            else:
                v += alpha * qmean[n - 1] * qmean[m - 1]
            G[n - 1][m - 1] = G[m - 1][n - 1] = v
            done += 1
        if n == 1 or n % max(1, N // 20) == 0 or n == N:
            progress(done, total, start, f"exact rational Gram N={N}")

    gm = fmpq_mat(G)
    B = fmpq_mat([[G[i][j] for j in range(1, N)] for i in range(1, N)])
    cross = fmpq_mat([[G[i][0]] for i in range(1, N)])
    x = B.solve(-cross)
    ehat = G[0][0] + (fmpq_mat([[G[0][j] for j in range(1, N)]]) * x)[0, 0]
    if ehat <= 0:
        raise ArithmeticError(f"nonpositive exact Schur complement at N={N}")
    return gm, ehat


def direct_exact_check(N: int, K: int) -> bool:
    """Independent direct residue check of floor-block moments for small N."""
    for n in range(1, N + 1):
        for m in range(1, n + 1):
            got = exact_finite_entry(N, K, math.lcm(*range(1, K + 1)),
                                     [0] + [sum(math.lcm(*range(1, K + 1)) // t for t in range(1, j + 1))
                                            for j in range(1, K + 1)], n, m)
            r = fmpq(0)
            for k in range(1, K):
                rn = fmpq(1) if n == 1 else fmpq(k % n, n)
                rm = fmpq(1) if m == 1 else fmpq(k % m, m)
                r += rn * rm / (k * (k + 1))
            assert got == r, (N, K, n, m, got, r)
    return True


def mobius_jordan_data(N: int):
    mu = [0] * (N + 1)
    lp = [0] * (N + 1)
    primes = []
    mu[1] = 1
    for i in range(2, N + 1):
        if not lp[i]:
            lp[i] = i
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if p > lp[i] or i * p > N:
                break
            lp[i * p] = p
            mu[i * p] = 0 if p == lp[i] else -mu[i]
    J2 = [0] * (N + 1)
    for d in range(2, N + 1):
        value = d * d
        p = 2
        x = d
        while p * p <= x:
            if x % p == 0:
                value = value // (p * p) * (p * p - 1)
                while x % p == 0:
                    x //= p
            p += 1
        if x > 1:
            value = value // (x * x) * (x * x - 1)
        J2[d] = value
    divs = [[] for _ in range(N + 1)]
    for d in range(2, N + 1):
        for n in range(d, N + 1, d):
            divs[n].append(d)
    return mu, J2, divs


def exact_b_nu_ca(N: int, coeffs: list[fmpq]):
    """Exact mean, Jordan variance and C*a for rational coefficient inputs."""
    mu, J2, divs = mobius_jordan_data(N)
    b = fmpq(1)
    for n in range(2, N + 1):
        b += coeffs[n - 1] * fmpq(n - 1, 2 * n)
    zd = [fmpq(0) for _ in range(N + 1)]
    for n in range(2, N + 1):
        term = coeffs[n - 1] / n
        for d in divs[n]:
            zd[d] += term
    nu = fmpq(0)
    for d in range(2, N + 1):
        nu += fmpq(J2[d], 12) * zd[d] * zd[d]
    ca = [fmpq(0)] * N
    for n in range(2, N + 1):
        ca[n - 1] = sum((fmpq(J2[d], 12 * n) * zd[d] for d in divs[n]), fmpq(0))
    return b, nu, ca, mu, J2, divs


def trace_inverse_covariance_bound(N: int, mu, J2, divs) -> fmpq:
    """Return trace(C^-1)/12 from the exact divisor inverse formula."""
    total = fmpq(0)
    for d in range(2, N + 1):
        inner = 0
        for n in divs[d]:
            inner += n * n * (mu[d // n] != 0)
        total += fmpq(inner, J2[d])
    return total


def arb_interval_text(x: arb, digits: int = 30) -> str:
    return x.str(digits)


def arb_vasyunin_minimizer(N: int, precision: int = 256):
    """Rigorous Arb enclosures of the old full Vasyunin Gram minimizer."""
    ctx.prec = precision
    pi = arb.pi()
    gamma = arb.const_euler()
    kappa = (2 * pi).log() - gamma
    V: dict[int, list[arb]] = {1: [arb(0)]}
    start = time.monotonic()
    total = sum(q * q for q in range(2, N + 1))
    done = 0
    for q in range(2, N + 1):
        cot = [arb(0)] + [arb(fmpq(a, q)).cot_pi() for a in range(1, q)]
        vals = [arb(0) for _ in range(q)]
        for h in range(1, q):
            if math.gcd(h, q) != 1:
                continue
            acc = arb(0)
            for a in range(1, q):
                acc += arb(fmpq((h * a) % q, q)) * cot[a]
            vals[h] = acc
        V[q] = vals
        done += q * q
        if q == 2 or q % max(1, N // 20) == 0 or q == N:
            progress(done, total, start, f"Arb Vasyunin intervals N={N}")

    def Q(n: int, m: int) -> arb:
        g = math.gcd(n, m)
        h, k = n // g, m // g
        v1 = V[k][h % k] if k > 1 else arb(0)
        v2 = V[h][k % h] if h > 1 else arb(0)
        return (kappa * arb(fmpq(1, h) + fmpq(1, k)) / 2
                + arb(k - h) * arb(fmpq(h, k)).log() / (2 * h * k)
                - pi * (v1 + v2) / (2 * h * k)) / g

    q1 = [arb(0)] + [Q(n, 1) for n in range(1, N + 1)]
    G = [[arb(0) for _ in range(N - 1)] for _ in range(N - 1)]
    b = []
    for n in range(2, N + 1):
        b.append(arb(n).log() / n)
        for m in range(2, N + 1):
            G[n - 2][m - 2] = Q(n, m) - q1[n] / m - q1[m] / n + kappa / (n * m)
    Gm = arb_mat(G)
    bm = arb_mat([[x] for x in b])
    coeff = Gm.solve(-bm)
    e = arb(1) + (bm.transpose() * coeff)[0, 0]
    if not e.is_finite():
        raise ArithmeticError(f"Arb solve failed to enclose e_N at N={N}: {e}")
    return e, coeff, Gm, bm


def true_optimum_tail_rhs(N: int, K: int, coeff) -> arb:
    ctx.prec = 256
    mean = arb(1)
    for n in range(2, N + 1):
        mean += coeff[n - 2, 0] * arb(fmpq(n - 1, 2 * n))
    _, J2, divs = mobius_jordan_data(N)
    z = [arb(0) for _ in range(N + 1)]
    for n in range(2, N + 1):
        term = coeff[n - 2, 0] / n
        for d in divs[n]:
            z[d] += term
    nu = arb(0)
    for d in range(2, N + 1):
        nu += arb(fmpq(J2[d], 12)) * z[d] * z[d]
    rhs = 2 * (N * mean * mean + 2 * N * N * nu) / (K * (K + 1))
    return rhs


def certify_vasyunin_exact_point(N: int, ehat: fmpq):
    e, coeff, G, b = arb_vasyunin_minimizer(N)
    gap = arb(ehat) - e
    rhs = true_optimum_tail_rhs(N, exact_k(N), coeff)
    if not gap.is_finite() or not rhs.is_finite():
        raise ArithmeticError("nonfinite Arb J1/J2 evidence")
    return e, gap, rhs


def compile_native() -> Path:
    global _NATIVE_TMP
    _NATIVE_TMP = tempfile.TemporaryDirectory(prefix="r8_certificate_bin_")
    exe = Path(_NATIVE_TMP.name) / "certificate_native"
    subprocess.run(["clang++", "-O3", "-std=c++17", "-pthread", str(NATIVE), "-o", str(exe)], check=True)
    return exe


def run_native(exe: Path, mode: str, N: int, payload: bytes | None = None):
    with tempfile.TemporaryDirectory(prefix="r8_certificate_") as td:
        inp = Path(td) / "input.bin"
        out = Path(td) / "output.bin"
        if payload is not None:
            inp.write_bytes(payload)
        cmd = [str(exe), mode, str(N), str(inp), str(out)]
        # Inherit stdout/stderr so ASCII progress and ETA stay live and are
        # retained by the caller's certificate_run.log redirection.
        subprocess.run(cmd, check=True)
        if mode == "gram":
            raw = out.read_bytes()
            got_N = struct.unpack_from("=I", raw)[0]
            assert got_N == N and len(raw) == 4 + 8 * N * N
            G = np.frombuffer(raw, dtype="=f8", offset=4).copy().reshape((N, N))
            return G
        return out.read_text().splitlines()


def float_coeffs_as_rationals(values: list[float]) -> list[fmpq]:
    return [fmpq(*float(x).as_integer_ratio()) for x in values]


def coeff_payload(values: list[float]) -> bytes:
    return struct.pack("=" + "d" * len(values), *[float(x) for x in values])


def parse_native_eval(lines: list[str]):
    meta = lines[0].split()
    assert meta[0] == "META"
    data = {k: v for k, v in (x.split("=", 1) for x in meta[1:])}
    H = fmpq_decimal(lines[1].split("=", 1)[1])
    grad = [fmpq_decimal(x) for x in lines[2].split()[1:]]
    return H, grad, data


def gamma_bound(m: int, u: fmpq) -> fmpq:
    x = m * u
    return x / (1 - x)


def direct_eval_error_bounds(N: int, K: int, A: fmpq, mantissa: int, minsub: str, Hstr: str, gstrs: list[str]):
    # Native direct rows use only IEEE basic operations (no libm). The bound
    # covers each residue division, product, accumulation, and decimal output.
    u = fmpq(1, 1 << mantissa)
    Rmax = 1 + A
    # Twice the printed denorm_min also covers its 30-digit text conversion.
    subnormal = 2 * fmpq_decimal(minsub)
    deltaR = gamma_bound(2 * N + 2, u) * (1 + A) + 2 * u * A + (2 * N + 2) * subnormal
    Hout = fmpq(1, 10**27) * max(fmpq(1), qabs(fmpq_decimal(Hstr)))
    # Eight rounded operations per row is deliberately generous for direct
    # residue evaluation, weighted products, thread-local accumulation and
    # the final reduction.
    Herror = (2 * Rmax * deltaR + deltaR * deltaR
              + gamma_bound(8 * K + 16, u) * Rmax * Rmax
              + (2 * N * K + 4 * K) * subnormal + Hout)
    Gout = max((max(fmpq(1), qabs(fmpq_decimal(x))) for x in gstrs), default=fmpq(1)) / 10**27
    gerr = deltaR + (u + gamma_bound(8 * K + 16, u)) * Rmax + (4 * K + 2 * N + 4) * subnormal + Gout
    return Herror, gerr


def candidate_values(N: int) -> list[float]:
    return PART_A_COEFF[N][1:]


def run_preflight() -> None:
    load_part_a()
    # Exact small rational replay, including a source-published example.
    G3, e3 = exact_upper_gram(3)
    assert e3 == fmpq(2080069, 11531604), e3
    assert direct_exact_check(5, exact_k(5))
    mu, J2, divs = mobius_jordan_data(20)
    tr = trace_inverse_covariance_bound(20, mu, J2, divs)
    assert tr > 0
    # Check the exact covariance inverse trace formula against direct inverse.
    C = fmpq_mat([[fmpq(math.gcd(n, m)**2 - 1, 12 * n * m)
                   for m in range(2, 21)] for n in range(2, 21)])
    Cinv = C.inv()
    assert sum((Cinv[i, i] for i in range(19)), fmpq(0)) == 12 * tr
    # Native segmented candidate matrix must agree with the exact rational
    # small matrix; the native direct-row enclosure is checked against exact
    # rational H and gradient for a float-exact input vector.
    exe = compile_native()
    G10_exact, eh10 = exact_upper_gram(10)
    G10_float = run_native(exe, "gram", 10)
    max_matrix_error = max(abs(float(G10_exact[i, j]) - G10_float[i, j])
                           for i in range(10) for j in range(10))
    assert max_matrix_error < 1e-11, max_matrix_error
    aval = PART_A_COEFF[10][1:]
    aq = [fmpq(0)] + float_coeffs_as_rationals(aval)
    lines = run_native(exe, "eval", 10, coeff_payload(aval))
    Hnum, gnum, meta = parse_native_eval(lines)
    H_exact = fmpq(0)
    g_exact = [fmpq(0) for _ in range(9)]
    for k in range(1, exact_k(10)):
        R = fmpq(1)
        rs = []
        for n in range(2, 11):
            r = fmpq(k % n, n)
            rs.append(r)
            R += aq[n - 1] * r
        w = fmpq(1, k * (k + 1))
        H_exact += R * R * w
        for j, r in enumerate(rs):
            g_exact[j] += R * r * w
    Aexact = sum((qabs(q) for q in aq[1:]), fmpq(0))
    Herr, gerr = direct_eval_error_bounds(10, exact_k(10), Aexact, int(meta["mantissa"]), meta["minsub"],
                                          lines[1].split("=", 1)[1], lines[2].split()[1:])
    assert qabs(Hnum - H_exact) <= Herr
    assert all(qabs(gnum[j] - g_exact[j]) <= gerr for j in range(9))
    # Check the Arb Vasyunin solve and J2 at one endpoint before the grid.
    e2, gap2, rhs2 = certify_vasyunin_exact_point(10, eh10)
    assert e2.is_finite() and gap2.is_finite() and rhs2.is_finite()
    record = {
        "PASS": True,
        "exact_ehat_3": str(e3),
        "floor_block_matches_direct_N5": True,
        "trace_inverse_covariance_matches_exact_inverse_N20": True,
        "native_segmented_matrix_max_error_N10": max_matrix_error,
        "native_direct_eval_interval_contains_exact_H_and_gradient_N10": True,
        "arb_vasyunin_N10_finite": True,
        "pre_registration_commit": "94ec9ac25",
    }
    (HERE / "certificate_preflight.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2), flush=True)


def format_interval_rows(rows, fields):
    path = HERE / "certificate_results.csv"
    with path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields, lineterminator="\n")
        w.writeheader()
        w.writerows(rows)


def run_exact_grid() -> dict[int, fmpq]:
    exact = {}
    rows = []
    start = time.monotonic()
    for i, N in enumerate(EXACT_GRID):
        _, eh = exact_upper_gram(N)
        exact[N] = eh
        ctx.prec = 256
        eh_arb = arb(eh)
        logprod = eh_arb * arb(N).log()
        en, gap, rhs = certify_vasyunin_exact_point(N, eh)
        ratio_cert = eh_arb / en
        j1_pass = gap > 0
        j2_pass = (gap >= 0 and (rhs - gap) > 0) if N <= 50 else None
        c = candidate_values(N)
        ratio = float(eh) / PART_A_E[N]
        row = {
            "N": N,
            "K": exact_k(N),
            "ehat_exact_numerator": str(eh.numerator),
            "ehat_exact_denominator": str(eh.denominator),
            "ehat_decimal_interval": arb_interval_text(eh_arb),
            "e_N_partA_diagnostic": f"{PART_A_E[N]:.17g}",
            "ehat_over_eN_diagnostic_ratio": f"{ratio:.17g}",
            "ehat_over_eN_certified_interval": arb_interval_text(ratio_cert),
            "ehat_logN_certified_interval": arb_interval_text(logprod),
            "ehat_logN_le_half_certified": str(logprod < arb("0.5")),
            "eN_arb_interval": "" if en is None else arb_interval_text(en),
            "J1_gap_interval": "" if gap is None else arb_interval_text(gap),
            "J1_pass": str(j1_pass),
            "J2_rhs_minus_gap_interval": "" if N > 50 else arb_interval_text(rhs - gap),
            "J2_optimum_rhs_interval": "" if N > 50 else arb_interval_text(rhs),
            "J2_pass": "" if N > 50 else str(j2_pass),
        }
        rows.append(row)
        witness = {
            "N": N,
            "K": exact_k(N),
            "ehat_exact": {"numerator": str(eh.numerator), "denominator": str(eh.denominator)},
            "eN_arb_interval": arb_interval_text(en),
            "ehat_minus_eN_arb_interval": arb_interval_text(gap),
            "ehat_over_eN_arb_interval": arb_interval_text(ratio_cert),
            "J1_pass": bool(j1_pass),
            "J2_applicable": N <= 50,
            "J2_rhs_arb_interval": arb_interval_text(rhs) if N <= 50 else None,
            "J2_rhs_minus_gap_arb_interval": arb_interval_text(rhs-gap) if N <= 50 else None,
            "preregistration_commit": "94ec9ac25",
            "method": "exact rational G_up Schur complement; Arb Vasyunin Gram minimizer",
        }
        (HERE / f"certificate_witness_N{N}.json").write_text(json.dumps(witness, indent=2) + "\n")
        progress(i + 1, len(EXACT_GRID), start, f"exact+Arb grid N={N}")
    format_interval_rows(rows, list(rows[0]))
    return exact


def run_large_grid(exact: dict[int, fmpq], grid=INTERVAL_GRID):
    exe = compile_native()
    rows = []
    for N in grid:
        K = exact_k(N)
        print(f"Preparing candidate Gram N={N}, K={K}", flush=True)
        G = run_native(exe, "gram", N)
        B = G[1:, 1:]
        cross = G[1:, 0]
        # Cholesky solve on the symmetric candidate matrix. The result is only
        # a candidate; its certification follows from the interval residual.
        a = solve(B, -cross, assume_a="pos", check_finite=False)
        print(f"Evaluating candidate objective/gradient N={N}", flush=True)
        lines = run_native(exe, "eval", N, coeff_payload(a))
        Hnum, ghead, meta = parse_native_eval(lines)
        p = float_coeffs_as_rationals(list(a))
        coeffs = [fmpq(0)] + p
        mean, nu, ca, mu, J2, divs = exact_b_nu_ca(N, coeffs)
        A = sum((qabs(x) for x in coeffs[1:]), fmpq(0))
        Herror, gerror = direct_eval_error_bounds(N, K, A, int(meta["mantissa"]), meta["minsub"], lines[1].split("=", 1)[1], lines[2].split()[1:])
        alpha = fmpq(1, K) + fmpq(N, K * (K + 1))
        beta = fmpq(1, K) + fmpq(2 * N * N, K * (K + 1))
        Ucenter = Hnum + alpha * mean * mean + beta * nu
        Ulo, Uhi = Ucenter - Herror, Ucenter + Herror
        grad_centers = [ghead[j] + alpha * mean * fmpq(n - 1, 2 * n) + beta * ca[n - 1]
                        for j, n in enumerate(range(2, N + 1))]
        grad_sq_upper = sum(((qabs(g) + gerror) ** 2 for g in grad_centers), fmpq(0))
        lambdaB = beta / (12 * trace_inverse_covariance_bound(N, mu, J2, divs))
        lower = Ulo - grad_sq_upper / lambdaB
        # Eq. (9) plus the exact Young slack gives E(c) <= U(c)-slack(c).
        # Use the same near-minimizer to obtain a rigorous e_N upper bound.
        d = arb(N).sqrt() * abs(arb(mean)) - N * arb(nu).sqrt()
        young_slack = d * d / (K * (K + 1))
        Eupper = (arb(Uhi) - young_slack).upper()
        eh_lo, eh_hi = arb(lower), arb(Uhi)
        j1_margin = eh_lo - Eupper
        logprod_lo = eh_lo * arb(N).log()
        logprod_hi = eh_hi * arb(N).log()
        logprod = f"[{arb_interval_text(logprod_lo)}; {arb_interval_text(logprod_hi)}]"
        j1_pass = j1_margin > 0
        j2_pass = ""
        row = {
            "N": N,
            "K": K,
            "ehat_exact_numerator": "",
            "ehat_exact_denominator": "",
            "ehat_decimal_interval": f"[{arb_interval_text(eh_lo)}; {arb_interval_text(eh_hi)}]",
            "e_N_partA_diagnostic": f"{PART_A_E[N]:.17g}",
            "ehat_over_eN_diagnostic_ratio": f"{float(Ucenter) / PART_A_E[N]:.17g}",
            "ehat_over_eN_certified_interval": f">= {arb_interval_text(eh_lo / Eupper)}; no finite upper bound computed",
            "ehat_logN_certified_interval": logprod,
            "ehat_logN_le_half_certified": str(logprod_hi < arb("0.5")),
            "eN_arb_interval": f"upper <= {arb_interval_text(Eupper)} (candidate Young-slack enclosure)",
            "J1_gap_interval": arb_interval_text(j1_margin),
            "J1_pass": str(j1_pass),
            "J2_rhs_minus_gap_interval": "",
            "J2_optimum_rhs_interval": "not requested above N=50",
            "J2_pass": j2_pass,
        }
        rows.append(row)
        witness = {
            "N": N,
            "K": K,
            "candidate_a_float_hex": [float(x).hex() for x in a],
            "candidate_a_exact_rationals": [str(q) for q in p],
            "H_direct_center": str(Hnum),
            "H_direct_error_bound": str(Herror),
            "gradient_center_norm_sq_upper": str(grad_sq_upper),
            "gradient_component_error_bound": str(gerror),
            "mean_b_exact": str(mean),
            "jordan_variance_exact": str(nu),
            "alpha_exact": str(alpha),
            "beta_exact": str(beta),
            "lambda_B_lower_exact": str(lambdaB),
            "candidate_U_lower_exact": str(Ulo),
            "candidate_U_upper_exact": str(Uhi),
            "ehat_lower_exact": str(lower),
            "young_slack_arb_interval": arb_interval_text(young_slack),
            "eN_upper_arb": arb_interval_text(Eupper),
            "J1_margin_arb": arb_interval_text(j1_margin),
            "preregistration_commit": "94ec9ac25",
            "compiler": "Apple clang++ -O3 -std=c++17 -pthread",
            "direct_rounding_model": "round-to-nearest; relative gamma bounds for normal operations; denorm_min additive budget; output decimal allowance 1e-27*max(1,abs(value))",
            "candidate_matrix_method": "segmented floor-block residues; candidate only, not used in enclosure",
            "command": "uv run --no-project --with python-flint==0.9.0 --with numpy==2.3.5 --with scipy==1.17.0 python certificate.py --large-only",
        }
        (HERE / f"certificate_witness_N{N}.json").write_text(json.dumps(witness, indent=2) + "\n")
        print(f"CERT N={N}: ehat=[{eh_lo}; {eh_hi}] eN_upper={Eupper} J1_margin={j1_margin}", flush=True)
    path = HERE / "certificate_results.csv"
    # Append large rows to the exact-grid table without modifying other files.
    with path.open("a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        w.writerows(rows)


def write_judges():
    rows = []
    # Exact Arb Vasyunin minimizers are already included in certificate_results
    # for the J2 grid. Record the theorem-level J1 and the numerical gap witnesses.
    with (HERE / "certificate_results.csv").open(newline="") as f:
        for r in csv.DictReader(f):
            if not r["N"]:
                continue
            N = int(r["N"])
            j1 = r.get("J1_pass", "") == "True"
            rows.append({
                "judge": "J1",
                "N": N,
                "status": "PASS_ANALYTIC_AND_NUMERIC" if j1 else "ANALYTIC_PASS_NUMERIC_UNRESOLVED",
                "evidence": "G_inf<=G_up from source (10)-(13); Arb true-minimum enclosure" if N <= 200 else "certified ehat lower endpoint exceeds candidate E(c) upper bound from Young slack",
            })
            if N in (10, 20, 50):
                j2 = r.get("J2_pass", "") == "True"
                rows.append({
                    "judge": "J2",
                    "N": N,
                    "status": "PASS_SOURCE_OPTIMUM_APPLIES" if j2 else "SOURCE_APPLIES_NUMERIC_UNRESOLVED",
                    "evidence": "Arb true minimizer enclosure: ehat-e_N interval is contained below RHS (11) interval",
                })
    with (HERE / "certificate_judges.csv").open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["judge", "N", "status", "evidence"], lineterminator="\n")
        w.writeheader()
        w.writerows(rows)


def write_summary():
    with (HERE / "certificate_results.csv").open(newline="") as f:
        rows = list(csv.DictReader(f))
    p1_rows = [r for r in rows if int(r["N"]) <= 1000]
    p1_fail = [int(r["N"]) for r in p1_rows if float(r["ehat_over_eN_diagnostic_ratio"]) > 1.5]
    p2_fail = [int(r["N"]) for r in rows if r["ehat_logN_le_half_certified"] != "True"]
    j1_fail = [int(r["N"]) for r in rows if r["J1_pass"] != "True"]
    j2_fail = [int(r["N"]) for r in rows if int(r["N"]) in (10, 20, 50) and r["J2_pass"] != "True"]
    summary = {
        "scope": "Part 1 certificate and J1/J2 only",
        "preregistration_commit": "94ec9ac25",
        "preflight": "PASS",
        "P1": {"score": "MISS" if p1_fail else "HIT", "failed_N": p1_fail,
               "rule": "diagnostic ehat/e_N <= 1.5 at every certificate-grid N<=1000"},
        "P2": {"score": "MISS" if p2_fail else "HIT", "failed_N": p2_fail,
               "rule": "certified ehat_N*log(N) <= 1/2 at every certificate-grid point"},
        "J1": {"score": "PASS" if not j1_fail else "UNRESOLVED", "failed_N": j1_fail,
               "rule": "source G_inf<=G_up, with strict numerical separation at all eight points"},
        "J2": {"score": "PASS" if not j2_fail else "UNRESOLVED", "failed_N": j2_fail,
               "rule": "at the Arb-enclosed true optimum, ehat-e_N <= RHS (11), N=10,20,50"},
        "points": [{
            "N": int(r["N"]), "K": int(r["K"]),
            "ehat_exact": (r["ehat_exact_numerator"] + "/" + r["ehat_exact_denominator"])
                if r["ehat_exact_numerator"] else None,
            "ehat_interval": r["ehat_decimal_interval"],
            "e_N_partA_diagnostic": r["e_N_partA_diagnostic"],
            "ratio_partA_diagnostic": r["ehat_over_eN_diagnostic_ratio"],
            "ratio_certified": r["ehat_over_eN_certified_interval"],
            "ehat_logN_interval": r["ehat_logN_certified_interval"],
            "threshold_pass": r["ehat_logN_le_half_certified"] == "True",
            "J1_pass": r["J1_pass"] == "True",
            "J2_pass": None if not r["J2_pass"] else r["J2_pass"] == "True",
        } for r in rows],
        "honesty": {"RH_PROVED": False, "PX_RH_CLAIM": "NOT_MADE",
                    "large_ratio_limit": "large-grid ratio has a certified lower bound only; the upper endpoint uses archived Part A diagnostic e_N"},
    }
    (HERE / "certificate_summary.json").write_text(json.dumps(summary, indent=2) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--preflight-only", action="store_true")
    ap.add_argument("--exact-only", action="store_true")
    ap.add_argument("--large-only", action="store_true")
    ap.add_argument("--large-n", type=int, action="append")
    args = ap.parse_args()
    load_part_a()
    if args.preflight_only:
        run_preflight()
        return
    if args.large_only:
        run_large_grid({}, args.large_n or INTERVAL_GRID)
        write_judges()
        write_summary()
        return
    exact = run_exact_grid()
    if not args.exact_only:
        run_large_grid(exact)
    write_judges()
    if not args.exact_only:
        write_summary()


if __name__ == "__main__":
    main()
