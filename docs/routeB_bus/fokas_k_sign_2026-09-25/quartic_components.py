#!/usr/bin/env python3
"""Diagnostic split of the central full quartic into W02, -WR, and -Prime."""
from __future__ import annotations

import argparse
import json
import time
from functools import lru_cache
from pathlib import Path

import mpmath as mp

import rectangle_probe as rp  # noqa: E402
import full_center_probe as fc  # noqa: E402


def q_kernel(x, n, j, L):
    # The exact kernel vanishes at the full period x=L; avoid retaining the
    # harmless sin(2*pi*integer) roundoff in the cutoff Prime term k=m.
    if x == L:
        return mp.mpf(0)
    if n == j:
        return 2 * (L - x) / L * mp.cos(2 * mp.pi * n * x / L)
    return (mp.sin(2 * mp.pi * j * x / L) - mp.sin(2 * mp.pi * n * x / L)) / (mp.pi * (n - j))


def von_mangoldt(k):
    for p in range(2, k + 1):
        if any(p % d == 0 for d in range(2, int(p**0.5) + 1)):
            continue
        power = p
        while power < k:
            power *= p
        if power == k:
            return mp.log(p)
    return mp.mpf(0)


def component_matrices(m):
    """Return signed matrices W02, -WR, -Prime using full_center_probe formulas."""
    L = mp.log(m)
    modes = list(range(-m, m + 1))
    size = len(modes)
    W02, WR, Prime = mp.zeros(size), mp.zeros(size), mp.zeros(size)

    grid = [L * k / 8 for k in range(9)]
    moments = {0: mp.mpf(0)}
    diagonals = {}
    for n in range(m + 1):
        omega = 2 * mp.pi * n / L
        if n:
            moments[n] = mp.quad(
                lambda x: omega / 2 if not x else mp.exp(x / 2) * mp.sin(omega * x) / (2 * mp.sinh(x)),
                grid,
            )
            moments[-n] = -moments[n]
        diagonals[n] = mp.quad(
            lambda x: mp.mpf("0.5") - 1 / L if not x else
            (mp.exp(x / 2) * q_kernel(x, n, n, L) - 2) / (2 * mp.sinh(x)),
            grid,
        )

    wr_constant = mp.euler + mp.log(4 * mp.pi * mp.tanh(L / 2))
    C = 32 * L * mp.sinh(L / 4) ** 2
    a = [1 / (L**2 + 16 * mp.pi**2 * n**2) for n in modes]
    b = [n / (L**2 + 16 * mp.pi**2 * n**2) for n in modes]
    for i, n in enumerate(modes):
        for j in range(i, size):
            v = modes[j]
            w02 = C * (L**2 * a[i] * a[j] - 16 * mp.pi**2 * b[i] * b[j])
            wr = (wr_constant + diagonals[abs(n)] if n == v else
                  (moments[v] - moments[n]) / (mp.pi * (n - v)))
            prime = mp.fsum(
                von_mangoldt(k) / mp.sqrt(k) * q_kernel(mp.log(k), n, v, L)
                for k in range(2, m + 1)
            )
            W02[i, j] = W02[j, i] = w02
            WR[i, j] = WR[j, i] = wr
            Prime[i, j] = Prime[j, i] = prime
    signed = {"W02": W02, "-WR": -WR, "-Prime": -Prime}
    return signed, {"C": C, "a": a, "b": b}


def trace_projection(Pi, A):
    return mp.fsum((Pi * A * Pi)[i, i] for i in range(Pi.rows))


def component_forms(A, z, p, Pi, X2, Y2, q, v):
    qz_c = (z.H * A * z)[0]
    qp_c = (p.H * A * p)[0]
    theta_c = trace_projection(Pi, A)
    r3_c = Y2 * (qz_c - theta_c * X2) + X2 * qp_c
    tau_c = (v.H * A * v)[0] - (q.H * A * q)[0]
    return {
        "qz": qz_c,
        "qp": qp_c,
        "theta": theta_c,
        "quartic": r3_c,
        "tau": tau_c,
        "identity_error": r3_c + X2 * Y2 * tau_c,
        "max_imaginary_residual": max(abs(mp.im(qz_c)), abs(mp.im(qp_c)), abs(mp.im(theta_c)), abs(mp.im(r3_c)), abs(mp.im(tau_c))),
    }


def companion_vector(Pi, p, Y2):
    """Construct unit v in range(Pi), orthogonal to p/Y; unique up to phase."""
    u = p / mp.sqrt(Y2)
    for j in range(Pi.rows):
        candidate = mp.matrix([Pi[i, j] for i in range(Pi.rows)])
        candidate -= u * (u.H * candidate)[0]
        norm2 = mp.re((candidate.H * candidate)[0])
        if norm2 > mp.mpf("1e-30"):
            return candidate / mp.sqrt(norm2)
    raise ArithmeticError("could not construct plane companion")


def delta_q(x, q, v, modes, L):
    Q = mp.matrix([[q_kernel(x, n, j, L) for j in modes] for n in modes])
    return mp.re((v.H * Q * v - q.H * Q * q)[0])


def sum_abs(v):
    return abs(mp.fsum(v[i] for i in range(v.rows))) ** 2


def run(m, dps):
    mp.mp.dps = dps
    # The source kernels only depend on this process-wide precision.
    rp._mp_kernel = lru_cache(maxsize=None)(rp._mp_kernel)
    intervals = rp.bracket(m)
    e0, e4 = (sum(intervals[i]) / 2 for i in (0, 4))
    P0, P4 = rp.recurrence(m, e0)[0], rp.recurrence(m, e4)[0]
    F = rp.F_matrix(m)
    z = F * mp.matrix([(-1) ** k * (P0[k] - P4[k]) for k in range(1, 6 * m)])
    Pi, parity_error, gaussian_cutoff = fc.gaussian_plane(m)
    p = Pi * z
    X2 = mp.re((z.H * z)[0])
    Y2 = mp.re((p.H * p)[0])
    q = z / mp.sqrt(X2)
    v = companion_vector(Pi, p, Y2)
    modes = list(range(-m, m + 1))
    components, w02_factor = component_matrices(m)
    terms = {name: component_forms(A, z, p, Pi, X2, Y2, q, v)
             for name, A in components.items()}
    K = sum(components.values(), mp.zeros(2 * m + 1))
    total = component_forms(K, z, p, Pi, X2, Y2, q, v)
    term_values = [mp.re(terms[name]["quartic"]) for name in ("W02", "-WR", "-Prime")]
    gross = mp.fsum(abs(x) for x in term_values)
    cancellation_factor = gross / abs(mp.re(total["quartic"]))
    positive = mp.fsum(x for x in term_values if x > 0)
    negative_abs = mp.fsum(-x for x in term_values if x < 0)
    one = mp.matrix([1] * (2 * m + 1))
    endpoint_limit = (mp.re((one.T * Pi * one)[0]) - sum_abs(p / mp.sqrt(Y2)) - sum_abs(q)) / mp.log(m)
    t_grid = [mp.mpf(x) for x in ("0.05", "0.1", "0.25", "0.5", "0.75", "0.9")]
    delta_samples = {mp.nstr(t, 3): mp.re(delta_q(mp.log(m) * t, q, v, modes, mp.log(m))) for t in t_grid}
    imag_q = {str(n): mp.im(q[i, 0]) for i, n in enumerate(modes)}
    symmetry = max(abs(z[i, 0] - mp.conj(z[len(modes) - 1 - i, 0]))
                   for i in range(len(modes)))
    factorization = mp.matrix([[w02_factor["C"] * (mp.log(m)**2 * w02_factor["a"][i] * w02_factor["a"][j]
                                                          - 16 * mp.pi**2 * w02_factor["b"][i] * w02_factor["b"][j])
                                for j in range(len(modes))] for i in range(len(modes))])
    W02_factorization_error = mp.norm(components["W02"] - factorization)

    def nstr(x, digits=35):
        return mp.nstr(x, digits)

    result = {
        "status": "DIAGNOSTIC_ONLY_NOT_A_PROOF",
        "m": m,
        "dps": dps,
        "central_energy_midpoints": {"E0": nstr(e0), "E4": nstr(e4)},
        "norm_z": nstr(mp.sqrt(X2)),
        "norm_Pi_z": nstr(mp.sqrt(Y2)),
        "projection_idempotence_error": nstr(mp.norm(Pi * Pi - Pi), 10),
        "gaussian_parity_error": nstr(parity_error, 10),
        "gaussian_cutoff_terms": gaussian_cutoff,
        "W02_rank_two_factorization": {
            "rank": 2,
            "C": nstr(w02_factor["C"]),
            "factorization_frobenius_residual": nstr(W02_factorization_error, 10),
            "formula": "C*(L^2*a*a^T - 16*pi^2*b*b^T), a_n=1/(L^2+16*pi^2*n^2), b_n=n/(L^2+16*pi^2*n^2)",
        },
        "signed_components": {
            name: {
                "quartic_R3_contribution": nstr(mp.re(data["quartic"])),
                "normalized_tau_contribution": nstr(mp.re(data["tau"])),
                "share_of_total_tau_percent": nstr(100 * mp.re(data["tau"]) / mp.re(total["tau"])),
                "theta_component": nstr(mp.re(data["theta"])),
                "qAq": nstr(mp.re((q.H * components[name] * q)[0])),
                "vAv": nstr(mp.re((v.H * components[name] * v)[0])),
                "quartic_identity_residual": nstr(data["identity_error"], 10),
                "max_imaginary_residual": nstr(data["max_imaginary_residual"], 10),
            }
            for name, data in terms.items()
        },
        "total": {
            "central_full_quartic_R3": nstr(mp.re(total["quartic"])),
            "normalized_tau": nstr(mp.re(total["tau"])),
            "sum_of_signed_quartic_components": nstr(mp.fsum(term_values)),
            "component_sum_residual": nstr(mp.fsum(term_values) - mp.re(total["quartic"]), 10),
            "quartic_normalization_identity_residual": nstr(total["identity_error"], 10),
            "gross_absolute_component_sum": nstr(gross),
            "gross_to_net_cancellation_factor": nstr(cancellation_factor),
            "net_as_percent_of_gross_absolute_sum": nstr(100 / cancellation_factor),
            "positive_quartic_bucket": nstr(positive),
            "negative_quartic_bucket_absolute": nstr(negative_abs),
            "q_v_orthogonality_residual": nstr((q.H * v)[0], 10),
            "q_conjugate_symmetry_residual": nstr(symmetry, 10),
            "q_imaginary_modes": {n: nstr(x) for n, x in imag_q.items()},
            "endpoint_hDelta_limit_at_x0": nstr(endpoint_limit),
            "deltaQ_samples_t": {t: nstr(x) for t, x in delta_samples.items()},
        },
    }
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, choices=(2, 4), required=True)
    ap.add_argument("--dps", type=int, default=80)
    args = ap.parse_args()
    started = time.time()
    result = run(args.m, args.dps)
    result["seconds"] = time.time() - started
    output = Path(__file__).with_name(f"quartic_components_m{args.m}_dps{args.dps}.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print(f"WROTE {output}")


if __name__ == "__main__":
    main()
