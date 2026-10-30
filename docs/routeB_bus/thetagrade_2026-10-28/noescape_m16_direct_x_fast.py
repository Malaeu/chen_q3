#!/usr/bin/env python3
"""Fixed-quadrature physical k(W,v) and direct X for the retained m=16 cell.

This is a finite high-precision diagnostic, not an error certificate. It reuses
the already computed physical k(h_out,v) and Arb B from direct_x.json.
"""

from __future__ import annotations

import hashlib
import json
import signal
import sys
import time
from pathlib import Path

sys.dont_write_bytecode = True

import mpmath as mp
from flint import arb, ctx

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "noescape_m16_direct_x.json"
EIGEN = HERE / "noescape_m16_eigenpair.json"
OUTPUT = HERE / "noescape_m16_direct_x_fast.json"
M = 16
ORDERS = (64, 96)
W_THETA_TERMS = 2
W_IMAGE_MAX = 1
MP_DPS = 60
TIME_CAP = 120


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def midpoint(ball: str) -> mp.mpf:
    return mp.mpf(arb(ball).mid().str(MP_DPS, radius=False))


def nodes_weights(order: int) -> tuple[list[mp.mpf], list[mp.mpf]]:
    xs, ws = mp.gauss_quadrature(order, "legendre")
    return list(xs), list(ws)


def integrate(fun, a, z, rule):
    if z <= a:
        return mp.mpf(0)
    xs, ws = rule
    scale = (z - a) / 2
    center = (z + a) / 2
    return scale * mp.fsum(w * fun(center + scale * x) for x, w in zip(xs, ws))


def compute(order: int, coeff: list[mp.mpf], lam: mp.mpf, khout: mp.mpf, B: mp.mpf):
    L = mp.log(M)
    b = L / 2
    pi = mp.pi
    sqrtL = mp.sqrt(L)
    omega = [2 * pi * n / L for n in range(1, M + 1)]
    cp = coeff[M + 1:]
    rule = nodes_weights(order)
    cstar = mp.euler + mp.log(8 * pi) + pi / 2

    def h(x):
        u = mp.exp(2 * x)
        return mp.exp(x / 2) * mp.fsum(
            (16 * pi**2 * n**4 * u**2 - 24 * pi * n**2 * u)
            * mp.exp(-pi * n**2 * u)
            for n in range(1, W_THETA_TERMS + 1)
        )

    def W(x):
        z = abs(x)
        return h(L - z) + h(L + z)

    def v(x):
        return (coeff[M] + 2 * mp.fsum(
            a * mp.cos(w * (x + b)) for a, w in zip(cp, omega)
        )) / sqrtL

    def p(x):
        return mp.sqrt(2) * mp.cosh(x / 2)

    def j(s):
        return mp.exp(-s / 2) / (-mp.expm1(-2 * s))

    def qW(s):
        # 2<W(x),v(x+s)> on the overlap; split at the W cusp x=0.
        right = b - s
        if right <= -b:
            return mp.mpf(0)
        f = lambda x: W(x) * v(x + s)
        if right > 0:
            return 2 * (integrate(f, -b, 0, rule) + integrate(f, 0, right, rule))
        return 2 * integrate(f, -b, right, rule)

    inner = 2 * integrate(lambda x: W(x) * v(x), 0, b, rule)
    p_v = 2 * integrate(lambda x: v(x) * p(x), 0, b, rule)
    w_p = 2 * integrate(lambda x: W(x) * p(x), 0, b, rule)
    diagonal = -cstar * inner
    pole = w_p * p_v

    # The paired difference cancels the singularity at s=0. The exact value
    # at zero is W(b)v(b), but Gauss nodes never include the endpoint.
    arch_window = integrate(lambda s: j(s) * (2 * inner - qW(s)), 0, b, rule)
    arch_window += integrate(lambda s: j(s) * (2 * inner - qW(s)), b, L, rule)
    J_L = mp.log(mp.mpf(5) / 3) / 2 + mp.atan(mp.mpf(1) / 4)
    arch_tail = 2 * inner * J_L

    prime = mp.mpf(0)
    prime_terms = {}
    for n in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16):
        # All and only prime powers <=16; Lambda(p^a)=log p.
        base = {4: 2, 8: 2, 9: 3, 16: 2}.get(n, n)
        term = -mp.log(base) / mp.sqrt(n) * qW(mp.log(n))
        prime += term
        prime_terms[str(n)] = mp.nstr(term, 45)

    kw = diagonal + arch_window + arch_tail + prime + pole
    correction = lam * inner  # <P_m W,A_m v> for the selected eigenvector
    beta = kw - correction
    X = khout - beta
    return {
        "order": order,
        "inner_W_v": mp.nstr(inner, 50),
        "k_W_components": {
            "diagonal_minus_cstar_inner": mp.nstr(diagonal, 50),
            "arch_paired_difference_0_to_L": mp.nstr(arch_window, 50),
            "arch_s_gt_L_exact_tail": mp.nstr(arch_tail, 50),
            "prime_powers_2_to_16": prime_terms,
            "prime_sum": mp.nstr(prime, 50),
            "p_pole_product": mp.nstr(pole, 50),
            "q_pole_product": "0 by parity",
        },
        "k_W_v": mp.nstr(kw, 50),
        "projection_correction_lambda_inner_W_v": mp.nstr(correction, 50),
        "k_beta_v": mp.nstr(beta, 50),
        "k_hout_v_reused": mp.nstr(khout, 50),
        "X_signed": mp.nstr(X, 50),
        "abs_X_over_B_midpoint": mp.nstr(abs(X) / B, 40),
        "B_midpoint_reused": mp.nstr(B, 50),
    }


def main():
    started = time.monotonic()
    signal.signal(signal.SIGALRM, lambda _s, _f: (_ for _ in ()).throw(TimeoutError("120s cap")))
    signal.setitimer(signal.ITIMER_REAL, TIME_CAP)
    out = {
        "status": "INCOMPLETE",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "literal m=N=16 selected even eigenvector i=1; no range scan",
        "formula": "X=k(h_out,v)-k(W,v)+<P_m W,A_m v>",
        "source_partial_sha256": digest(SOURCE),
        "eigenpair_sha256": digest(EIGEN),
        "orders": ORDERS,
        "mpmath_dps": MP_DPS,
        "W_theta_terms": W_THETA_TERMS,
        "W_images": "ell=+/-1",
        "h_out_input": "preserved 50-dps physical diagnostic; theta=12, prime powers<=64, arch S=L+0.3, pole tail b+1",
        "results": [],
    }
    try:
        mp.mp.dps = MP_DPS
        ctx.dps = 90
        source = json.loads(SOURCE.read_text())
        eigen = json.loads(EIGEN.read_text())
        if source.get("last_completed_stage") != "direct physical k(h_out,v)":
            raise ValueError("preserved source is not the expected partial run")
        if source["input_sha256"] != digest(EIGEN):
            raise ValueError("preserved source/eigenpair identity changed")
        modes = eigen["selected_eigenvector"]["fourier_modes_minus16_to_plus16"]
        coeff = [midpoint(item["ball"]) for item in modes]
        norm = mp.sqrt(mp.fsum(c*c for c in coeff))
        coeff = [c/norm for c in coeff]
        lam = midpoint(eigen["eigensolver"]["selected_eigenvalue_i1"]["ball"])
        khout = mp.mpf(source["k_hout"]["value_mpmath_midpoint"])
        B = midpoint(source["input"]["B_abs_lambda_times_overlap"]["ball"])
        b = mp.log(M) / 2
        u = mp.exp(2 * b)
        def theta_term(n):
            return mp.exp(b / 2) * (
                16 * mp.pi**2 * n**4 * u**2 - 24 * mp.pi * n**2 * u
            ) * mp.exp(-mp.pi * n**2 * u)
        h1, h2, h3 = (theta_term(n) for n in (1, 2, 3))
        out["W_theta_truncation_diagnostic"] = {
            "minimum_theta_argument": "b=log(16)/2",
            "h_n1_at_b": mp.nstr(h1, 20),
            "h_n2_at_b": mp.nstr(h2, 20),
            "first_omitted_h_n3_at_b": mp.nstr(h3, 20),
            "abs_n3_over_n1_at_b": mp.nstr(abs(h3/h1), 20),
            "interpretation": "terms decay much faster for x>b; no propagated error certificate",
        }
        for order in ORDERS:
            t = time.monotonic()
            out["results"].append(compute(order, coeff, lam, khout, B))
            out["last_order_seconds"] = round(time.monotonic()-t, 3)
            OUTPUT.write_text(json.dumps(out, indent=2) + "\n")
            print(f"completed order {order} in {out['last_order_seconds']}s", flush=True)
        a, z = out["results"]
        out["order_difference_X"] = mp.nstr(mp.mpf(z["X_signed"])-mp.mpf(a["X_signed"]), 35)
        out["order_difference_k_W"] = mp.nstr(mp.mpf(z["k_W_v"])-mp.mpf(a["k_W_v"]), 35)
        L = mp.log(M)
        S = L + mp.mpf("0.3")
        arch_tail_indicator = (
            2 * mp.sqrt(L) * 1000
            * mp.exp(mp.mpf(9) * (S - L/2) / 2 - mp.pi * mp.exp(2 * (S - L/2)))
            * (mp.log((1 + mp.exp(-S/2)) / (1 - mp.exp(-S/2))) / 2
               + mp.atan(mp.exp(-S/2)))
        )
        absX = abs(mp.mpf(z["X_signed"]))
        out["quarter_B_context_diagnostic"] = {
            "B_over_4": mp.nstr(B / 4, 25),
            "reused_hout_arch_tail_coarse_envelope": mp.nstr(arch_tail_indicator, 25),
            "abs_X_plus_that_envelope": mp.nstr(absX + arch_tail_indicator, 25),
            "ratio_to_B": mp.nstr((absX + arch_tail_indicator) / B, 25),
            "unspent_B_over_4_margin_before_other_errors": mp.nstr(B/4 - absX - arch_tail_indicator, 25),
            "interpretation": "one coarse omitted-tail envelope fits the quarter-B budget; other source, quadrature, and vector errors are not certified",
        }
        out["status"] = "FINITE_M16_DIRECT_X_NUMERICAL_DIAGNOSTIC_NOT_A_CERTIFICATE"
        out["limitations"] = [
            "Fixed quadrature order difference is a convergence diagnostic, not an error bound.",
            "The reused k(h_out,v) has large signed cancellation and no propagated quadrature/tail certificate.",
            "The previous coarse h_out arch-tail envelope at S=L+0.3 is 4.7333e-34, larger than this X; the displayed sign is not certified.",
            "W uses theta n<=2 and images |ell|=1; omitted tails are not rigorously propagated.",
            "The full relative F/X error budget and cofinal source estimate remain open.",
        ]
    except Exception as exc:
        out["error"] = f"{type(exc).__name__}: {exc}"
        raise
    finally:
        out["runtime_seconds"] = round(time.monotonic()-started, 3)
        OUTPUT.write_text(json.dumps(out, indent=2) + "\n")
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == "__main__":
    main()
