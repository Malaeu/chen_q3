#!/usr/bin/env python3
"""Direct physical-space m=16 diagnostic for the NOESCAPE exterior term.

This reads the retained Arb eigenvector and evaluates

    X(v) = k(h_out, v) - k(W - P_m W, v)
         = k(h_out, v) - k(W, v) + <P_m W, A_m v>

in the full source form.  It is one finite diagnostic, not a certified
F/X discriminator or a proof.  The source-form quadratures use mpmath
midpoints; only the normalized eigenvector and B=|lambda_1 <h,v>| receive
Arb enclosures.  Finite theta/image/prime cutoffs and the absent rigorous
quadrature propagation are recorded in the output.
"""

from __future__ import annotations

import hashlib
import json
import signal
import sys
import time
from pathlib import Path
from typing import Any

sys.dont_write_bytecode = True

from flint import acb, arb, ctx  # noqa: E402
import mpmath as mp  # noqa: E402

HERE = Path(__file__).resolve().parent
INPUT = HERE / "noescape_m16_eigenpair.json"
OUTPUT = HERE / "noescape_m16_direct_x.json"
M = 16
THETA_TERMS = 12
IMAGE_MAX = 1
PRIME_CUTOFF = 64
MP_DPS = 50
TIME_BUDGET_SECONDS = 80


class DiagnosticTimeout(TimeoutError):
    pass


def _alarm(_signum: int, _frame: Any) -> None:
    raise DiagnosticTimeout(f"wall-time cap {TIME_BUDGET_SECONDS}s reached")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def arb_record(value: arb) -> dict[str, str]:
    return {"ball": str(value), "lower": str(value.lower()), "upper": str(value.upper())}


def mp_midpoint(value: arb) -> mp.mpf:
    return mp.mpf(value.mid().str(MP_DPS, radius=False))


def theta_arb(x: acb) -> acb:
    """The displayed positive theta source, truncated after 12 terms."""
    u = (2 * x).exp()
    prefactor = (x / 2).exp()
    total = acb(0)
    pi = arb.pi()
    for n in range(1, THETA_TERMS + 1):
        na = arb(n)
        n2u = na * na * u
        total += (16 * pi**2 * na**4 * u**2 - 24 * pi * n2u) * (-pi * n2u).exp()
    return prefactor * total


def normalized_arb_input(data: dict[str, Any]) -> tuple[list[arb], arb, arb, arb]:
    modes = data["selected_eigenvector"]["fourier_modes_minus16_to_plus16"]
    order = data["selected_eigenvector"]["mode_order"]
    if order != list(range(-M, M + 1)) or len(modes) != 2 * M + 1:
        raise ValueError("retained vector is not in the expected -16..16 Fourier order")
    coeffs = [arb(item["ball"]) for item in modes]
    norm2 = sum((coefficient**2 for coefficient in coeffs), arb(0))
    if 1 not in norm2:
        raise ValueError("retained full Fourier vector norm-squared does not enclose one")
    norm = norm2.sqrt()
    unit = [coefficient / norm for coefficient in coeffs]
    lam = arb(data["eigensolver"]["selected_eigenvalue_i1"]["ball"])
    return unit, norm2, norm, lam


def overlap_and_B(unit: list[arb], lam: arb) -> tuple[arb, arb, arb]:
    ctx.dps = 50
    ctx.threads = 1
    L = arb(M).log()
    b = L / 2
    sqrtL = L.sqrt()
    positive = unit[M:]

    def v_acb(x: acb) -> acb:
        total = acb(positive[0])
        for n in range(1, M + 1):
            total += 2 * positive[n] * (2 * arb.pi() * n * (x + b) / L).cos()
        return total / sqrtL

    pieces = []
    for i in range(16):
        left = b * i / 16
        right = b * (i + 1) / 16
        pieces.append(acb.integral(
            lambda x, _analytic: theta_arb(x) * v_acb(x),
            left,
            right,
            rel_tol=arb("1e-25"),
            abs_tol=arb("1e-25"),
        ).real)
    integral = sum(pieces, arb(0)) * 2
    # For x>=0, the n>=13 theta tail is below 1e-210 uniformly on [0,b];
    # this deliberately coarse radius also covers its integral against the
    # unit finite Fourier vector.
    overlap = integral + arb(0, arb("1e-210"))
    B = abs(lam * overlap)
    return overlap, B, integral


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def von_mangoldt(n: int) -> mp.mpf:
    if n < 2:
        return mp.mpf(0)
    for p in range(2, n + 1):
        if not is_prime(p) or n % p:
            continue
        q = n
        while q % p == 0:
            q //= p
        return mp.log(p) if q == 1 else mp.mpf(0)
    return mp.mpf(0)


def coarse_C0() -> mp.mpf:
    # 1000 is a coarse envelope constant for 16*pi^2 sum n^4 exp(-pi(n^2-1)).
    return mp.mpf(1000)


def prime_tail_bound(cutoff: int, L: mp.mpf) -> mp.mpf:
    """Geometric majorant for the NOESCAPE h_out prime tail (n>cutoff)."""
    n = mp.mpf(cutoff + 1)
    a = mp.pi / M
    first = mp.log(n) * n**4 * mp.exp(-a * n**2)
    q = ((n + 1) / n) ** 5 * mp.exp(-a * (2 * n + 1))
    if q >= 1:
        raise ValueError("prime tail geometric ratio is not below one")
    return 2 * mp.sqrt(L) * coarse_C0() * mp.mpf(M) ** (-mp.mpf(9) / 4) * first / (1 - q)


def main() -> int:
    started = time.monotonic()
    current_stage = "read retained eigenvector"
    partial: dict[str, Any] = {
        "status": "INCOMPLETE_TIMEOUT_OR_ERROR",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "m=16, selected even-sector index i=1 only",
        "formula": "X(v)=k(h_out,v)-k(beta,v), beta=W-P_mW; k(beta,v)=k(W,v)-<P_mW,A_m v>",
        "input_path": str(INPUT),
        "input_sha256": sha256(INPUT),
        "last_completed_stage": None,
    }
    signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, TIME_BUDGET_SECONDS)
    try:
        ctx.threads = 1
        ctx.dps = 90
        data = json.loads(INPUT.read_text(encoding="utf-8"))
        unit_arb, norm2, norm, lam_arb = normalized_arb_input(data)
        partial["last_completed_stage"] = "Arb-normalized retained vector"
        partial["input"] = {
            "selected_index_zero_based": 1,
            "normalization": "full -16..16 Arb interval vector divided by sqrt(sum c_n^2)",
            "input_norm_squared": arb_record(norm2),
            "normalization_factor": arb_record(norm),
            "selected_eigenvalue": arb_record(lam_arb),
        }
        overlap_arb, B_arb, overlap_integral = overlap_and_B(unit_arb, lam_arb)
        partial["last_completed_stage"] = "Arb-normalized retained vector and physical h overlap"
        partial["input"] = {
            "selected_index_zero_based": 1,
            "normalization": "full -16..16 Arb interval vector divided by sqrt(sum c_n^2)",
            "input_norm_squared": arb_record(norm2),
            "normalization_factor": arb_record(norm),
            "selected_eigenvalue": arb_record(lam_arb),
            "physical_overlap_h_v": arb_record(overlap_arb),
            "B_abs_lambda_times_overlap": arb_record(B_arb),
            "overlap_arb_integral_before_theta_tail_radius": arb_record(overlap_integral),
            "overlap_method": "python-flint Arb quadrature on 2*integral_0^(log(16)/2) h(x)v(x) dx",
            "theta_terms": THETA_TERMS,
            "theta_tail_radius_added": "1e-210 (coarse absolute radius for the omitted n>=13 theta terms)",
        }

        mp.mp.dps = MP_DPS
        L = mp.log(M)
        b = L / 2
        sqrtL = mp.sqrt(L)
        mp_modes = [mp_midpoint(value) for value in unit_arb]
        c = {n: mp_modes[n + M] for n in range(-M, M + 1)}
        c0 = c[0]
        cp = {n: c[n] for n in range(1, M + 1)}
        pi = mp.pi
        cstar = mp.euler + mp.log(8 * pi) + pi / 2

        def h(x: mp.mpf) -> mp.mpf:
            # All calls below have x>=0. Twelve terms include the whole-line
            # core accurately at x=0 and vastly overresolve the m=16 tails.
            u = mp.exp(2 * x)
            return mp.exp(x / 2) * mp.fsum(
                (16 * pi**2 * n**4 * u**2 - 24 * pi * n**2 * u)
                * mp.exp(-pi * n**2 * u)
                for n in range(1, THETA_TERMS + 1)
            )

        def v(x: mp.mpf) -> mp.mpf:
            return (c0 + 2 * mp.fsum(cp[n] * mp.cos(2 * pi * n * (x + b) / L) for n in range(1, M + 1))) / sqrtL

        def vprime(x: mp.mpf) -> mp.mpf:
            return -2 * mp.fsum(
                cp[n] * (2 * pi * n / L) * mp.sin(2 * pi * n * (x + b) / L)
                for n in range(1, M + 1)
            ) / sqrtL

        def W(x: mp.mpf) -> mp.mpf:
            z = abs(x)
            return mp.fsum(h(z + ell * L) + h(ell * L - z) for ell in range(1, IMAGE_MAX + 1))

        def quad(fun: Any, a: mp.mpf, z: mp.mpf) -> mp.mpf:
            if z <= a:
                return mp.mpf(0)
            points = [a]
            if a < 0 < z:
                points.append(mp.mpf(0))
            points.append(z)
            return mp.quad(fun, points)

        def j(s: mp.mpf) -> mp.mpf:
            if s == 0:
                return mp.inf
            return mp.exp(-s / 2) / (1 - mp.exp(-2 * s))

        def qout(s: mp.mpf) -> mp.mpf:
            if s == 0:
                return mp.mpf(0)
            lo = max(-b, b - s)
            return 2 * quad(lambda y: h(y + s) * v(y), lo, b)

        def qW(s: mp.mpf) -> mp.mpf:
            if s >= L:
                return mp.mpf(0)
            return 2 * quad(lambda x: W(x) * v(x + s), -b, b - s)

        current_stage = "direct physical k(h_out,v)"
        S = L + mp.mpf("0.3")
        h_b = h(b)
        v_b = v(b)

        def hout_arch_integrand(s: mp.mpf) -> mp.mpf:
            if s == 0:
                return h_b * v_b
            return j(s) * qout(s)

        hout_arch_positive = quad(hout_arch_integrand, mp.mpf(0), L)
        hout_arch_positive += quad(hout_arch_integrand, L, S)
        hout_arch = -hout_arch_positive

        hout_prime_sum = mp.mpf(0)
        for n in range(2, PRIME_CUTOFF + 1):
            lamn = von_mangoldt(n)
            if lamn:
                hout_prime_sum += lamn / mp.sqrt(n) * qout(mp.log(n))
        hout_prime = -hout_prime_sum

        p = lambda x: mp.sqrt(2) * mp.cosh(x / 2)
        h_out_p = 2 * mp.quad(lambda x: h(x) * p(x), [b, b + mp.mpf("0.25"), b + mp.mpf("0.6"), b + 1])
        p_v = 2 * quad(lambda x: v(x) * p(x), mp.mpf(0), b)
        hout_pole = h_out_p * p_v
        k_hout = hout_arch + hout_prime + hout_pole
        partial["last_completed_stage"] = current_stage
        partial["k_hout"] = {
            "value_mpmath_midpoint": mp.nstr(k_hout, 50),
            "quadrature_settings": {
                "method": "nested mpmath midpoint quadrature at 50 dps; no rigorous enclosure",
                "arch_upper_limit": "S=L+0.3",
                "prime_power_upper_limit": PRIME_CUTOFF,
                "p_pole_integral_interval": "both tails integrated from b to b+1; further tail not propagated",
            },
            "components": {
                "archimedean_minus_integral_0_to_S": mp.nstr(hout_arch, 50),
                "all_prime_powers_2_to_cutoff_with_Lambda_over_sqrt_n": mp.nstr(hout_prime, 50),
                "p_pole_product": mp.nstr(hout_pole, 50),
                "q_pole_product": "0 by even/odd parity",
                "diagonal_inner_product": "0 by disjoint supports",
            },
        }

        current_stage = "direct physical k(W,v)"
        w_inner = 2 * quad(lambda x: W(x) * v(x), mp.mpf(0), b)

        def dW(s: mp.mpf) -> mp.mpf:
            if s == 0:
                # lim_{s->0} j(s)*(2<W,v>-Q_W,v(s)) = W(b)v(b);
                # the integral of W*v' vanishes by even/odd parity.
                return 2 * w_inner
            first = quad(lambda x: W(x) * (v(x) - v(x + s)), -b, b - s)
            second = quad(lambda x: W(x) * v(x), b - s, b)
            return 2 * (first + second)

        def w_arch_integrand(s: mp.mpf) -> mp.mpf:
            if s == 0:
                return W(b) * v(b)
            return j(s) * dW(s)

        w_arch_window = quad(w_arch_integrand, mp.mpf(0), b)
        w_arch_window += quad(w_arch_integrand, b, L)
        jL = mp.mpf("0.5") * mp.log(mp.mpf(5) / 3) + mp.atan(mp.mpf(1) / 4)
        w_arch_tail = 2 * w_inner * jL
        w_arch = w_arch_window + w_arch_tail

        w_prime_sum = mp.mpf(0)
        for n in range(2, M + 1):
            lamn = von_mangoldt(n)
            if lamn:
                w_prime_sum += lamn / mp.sqrt(n) * qW(mp.log(n))
        w_prime = -w_prime_sum
        w_p = 2 * quad(lambda x: W(x) * p(x), mp.mpf(0), b)
        w_pole = w_p * p_v
        w_diagonal = -cstar * w_inner
        k_W = w_diagonal + w_arch + w_prime + w_pole

        # Since A_m v=lambda_1 v and v lies in V_m, <P_m W,A_m v>
        # equals lambda_1 <W,v>.  This is the direct finite correction.
        projection_correction = mp_midpoint(lam_arb) * w_inner
        k_beta = k_W - projection_correction
        X = k_hout - k_beta
        Bmid = mp_midpoint(B_arb)
        ratio = abs(X) / Bmid if Bmid != 0 else mp.nan
        partial["last_completed_stage"] = current_stage

        # The following envelopes identify omitted terms but are not propagated
        # through all nested quadratures; output therefore remains diagnostic.
        prime_remainder = prime_tail_bound(PRIME_CUTOFF, L)
        mp_S = S
        arch_cut_remainder = (
            2 * mp.sqrt(L) * coarse_C0()
            * mp.exp(mp.mpf(9) * (S - b) / 2 - pi * mp.exp(2 * (S - b)))
            * (mp.mpf("0.5") * mp.log((1 + mp.exp(-S / 2)) / (1 - mp.exp(-S / 2))) + mp.atan(mp.exp(-S / 2)))
        )
        image_remainder_point = 3 * b
        image_remainder = 2 * coarse_C0() * mp.exp(mp.mpf(9) * image_remainder_point / 2 - pi * mp.exp(2 * image_remainder_point))

        partial.update({
            "status": "FINITE_M16_DIRECT_X_NUMERICAL_DIAGNOSTIC_NOT_A_CERTIFICATE",
            "route_status": "CHALLENGER_NOT_RH",
            "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
            "scope": "literal even CCM cell m=N=16, retained selected eigenvector i=1 only; no range scan",
            "formula": "X(v)=k(h_out,v)-k(beta,v), beta=W-P_mW; k(beta,v)=k(W,v)-<P_mW,A_m v>",
            "k_W_components": {
                "diagonal_minus_cstar_inner": mp.nstr(w_diagonal, 50),
                "arch_paired_difference_on_0_to_L": mp.nstr(w_arch_window, 50),
                "arch_s_gt_L_exact_tail_2_inner_times_J_L": mp.nstr(w_arch_tail, 50),
                "J_L_exact_m16": "0.5*log(5/3)+atan(1/4)",
                "finite_prime_powers_2_to_16": mp.nstr(w_prime, 50),
                "p_pole_product": mp.nstr(w_pole, 50),
                "q_pole_product": "0 by even/odd parity",
                "sum": mp.nstr(k_W, 50),
            },
            "projection_correction_lambda_times_inner_W_v": mp.nstr(projection_correction, 50),
            "k_beta_direct_from_W_minus_projection": mp.nstr(k_beta, 50),
            "X_signed_mpmath_midpoint": mp.nstr(X, 50),
            "abs_X_over_B_midpoint_diagnostic_only": mp.nstr(ratio, 30),
            "numerical_method": {
                "source_form": "full literal form (1.4): diagonal, paired arch term, all included prime powers, p/q poles",
                "eigenvector_midpoints": "Arb-normalized retained coefficients converted to mpmath midpoints",
                "mpmath_dps": MP_DPS,
                "quadrature": "nested mpmath quadrature; no rigorous quadrature enclosure",
                "physical_h_overlap_and_B": "python-flint Arb quadrature; h theta tail radius added",
                "image_terms_in_W": "ell=+/-1; omitted |ell|>=2",
                "h_out_prime_powers": f"all Lambda(n)!=0 for 2<=n<={PRIME_CUTOFF}; terms above cutoff omitted",
                "h_out_arch": f"integrated through S=L+0.3={mp.nstr(S, 20)}; tail omitted",
            },
            "omitted_term_indicators_not_a_full_error_certificate": {
                "h_out_prime_tail_envelope_using_NOESCAPE_4_13": mp.nstr(prime_remainder, 20),
                "h_out_arch_tail_envelope_using_theta_bound": mp.nstr(arch_cut_remainder, 20),
                "first_omitted_W_image_pointwise_theta_envelope_at_3b": mp.nstr(image_remainder, 20),
                "all_bound_constants_and_quadrature_errors_propagated": False,
            },
            "limitations": [
                "The source-form values are mpmath numerical midpoints, not rigorous intervals.",
                "Finite prime and image remainders are indicated but not propagated through every nested integral.",
                "The full relative F/X error budget, Fourier/source map and quadrature/vector errors are not certified.",
                "This one-cell X/B comparison is diagnostic only and proves no cofinal statement or RH implication.",
                "CHALLENGER_NOT_RH; PX_RH_CLAIM remains NOT_MADE.",
            ],
            "runtime_seconds": round(time.monotonic() - started, 3),
        })
        OUTPUT.write_text(json.dumps(partial, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        return 0
    except DiagnosticTimeout as exc:
        partial["error"] = str(exc)
        partial["last_active_stage"] = current_stage
        partial["runtime_seconds"] = round(time.monotonic() - started, 3)
        OUTPUT.write_text(json.dumps(partial, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(json.dumps(partial, indent=2, ensure_ascii=False), flush=True)
        return 124
    except Exception as exc:
        partial["error"] = f"{type(exc).__name__}: {exc}"
        partial["last_active_stage"] = current_stage
        partial["runtime_seconds"] = round(time.monotonic() - started, 3)
        OUTPUT.write_text(json.dumps(partial, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(json.dumps(partial, indent=2, ensure_ascii=False), flush=True)
        raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == "__main__":
    raise SystemExit(main())
