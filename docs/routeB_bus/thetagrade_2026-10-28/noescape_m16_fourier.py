#!/usr/bin/env python3
"""Finite M=64,96 Fourier-tail diagnostic for the retained m=16 vector.

This evaluates the signed F term in NOESCAPE (4.7)--(4.10), using the closed
off-diagonal alpha/moment formula.  It neither changes the eigenproblem nor
certifies an infinite Fourier tail, the source quadrature, or the eigenvector.
"""

from __future__ import annotations

import hashlib
import json
import signal
import sys
import time
from functools import lru_cache
from pathlib import Path

sys.dont_write_bytecode = True

import mpmath as mp
from flint import arb, ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
EIGEN = HERE / "noescape_m16_eigenpair.json"
DIRECT_X = HERE / "noescape_m16_direct_x.json"
FAST_X = HERE / "noescape_m16_direct_x_fast.json"
OUTPUT = HERE / "noescape_m16_fourier.json"
M = 16
ORDERS = (64, 96)
DPS = 80
TIME_CAP = 90


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def midpoint(value: str) -> mp.mpf:
    return mp.mpf(arb(value).mid().str(DPS, radius=False))


def main() -> None:
    started = time.monotonic()
    signal.signal(signal.SIGALRM, lambda _s, _f: (_ for _ in ()).throw(TimeoutError("90s cap")))
    signal.setitimer(signal.ITIMER_REAL, TIME_CAP)
    out: dict[str, object] = {
        "status": "INCOMPLETE",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "m=N=16; retained zero-based eigenvector i=1; leakage only; no new eigenproblem or cell scan",
        "formula": "F_M = sum_{16<|n|<=M} (-1)^n H(2*pi*n/L)/sqrt(L) * sum_{|j|<=16} K_L(n,j) c_j",
        "source_normalization": "H(t)=4*xi(1/2-i*t); c_j are the retained normalized full-mode coordinates",
        "kernel_mapping": {
            "archimedean_moment": "mom_n = integral_0^L exp(x/2)*sin(2*pi*n*x/L)/(2*sinh(x)) dx",
            "builder_alpha": "alpha_n = mom_n/pi; alpha_-n=-alpha_n",
            "offdiagonal_wr": "(alpha_j-alpha_n)/(n-j) = (mom_j-mom_n)/(pi*(n-j))",
            "K_L": "w02 - wr - sum_{k=p^a<=16} (log p)/sqrt(k) * (sin(2*pi*j*log(k)/L)-sin(2*pi*n*log(k)/L))/(pi*(n-j))",
            "closed_alpha_source": "edge_ledger_build.CCMArbBuilder._alpha; mpmath hyp2f1/digamma translation, no nested high-mode quadrature",
            "prime_cutoff": "all prime powers k<=16, unchanged from the eigenproblem",
        },
        "orders": ORDERS,
        "mpmath_dps": DPS,
        "inputs_sha256": {},
        "results": [],
    }
    try:
        mp.mp.dps = DPS
        ctx.dps = 120
        L = mp.log(M)
        pi = mp.pi
        sqrtL = mp.sqrt(L)
        z = mp.mpf(1) / (M * M)

        eigen = json.loads(EIGEN.read_text(encoding="utf-8"))
        direct = json.loads(DIRECT_X.read_text(encoding="utf-8"))
        fast = json.loads(FAST_X.read_text(encoding="utf-8"))
        expected_eigen_hash = digest(EIGEN)
        if direct["input_sha256"] != expected_eigen_hash:
            raise ValueError("direct-X input does not bind the retained eigenpair")
        if fast["eigenpair_sha256"] != expected_eigen_hash:
            raise ValueError("fast-X input does not bind the retained eigenpair")
        if fast["source_partial_sha256"] != digest(DIRECT_X):
            raise ValueError("fast-X input does not bind direct_x.json")
        out["inputs_sha256"] = {
            "eigenpair_json": expected_eigen_hash,
            "direct_x_json": digest(DIRECT_X),
            "direct_x_fast_json": digest(FAST_X),
        }

        modes = eigen["selected_eigenvector"]["fourier_modes_minus16_to_plus16"]
        coeff_raw = [midpoint(row["ball"]) for row in modes]
        norm_raw = mp.sqrt(mp.fsum(c * c for c in coeff_raw))
        coeff = [c / norm_raw for c in coeff_raw]
        parity_defect = max(abs(coeff[M - j] - coeff[M + j]) for j in range(1, M + 1))
        out["retained_vector"] = {
            "selected_index_zero_based": eigen["eigensolver"]["selected_index_zero_based"],
            "normalization": "midpoints of the stored real-coordinate Arb balls, divided by sqrt(sum_j c_j^2)",
            "raw_norm_midpoint": mp.nstr(norm_raw, 30),
            "normalized_norm_midpoint": mp.nstr(mp.sqrt(mp.fsum(c * c for c in coeff)), 30),
            "max_even_pair_midpoint_defect": mp.nstr(parity_defect, 12),
            "eigenvalue_midpoint": mp.nstr(midpoint(eigen["eigensolver"]["selected_eigenvalue_i1"]["ball"]), 40),
        }

        # alpha_n is the closed form in edge_ledger_build.CCMArbBuilder._alpha.
        # The source's alpha is moment/pi; this keeps the 1/pi in wr exact.
        @lru_cache(maxsize=None)
        def alpha_pos(n: int) -> mp.mpf:
            a = mp.mpf(1) / 4 + 1j * pi * n / L
            hyp = mp.hyp2f1(1, a, a + 1, z)
            term = (2 * L / (L + 4 * pi * 1j * n)) * hyp
            return mp.re((mp.exp(-L / 2) * mp.im(term) + mp.im(mp.digamma(a)) / 2) / pi)

        def alpha_signed(n: int) -> mp.mpf:
            return alpha_pos(abs(n)) if n >= 0 else -alpha_pos(abs(n))

        prime_powers = ((2, 2), (3, 3), (4, 2), (5, 5), (7, 7), (8, 2), (9, 3), (11, 11), (13, 13), (16, 2))

        @lru_cache(maxsize=None)
        def KL(n: int, j: int) -> mp.mpf:
            if n == j:
                raise ValueError("the Fourier leakage rows must be off-diagonal")
            w02 = (
                32 * L * mp.sinh(L / 4) ** 2 * (L**2 - 16 * pi**2 * j * n)
                / ((L**2 + 16 * pi**2 * j**2) * (L**2 + 16 * pi**2 * n**2))
            )
            wr = (alpha_signed(j) - alpha_signed(n)) / (n - j)
            prime = mp.fsum(
                mp.log(p) / mp.sqrt(k)
                * (mp.sin(2 * pi * j * mp.log(k) / L) - mp.sin(2 * pi * n * mp.log(k) / L))
                / (pi * (n - j))
                for k, p in prime_powers
            )
            return w02 - wr - prime

        # Independent in-window source control: the existing full-center
        # literal matrix computes its moment integrals directly by quadrature.
        fokas = ROOT / "docs/routeB_bus/fokas_k_sign_2026-09-25"
        sys.path.insert(0, str(fokas))
        import full_center_probe as full_probe  # noqa: E402

        reference = full_probe.matrix_K(M)
        control_errors = [
            abs(KL(n, j) - reference[M + n, M + j])
            for n in range(-M, M + 1)
            for j in range(-M, M + 1)
            if n != j
        ]
        max_ctrl = max(control_errors)
        max_ref = max(abs(reference[M + n, M + j]) for n in range(-M, M + 1) for j in range(-M, M + 1) if n != j)
        out["in_window_offdiagonal_source_control"] = {
            "reference": "full_center_probe.matrix_K(16), independent direct moment quadrature",
            "entries_compared": len(control_errors),
            "max_abs_difference": mp.nstr(max_ctrl, 24),
            "max_difference_over_max_reference_entry": mp.nstr(max_ctrl / max_ref, 18),
            "quadrature_is_diagnostic": True,
        }

        @lru_cache(maxsize=None)
        def H(n: int) -> mp.mpf:
            t = 2 * pi * n / L
            s = mp.mpf(1) / 2 - 1j * t
            xi = s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)
            imag = abs(mp.im(4 * xi))
            max_h_imag[0] = max(max_h_imag[0], imag)
            return 4 * mp.re(xi)

        max_h_imag = [mp.mpf(0)]
        pair_terms: dict[int, mp.mpf] = {}
        max_pair_defect = mp.mpf(0)
        max_kpsi = mp.mpf(0)
        for n in range(M + 1, max(ORDERS) + 1):
            kp = mp.fsum(KL(n, j) * coeff[M + j] for j in range(-M, M + 1))
            km = mp.fsum(KL(-n, j) * coeff[M + j] for j in range(-M, M + 1))
            max_pair_defect = max(max_pair_defect, abs(kp - km))
            max_kpsi = max(max_kpsi, abs(kp), abs(km))
            # H(-t)=H(t) for xi; both signed modes are summed explicitly.
            pair_terms[n] = (-1) ** n * H(n) * (kp + km) / sqrtL

        partials = {}
        for order in ORDERS:
            partials[order] = mp.fsum(pair_terms[n] for n in range(M + 1, order + 1))
            largest_n = max(range(M + 1, order + 1), key=lambda n: abs(pair_terms[n]))
            out["results"].append({
                "order": order,
                "F_signed": mp.nstr(partials[order], 45),
                "first_positive_mode_term": mp.nstr(pair_terms[M + 1], 25),
                "last_mode_term": mp.nstr(pair_terms[order], 25),
                "largest_abs_mode_term": mp.nstr(abs(pair_terms[largest_n]), 25),
                "largest_term_n": largest_n,
                "modes_in_pair_sum": order - M,
            })
            OUTPUT.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")

        overlap = midpoint(direct["input"]["physical_overlap_h_v"]["ball"])
        lam = midpoint(eigen["eigensolver"]["selected_eigenvalue_i1"]["ball"])
        x_signed = mp.mpf(fast["results"][-1]["X_signed"])
        lambda_h = lam * overlap
        residual64 = partials[64] + x_signed + lambda_h
        residual96 = partials[96] + x_signed + lambda_h
        out["closure_check_using_independent_X_and_direct_overlap"] = {
            "X_signed_from_direct_x_fast_order96": mp.nstr(x_signed, 45),
            "lambda_times_physical_overlap": mp.nstr(lambda_h, 45),
            "F64_plus_X_plus_lambda_overlap": mp.nstr(residual64, 45),
            "F96_plus_X_plus_lambda_overlap": mp.nstr(residual96, 45),
            "F96_minus_F64": mp.nstr(partials[96] - partials[64], 35),
            "abs_F96_minus_F64_over_abs_lambda_overlap": mp.nstr(abs(partials[96] - partials[64]) / abs(lambda_h), 25),
            "abs_closure_residual96_over_abs_lambda_overlap": mp.nstr(abs(residual96) / abs(lambda_h), 25),
            "interpretation": "signed finite-cell closure diagnostic; not an error enclosure or cofinal estimate",
        }
        out["symmetry_and_tail_diagnostics"] = {
            "max_abs_kpsi_plus_minus_defect_n17_to96": mp.nstr(max_pair_defect, 24),
            "max_abs_kpsi_plus_or_minus": mp.nstr(max_kpsi, 24),
            "max_abs_imaginary_residue_in_4xi": mp.nstr(max_h_imag[0], 24),
            "F_tail_after_96": "not bounded in this run; F64-to-F96 difference is convergence data only",
        }
        out["status"] = "FINITE_M16_FOURIER_TAIL_DIAGNOSTIC_NOT_A_CERTIFICATE"
        out["remaining_error"] = [
            "No analytic bound for the omitted |n|>96 Fourier tail was established; convergence alone is not certification.",
            "The full-center source control uses mpmath direct moment quadrature and is diagnostic.",
            "The retained Arb vector balls were reduced to midpoints and renormalized; eigenvector and eigenvalue enclosure errors were not propagated through F.",
            "The independently computed direct-X and overlap inputs retain their own quadrature/tail limitations recorded in noescape_m16_direct_x_fast.json and noescape_m16_direct_x.json.",
            "This finite cell cannot establish the cofinal NOESCAPE target.",
        ]
    finally:
        out["runtime_seconds"] = round(time.monotonic() - started, 3)
        OUTPUT.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == "__main__":
    main()
