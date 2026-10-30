#!/usr/bin/env python3
"""Arb enclosure for the finite m=16 Fourier leakage sum through |n|=96.

The omitted-tail expression is transcribed from
docs/routeB_bus/proshka/NOESCAPE_FOURIER_TAIL_2026-10-30.md and is still
pending independent mathematical review.  No X quadrature is performed here.
"""

from __future__ import annotations

import hashlib
import json
import platform
import signal
import sys
import time
from pathlib import Path
from typing import Any

sys.dont_write_bytecode = True

from flint import acb, arb, ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PHASE5 = ROOT / "docs/routeB_bus/phase5_scripts"
sys.path.insert(0, str(PHASE5))

import edge_ledger_build as edge  # noqa: E402

M = 16
FINITE_ORDER = 96
DPS = 120
TIME_CAP = 90
EIGEN = HERE / "noescape_m16_eigenpair.json"
DIRECT_X = HERE / "noescape_m16_direct_x.json"
FAST_X = HERE / "noescape_m16_direct_x_fast.json"
PRIOR_DIAGNOSTIC = HERE / "noescape_m16_fourier.json"
TAIL_NOTE = ROOT / "docs/routeB_bus/proshka/NOESCAPE_FOURIER_TAIL_2026-10-30.md"
OUTPUT = HERE / "noescape_m16_fourier_arb.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ball_record(value: arb) -> dict[str, str]:
    return {"ball": str(value), "lower": str(value.lower()), "upper": str(value.upper())}


def main() -> None:
    started = time.monotonic()
    signal.signal(signal.SIGALRM, lambda _s, _f: (_ for _ in ()).throw(TimeoutError("90s cap")))
    signal.setitimer(signal.ITIMER_REAL, TIME_CAP)
    out: dict[str, Any] = {
        "status": "INCOMPLETE",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "m=N=16; retained zero-based eigenvector i=1; finite Fourier sum only; no new eigenproblem or cell scan",
        "finite_formula": "F_96=sum_{16<|n|<=96} (-1)^n H(2*pi*n/L)/sqrt(L) * sum_{|j|<=16} K_L(n,j)c_j",
        "xi_formula": "H(t)=4*xi(1/2-i*t), xi(s)=s(s-1)/2*pi^(-s/2)*Gamma(s/2)*zeta(s)",
        "kernel_formula_mapping": {
            "moment": "M_n=integral_0^L exp(-s/2)/(1-exp(-2s))*sin(2*pi*n*s/L) ds",
            "closed_arch_coefficient": "CCMArbBuilder._alpha(n)=M_n/pi; alpha(-n)=-alpha(n)",
            "offdiagonal_arch_entry": "(alpha_j-alpha_n)/(n-j)=(M_j-M_n)/(pi*(n-j))",
            "entry": "K_L(n,j)=w02(n,j)-wr(n,j)-sum_{k=p^a<=16}(log(p)/sqrt(k))*q_nm(n,j,log(k))",
            "prime_cutoff": "the literal prime-power set k=2,3,4,5,7,8,9,11,13,16",
        },
        "exact_real_symmetry": "xi(conjugate(s))=conjugate(xi(s)) and xi(s)=xi(1-s), hence H(t) is real and even for real t; Acb imag boxes were checked to contain zero for every sampled n",
        "kernel_source": "edge_ledger_build.CCMArbBuilder._alpha, w02, q_nm, and prime-power set; only off-diagonal entries are evaluated, without enlarging/rebuilding the eigenproblem",
        "tail_bound_source": "docs/routeB_bus/proshka/NOESCAPE_FOURIER_TAIL_2026-10-30.md; candidate derivation pending independent mathreview",
        "environment": {"python": platform.python_version(), "python_flint": getattr(__import__("flint"), "__version__", "unknown"), "arb_dps": DPS},
        "inputs_sha256": {},
    }
    try:
        ctx.dps = DPS
        ctx.threads = 1
        eigen = json.loads(EIGEN.read_text(encoding="utf-8"))
        direct = json.loads(DIRECT_X.read_text(encoding="utf-8"))
        fast = json.loads(FAST_X.read_text(encoding="utf-8"))
        prior = json.loads(PRIOR_DIAGNOSTIC.read_text(encoding="utf-8"))
        eigen_sha = digest(EIGEN)
        if direct["input_sha256"] != eigen_sha or fast["eigenpair_sha256"] != eigen_sha:
            raise ValueError("retained direct-X inputs do not bind the same eigenpair")
        if fast["source_partial_sha256"] != digest(DIRECT_X):
            raise ValueError("fast-X input does not bind the preserved direct_x.json")
        if prior["inputs_sha256"]["eigenpair_json"] != eigen_sha:
            raise ValueError("prior finite diagnostic does not bind the retained eigenpair")
        out["inputs_sha256"] = {
            "eigenpair_json": eigen_sha,
            "direct_x_json": digest(DIRECT_X),
            "direct_x_fast_json_comparison_only": digest(FAST_X),
            "prior_fourier_diagnostic_json": digest(PRIOR_DIAGNOSTIC),
            "tail_note": digest(TAIL_NOTE),
        }

        # Keep the full Arb coordinate intervals, then interval-normalize them.
        mode_rows = eigen["selected_eigenvector"]["fourier_modes_minus16_to_plus16"]
        raw = [arb(row["ball"]) for row in mode_rows]
        raw_norm2 = sum((c * c for c in raw), arb(0))
        raw_norm = raw_norm2.sqrt()
        if not (0 < raw_norm):
            raise ArithmeticError("retained vector norm interval is not bounded away from zero")
        coeff = [c / raw_norm for c in raw]
        normalized_norm2 = sum((c * c for c in coeff), arb(0))
        if 1 not in normalized_norm2:
            raise ArithmeticError("interval-normalized coordinates do not enclose unit norm")
        def interval_max(a: arb, b: arb) -> arb:
            # max(a,b)=(a+b+|a-b|)/2 for real inputs; interval arithmetic
            # encloses the exact maximum even when the input balls overlap.
            return (a + b + abs(a - b)) / 2

        parity_defect = arb(0)
        for j in range(1, M + 1):
            parity_defect = interval_max(parity_defect, abs(coeff[M - j] - coeff[M + j]))
        out["vector_interval_normalization"] = {
            "source": "selected_eigenvector.fourier_modes_minus16_to_plus16 Arb balls",
            "normalization": "divide each stored coordinate ball by sqrt(sum_j c_j^2), with interval arithmetic",
            "raw_norm_squared": ball_record(raw_norm2),
            "normalization_factor": ball_record(raw_norm),
            "normalized_norm_squared": ball_record(normalized_norm2),
            "normalized_norm_squared_contains_one": True,
            "max_even_pair_interval_defect": ball_record(parity_defect),
        }

        # N remains 16. The builder's closed alpha formula is evaluated at
        # |n|>16 only for leakage rows; it does not build an enlarged matrix.
        builder = edge.CCMArbBuilder(M, M)
        L = builder.L
        pi = builder.pi
        sqrtL = L.sqrt()
        alpha_cache: dict[int, arb] = {}

        def alpha_signed(n: int) -> arb:
            k = abs(n)
            if k not in alpha_cache:
                alpha_cache[k] = builder._alpha(k)
            return alpha_cache[k] if n >= 0 else -alpha_cache[k]

        prime_powers = builder.prime_powers
        kernel_cache: dict[tuple[int, int], arb] = {}

        def kernel(n: int, j: int) -> arb:
            key = (n, j)
            if key in kernel_cache:
                return kernel_cache[key]
            if n == j:
                raise ValueError("all leakage matrix entries must be off-diagonal")
            wr = (alpha_signed(j) - alpha_signed(n)) / (n - j)
            prime = arb(0)
            for k, p in prime_powers:
                prime += builder.log_prime[p] / arb(k).sqrt() * builder.q_nm(n, j, builder.log_k[k])
            result = builder.w02(n, j) - wr - prime
            kernel_cache[key] = result
            return result

        def xi_h(n: int) -> tuple[arb, arb]:
            t = 2 * pi * n / L
            s = acb(arb(1) / 2, -t)
            pi_power = (-s / 2 * pi.log()).exp()
            xi = (s * (s - 1) / 2) * pi_power * (s / 2).gamma() * s.zeta()
            h = 4 * xi
            if 0 not in h.imag:
                raise ArithmeticError(f"exact real H(t) not enclosed by imag box at n={n}: {h.imag}")
            return h.real, h.imag

        F64 = arb(0)
        F96 = arb(0)
        h_imag_boxes: dict[str, dict[str, str]] = {}
        h_real_boxes: dict[str, dict[str, str]] = {}
        max_kpsi_upper = arb(0)
        mode_pair_defect_upper = arb(0)
        for n in range(M + 1, FINITE_ORDER + 1):
            h_real, h_imag = xi_h(n)
            h_real_boxes[str(n)] = ball_record(h_real)
            h_imag_boxes[str(n)] = ball_record(h_imag)
            kp = sum((kernel(n, j) * coeff[M + j] for j in range(-M, M + 1)), arb(0))
            km = sum((kernel(-n, j) * coeff[M + j] for j in range(-M, M + 1)), arb(0))
            pair_defect = abs(kp - km)
            mode_pair_defect_upper = interval_max(mode_pair_defect_upper, pair_defect)
            for kval in (abs(kp), abs(km)):
                max_kpsi_upper = interval_max(max_kpsi_upper, kval)
            pair_term = ((-1) ** n) * h_real * (kp + km) / sqrtL
            F96 += pair_term
            if n <= 64:
                F64 += pair_term

        out["finite_sum"] = {
            "dps": DPS,
            "same_L": "log(16)",
            "same_prime_powers": [int(k) for k, _p in prime_powers],
            "terms": "explicit positive and negative n modes; H(-t)=H(t) and xi critical-line realness checked by Acb imaginary boxes containing zero",
            "F64": ball_record(F64),
            "F96": ball_record(F96),
            "max_abs_kpsi_interval_upper": str(max_kpsi_upper.upper()),
            "max_plus_minus_kpsi_interval_defect_upper": str(mode_pair_defect_upper.upper()),
            "H_sampled_real_intervals": {"n17": h_real_boxes["17"], "n96": h_real_boxes["96"]},
            "H_sampled_imaginary_intervals_contain_zero": all(0 in arb(v["ball"]) for v in h_imag_boxes.values()),
            "H_sampled_imaginary_intervals": {"n17": h_imag_boxes["17"], "n96": h_imag_boxes["96"]},
        }

        # Candidate tail estimate transcribed from the root note. The final
        # Arb evaluation checks this fixed expression, not its analytic proof.
        tail = arb(6553600) * arb(97) ** 3 * (-arb(679) / 6).exp()
        tail_lt_claimed = tail < arb("4.258e-37")
        F_infty_lower = (F96 - tail).lower()
        F_infty_upper = (F96 + tail).upper()
        overlap = arb(direct["input"]["physical_overlap_h_v"]["ball"])
        lam = arb(eigen["eigensolver"]["selected_eigenvalue_i1"]["ball"])
        lambda_overlap = lam * overlap
        if not (0 < lambda_overlap):
            raise ArithmeticError("lambda*physical overlap interval is not positive")
        tail_ratio_upper = (tail / lambda_overlap.lower()).upper()
        x_identity = -lambda_overlap - F96
        x_identity_lower = (x_identity - tail).lower()
        x_identity_upper = (x_identity + tail).upper()

        out["candidate_analytic_tail_bound"] = {
            "independent_math_review": "PENDING",
            "assumptions_and_bounds_from_note": [
                "|H(t)| <= 100(|t|+1)^3 exp(-pi|t|/6)",
                "t_n=2*pi*n/log(16)<3n and pi^2/(3log(16))>7/6, hence |H(t_n)|<=6400*n^3*exp(-7n/6)",
                "for unit carrier vectors and |n|>=97, |k(psi_n,v)|<256 and 1/sqrt(log(16))<1",
                "both signed tails give |F-F96|<=3276800*sum_{n>=97} n^3*exp(-7n/6)",
                "geometric ratio after n=97 is <1/2, hence <=6553600*97^3*exp(-679/6)",
            ],
            "arb_upper_expression": ball_record(tail),
            "arb_upper_bound_below_4_258e_minus_37": bool(tail_lt_claimed),
            "F_infinity_candidate_interval": {
                "lower": str(F_infty_lower),
                "upper": str(F_infty_upper),
                "status": "conditional on independent review accepting the analytic note",
            },
            "tail_over_abs_lambda_overlap_upper": str(tail_ratio_upper),
        }
        out["source_denominator"] = {
            "lambda_interval": ball_record(lam),
            "physical_overlap_h_v_interval_from_direct_x_json": ball_record(overlap),
            "lambda_times_overlap_interval": ball_record(lambda_overlap),
        }
        out["conditional_X_identity_only"] = {
            "formula": "X_identity = -lambda*<h,v> - F_infinity, from exact NOESCAPE closure only",
            "interval": {"lower": str(x_identity_lower), "upper": str(x_identity_upper)},
            "status": "ALGEBRAIC_CONSEQUENCE_ONLY_NOT_INDEPENDENT_X_EVALUATION_OR_IDENTITY_CHECK",
            "direct_x_fast_midpoint_for_context_only": fast["results"][-1]["X_signed"],
        }
        out["source_control"] = {
            "prior_diagnostic": "noescape_m16_fourier.json; 1056 off-diagonal entries against full_center_probe.matrix_K(16)",
            "prior_control_max_abs_difference": prior["in_window_offdiagonal_source_control"]["max_abs_difference"],
            "current_high_modes": "computed entrywise from the existing builder's closed alpha/w02/prime formula; no enlarged matrix/eigensolve",
            "source_control_is_diagnostic": True,
        }
        out["status"] = "FINITE_M16_F96_ARB_ENCLOSURE_WITH_REVIEW_PENDING_TAIL"
        out["remaining_error_map"] = [
            "The finite F96 interval propagates the stored eigenvector coordinate balls through interval normalization, alpha/kernel rows, and Acb gamma*zeta; it does not certify the candidate tail proof in the root note.",
            "The |n|>96 bound is recorded conditionally and awaits independent mathematical review; without acceptance, only F96 is interval-certified.",
            "No independently evaluated X interval or independent F+X+lambda overlap closure check was produced. The optional X_identity interval is only the NOESCAPE identity solved for X.",
            "Direct-X quadrature/tail errors remain as recorded in noescape_m16_direct_x_fast.json and noescape_m16_direct_x.json.",
            "A single m=16 cell and this finite source split do not establish the cofinal NOESCAPE target.",
        ]
    finally:
        out["runtime_seconds"] = round(time.monotonic() - started, 3)
        OUTPUT.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == "__main__":
    main()
