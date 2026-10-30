#!/usr/bin/env python3
"""Finite physical h-overlap of literal even CCM bottoms; diagnostic only.

For m=8,16,24,32 this uses full_center_probe.matrix_K(m), compressed by
parity_gap_table.parity_bases(m).E, and the lowest eigenvector of that even
block.  The physical window coefficient of h is evaluated as its whole-line
Fourier coefficient (-1)^n H(2*pi*n/L)/sqrt(L) minus the directly integrated
theta tail outside [-L/2,L/2].  All arithmetic is mpmath floating point;
this is not a numerical certificate or a cofinal claim.
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

import mpmath as mp

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
FOKAS = ROOT / "docs/routeB_bus/fokas_k_sign_2026-09-25"
sys.path.insert(0, str(FOKAS))

import full_center_probe as full_probe  # noqa: E402
from parity_gap_table import parity_bases  # noqa: E402

OUTPUT = HERE / "noescape_ground_overlap_probe.json"
MS = (8, 16, 24, 32)
BASE_DPS = 160
MAX_DPS_BUMP = 80
CELL_TIME_CAP_SECONDS = 240

_active_stage = "initialization"


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def nstr(value: Any, digits: int = BASE_DPS) -> str:
    return mp.nstr(value, digits, strip_zeros=False)


def h_u(u: mp.mpf) -> mp.mpf:
    """Positive-axis theta h(x), where u=exp(2x), x>=0."""
    total = mp.mpf(0)
    n = 1
    threshold = mp.mpf("2.4") * mp.mp.prec
    while True:
        a = mp.pi * n * n
        au = a * u
        if au > threshold:
            break
        total += (16 * mp.pi**2 * n**4 * u**2 - 24 * mp.pi * n**2 * u) * mp.exp(-au)
        n += 1
    return u ** mp.mpf("0.25") * total


def h_x(x: mp.mpf) -> mp.mpf:
    return h_u(mp.exp(2 * x))


def positive_half_integral(power: int = 1) -> mp.mpf:
    """Integrate h(x)^power on x>=0 using u=exp(2x), dx=du/(2u)."""
    def integrand(u: mp.mpf) -> mp.mpf:
        return h_u(u) ** power / (2 * u)

    # Segment the rapidly decaying tail so the quadrature sees the mass near 1.
    return mp.quad(integrand, [mp.mpf(1), 2, 4, 8, 16, mp.inf])


def four_xi(t: mp.mpf) -> mp.mpf:
    s = mp.mpf("0.5") - 1j * t
    xi = s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)
    return 4 * xi


def theta_tail_cos(b: mp.mpf, t: mp.mpf) -> mp.mpf:
    """Integral_b^infinity h(x) cos(t*x) dx via u=exp(2x)."""
    lower = mp.exp(2 * b)

    def integrand(u: mp.mpf) -> mp.mpf:
        x = mp.log(u) / 2
        return h_u(u) * mp.cos(t * x) / (2 * u)

    return mp.quad(integrand, [lower, lower + 1, lower + 4, lower + 12, mp.inf])


def normalized_residual(A: mp.matrix, vec: mp.matrix, lam: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    residual = A * vec - lam * vec
    abs_resid = mp.norm(residual)
    scale = max(mp.mpf(1), mp.norm(A) * mp.norm(vec), abs(lam) * mp.norm(vec))
    return abs_resid, abs_resid / scale


def run_cell(m: int, dps: int, norm_h_sq: mp.mpf) -> dict[str, Any]:
    global _active_stage
    mp.mp.dps = dps
    _active_stage = "construct full literal matrix_K"
    started = time.perf_counter()
    L = mp.log(m)

    # Do not replace or truncate this source: matrix_K contains all terms,
    # including prime powers <=m, both pole functionals, and the full diagonal.
    K = full_probe.matrix_K(m)
    _active_stage = "compress by registered even basis E"
    E, _O = parity_bases(m)
    A = E.T * K * E

    _active_stage = "diagonalize full even block"
    values, vectors = mp.eigsy(A)
    lam0, lam1 = values[0], values[1]
    w0 = vectors[:, 0]
    gap = lam1 - lam0
    residual, rel_residual = normalized_residual(A, w0, lam0)
    res_gap = residual / abs(gap) if gap else mp.inf

    # Whole-line transform coefficients, then an explicit physical-tail
    # subtraction. For even h, the two exterior tails combine into cos(t*x).
    _active_stage = "evaluate whole-line xi coefficients and physical tails"
    b = L / 2
    whole_coeffs: list[mp.mpf] = []
    interval_coeffs: list[mp.mpf] = []
    tail_coeffs: list[mp.mpf] = []
    max_h_imag = mp.mpf(0)
    for n in range(m + 1):
        t = 2 * mp.pi * n / L
        H = four_xi(t)
        max_h_imag = max(max_h_imag, abs(mp.im(H)))
        phase = -1 if n % 2 else 1
        whole = phase * mp.re(H) / mp.sqrt(L)
        tail = 2 * phase * theta_tail_cos(b, t) / mp.sqrt(L)
        whole_coeffs.append(whole)
        tail_coeffs.append(tail)
        interval_coeffs.append(whole - tail)

    # E has columns e_0 and (e_n+e_-n)/sqrt(2).  Thus this is the exact
    # coefficient pairing of the even eigenfunction with h restricted to I_m.
    overlap = w0[0] * interval_coeffs[0]
    for n in range(1, m + 1):
        overlap += mp.sqrt(2) * w0[n] * interval_coeffs[n]

    overlap_whole = w0[0] * whole_coeffs[0]
    for n in range(1, m + 1):
        overlap_whole += mp.sqrt(2) * w0[n] * whole_coeffs[n]
    overlap_tail = overlap_whole - overlap

    fraction = abs(overlap) ** 2 / norm_h_sq
    amp_fraction = abs(overlap) / mp.sqrt(norm_h_sq)
    elapsed = time.perf_counter() - started
    _active_stage = "cell complete"
    return {
        "m": m,
        "dimension_even": m + 1,
        "precision_dps": dps,
        "lambda_bottom": nstr(lam0),
        "lambda_first_excited": nstr(lam1),
        "first_even_gap": nstr(gap),
        "bottom_vector_norm_squared": nstr(mp.fdot(w0, w0)),
        "bottom_eigen_residual_l2": nstr(residual),
        "bottom_eigen_residual_relative_to_max_1_operator_scale": nstr(rel_residual),
        "residual_over_first_gap": nstr(res_gap),
        "physical_overlap_h_bottom_signed": nstr(overlap),
        "physical_overlap_h_bottom_abs": nstr(abs(overlap)),
        "normalized_squared_physical_h_overlap": nstr(fraction),
        "normalized_physical_h_overlap_abs": nstr(amp_fraction),
        "whole_line_overlap_before_tail_correction": nstr(overlap_whole),
        "signed_exterior_tail_correction_to_overlap": nstr(overlap_tail),
        "max_abs_mode_tail_coefficient": nstr(max(abs(v) for v in tail_coeffs)),
        "max_abs_whole_line_h_coefficient": nstr(max(abs(v) for v in whole_coeffs)),
        "max_abs_imaginary_part_of_H": nstr(max_h_imag),
        "source": {
            "matrix": "full_center_probe.matrix_K(m), unchanged full literal source",
            "even_basis": "parity_gap_table.parity_bases(m).E",
            "whole_line_h_coefficient": "(-1)^n * H(2*pi*n/L) / sqrt(L), H(t)=4*xi(1/2-i*t)",
            "physical_window_coefficient": "whole-line coefficient minus 2*(-1)^n/sqrt(L)*integral_(L/2)^infinity h(x)cos(2*pi*n*x/L)dx",
            "tail_method": "direct mpmath quadrature of the explicit positive-axis theta series, u=exp(2x)",
        },
        "numerical_method": {
            "eigensolver": "mpmath.eigsy on E.T * matrix_K(m) * E",
            "bottom_index_zero_based": 0,
            "theta_series_cutoff": "first omitted n satisfies pi*n^2*u > 2.4*mp.mp.prec bits",
            "quadrature": "mpmath adaptive quadrature; no interval enclosure",
        },
        "runtime_seconds": round(elapsed, 6),
    }


def write_payload(payload: dict[str, Any]) -> None:
    OUTPUT.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def on_alarm(_signum: int, _frame: Any) -> None:
    raise TimeoutError(f"per-cell time cap at stage: {_active_stage}")


def main() -> int:
    global _active_stage
    started = time.perf_counter()
    mp.mp.dps = BASE_DPS
    _active_stage = "direct positive-axis theta norm"
    norm_half = positive_half_integral(2)
    norm_h_sq = 2 * norm_half
    int_h_half = positive_half_integral(1)
    H0 = mp.re(four_xi(mp.mpf(0)))
    whole_integral_h = 2 * int_h_half
    norm_control = whole_integral_h - H0

    sources = {
        "this_script": Path(__file__).resolve(),
        "full_center_probe.py": FOKAS / "full_center_probe.py",
        "parity_gap_table.py": HERE / "parity_gap_table.py",
        "rectangle_probe.py": FOKAS / "rectangle_probe.py",
        "noescape_verdict_theta_tail_source.md": ROOT / "docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md",
    }
    payload: dict[str, Any] = {
        "status": "RUNNING",
        "diagnostic_class": "FINITE_FLOATING_POINT_DIAGNOSTIC_NEVER_A_CERTIFICATE",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "literal even bottom of full CCM matrix for m=8,16,24,32; no excited-mode substitution; no cofinal claim",
        "precision_initial_dps": BASE_DPS,
        "precision_bump_once_if_needed_dps": MAX_DPS_BUMP,
        "per_cell_time_cap_seconds": CELL_TIME_CAP_SECONDS,
        "h_norm": {
            "definition": "2*integral_0^infinity h(x)^2 dx, explicit positive-axis theta series",
            "squared_norm_mpmath": nstr(norm_h_sq),
            "norm_mpmath": nstr(mp.sqrt(norm_h_sq)),
            "integral_h_whole_line_mpmath": nstr(whole_integral_h),
            "H_zero_4xi_half_mpmath": nstr(H0),
            "integral_h_minus_H0_control": nstr(norm_control),
            "quadrature_is_rigorous": False,
        },
        "cells": [],
        "source_sha256": {name: file_sha256(path) for name, path in sources.items()},
        "limitations": [
            "Every result is an mpmath approximation; matrix quadrature, eigensolver, xi evaluations, theta quadrature, and norm integration have no rigorous error enclosure.",
            "The exterior correction is directly integrated from the defining theta series; it is not dropped or inferred from a periodized coefficient.",
            "The even gap and residual are numerical diagnostics only and do not certify a simple exact bottom eigenvalue.",
            "Finite m=8,16,24,32 cells do not imply any cofinal statement or NOESCAPE conclusion.",
            "No RH claim is made.",
        ],
    }
    write_payload(payload)

    signal.signal(signal.SIGALRM, on_alarm)
    completed = True
    for m in MS:
        mp.mp.dps = BASE_DPS
        cell_started = time.perf_counter()
        deadline = cell_started + CELL_TIME_CAP_SECONDS
        try:
            signal.setitimer(signal.ITIMER_REAL, max(0.01, deadline - time.perf_counter()))
            cell = run_cell(m, BASE_DPS, norm_h_sq)
            if mp.mpf(cell["residual_over_first_gap"]) > mp.mpf("1e-40"):
                signal.setitimer(signal.ITIMER_REAL, 0)
                # One precision increase only, and only when the eigensolver
                # residual is not negligible relative to the first gap.
                remaining = deadline - time.perf_counter()
                if remaining <= 0:
                    raise TimeoutError("per-cell time cap before the one permitted precision bump")
                mp.mp.dps = BASE_DPS + MAX_DPS_BUMP
                norm_half_bumped = positive_half_integral(2)
                norm_h_sq = 2 * norm_half_bumped
                remaining = deadline - time.perf_counter()
                if remaining <= 0:
                    raise TimeoutError("per-cell time cap during norm recomputation for precision bump")
                signal.setitimer(signal.ITIMER_REAL, remaining)
                cell = run_cell(m, BASE_DPS + MAX_DPS_BUMP, norm_h_sq)
                cell["precision_bump_reason"] = "base-precision residual/gap exceeded 1e-40"
            else:
                cell["precision_bump_reason"] = None
            signal.setitimer(signal.ITIMER_REAL, 0)
            payload["cells"].append(cell)
            write_payload(payload)
        except TimeoutError as exc:
            signal.setitimer(signal.ITIMER_REAL, 0)
            payload["cells"].append({
                "m": m,
                "status": "INCOMPLETE_PER_CELL_TIMEOUT",
                "last_stage": str(exc),
                "runtime_seconds": round(time.perf_counter() - started, 6),
            })
            completed = False
            write_payload(payload)
            break
        except Exception as exc:
            signal.setitimer(signal.ITIMER_REAL, 0)
            payload["cells"].append({
                "m": m,
                "status": "INCOMPLETE_ERROR",
                "last_stage": _active_stage,
                "error": f"{type(exc).__name__}: {exc}",
                "runtime_seconds": round(time.perf_counter() - started, 6),
            })
            completed = False
            write_payload(payload)
            break

    payload["status"] = "COMPLETE_FINITE_DIAGNOSTIC_NOT_A_CERTIFICATE" if completed else "PARTIAL_FINITE_DIAGNOSTIC_NOT_A_CERTIFICATE"
    payload["runtime_seconds_total"] = round(time.perf_counter() - started, 6)
    payload["runtime_environment"] = {
        "python": platform.python_version(),
        "mpmath": mp.__version__,
        "platform": platform.platform(),
    }
    payload["source_sha256"]["this_script"] = file_sha256(Path(__file__).resolve())
    write_payload(payload)
    print(json.dumps(payload, indent=2, ensure_ascii=False), flush=True)
    return 0 if completed else 1


if __name__ == "__main__":
    raise SystemExit(main())
