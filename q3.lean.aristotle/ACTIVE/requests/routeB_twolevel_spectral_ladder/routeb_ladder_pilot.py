#!/usr/bin/env python3
"""
Route B TwoLevelSpectralLadder pilot.

This file is intentionally self-contained inside the active request directory.
It is numerical evidence only: no RH claim, no proof integration.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[4]
REQUEST_DIR = Path(__file__).resolve().parent
OUT_DIR = REQUEST_DIR / "out"
REPORT = REQUEST_DIR / "report.md"
NU_COMPLEMENT_AUDIT = REQUEST_DIR / "nu_complement_audit.md"
ROGUE_TAIL_AUDIT = REQUEST_DIR / "rogue_tail_audit.md"


FAILURE_CODES = {
    "DEFINITIONS_NOT_FOUND",
    "MATRIX_CONVENTION_MISMATCH",
    "PRECISION_UNSTABLE",
    "N_LIMIT_NOT_STABLE",
    "FIRST_LEVEL_EXPONENT_MISMATCH",
    "ODD_BRANCH_NOT_ADMISSIBLE",
    "SECOND_LEVEL_NOT_PROLATE",
    "ROGUE_STATE_BELOW_LADDER",
    "TAIL_GAP_ASSUMPTION_FAILS",
    "GAP_COLLAPSE_E2CLASS",
    "ETA_VS_LEAKAGE_MISMATCH",
    "NORMALIZATION_B_LAMBDA_MISSING",
    "NUMERICAL_CONDITIONING_INVALID",
    "W_NOT_DECAYING",
}


def require_deps():
    missing = []
    for name in ("mpmath", "numpy", "scipy"):
        try:
            __import__(name)
        except Exception:
            missing.append(name)
    if missing:
        write_report(
            failure_code="PRECISION_UNSTABLE",
            definitions_log="Dependency check failed before calibration.",
            calibration={"dependency_missing": missing},
            ladder=[],
            fits={},
            notes=[
                "Required numerical dependencies are missing: " + ", ".join(missing),
                "Run with: uv run --no-project --with mpmath --with scipy --with numpy python routeb_ladder_pilot.py",
            ],
        )
        raise SystemExit(2)


require_deps()

import mpmath as mp
import numpy as np
from scipy import special


def mp_to_str(x: Any, digits: int = 50) -> str:
    if isinstance(x, str):
        return x
    try:
        return mp.nstr(x, digits)
    except Exception:
        return str(x)


def json_safe(x: Any) -> Any:
    if isinstance(x, dict):
        return {str(k): json_safe(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [json_safe(v) for v in x]
    if isinstance(x, (np.floating, np.integer)):
        return x.item()
    if isinstance(x, np.ndarray):
        return json_safe(x.tolist())
    if isinstance(x, (mp.mpf, mp.mpc)):
        return mp_to_str(x, 80)
    return x


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(payload), indent=2, sort_keys=True) + "\n")


def append_log(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(text.rstrip() + "\n")


def dps_for_lam(lam: mp.mpf) -> int:
    return int(120 + mp.ceil(4 * mp.pi * lam * lam / mp.log(10)))


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    r = int(math.isqrt(n))
    for d in range(3, r + 1, 2):
        if n % d == 0:
            return False
    return True


def von_mangoldt(k: int) -> mp.mpf:
    for p in range(2, k + 1):
        if not is_prime(p):
            continue
        t = p
        while t < k:
            t *= p
        if t == k:
            return mp.log(p)
    return mp.mpf("0")


def prime_powers_up_to(x: mp.mpf) -> List[Tuple[int, mp.mpf]]:
    limit = int(mp.floor(x + mp.mpf("1e-40")))
    out = []
    for k in range(2, limit + 1):
        lam = von_mangoldt(k)
        if lam != 0:
            out.append((k, lam))
    return out


def q_nm(n: int, m: int, y: mp.mpf, L: mp.mpf) -> mp.mpf:
    if n == m:
        return 2 * (1 - y / L) * mp.cos(2 * mp.pi * n * y / L)
    return (
        mp.sin(2 * mp.pi * m * y / L) - mp.sin(2 * mp.pi * n * y / L)
    ) / (mp.pi * (n - m))


def w02(n: int, m: int, L: mp.mpf) -> mp.mpf:
    return (
        32
        * L
        * mp.sinh(L / 4) ** 2
        * (L**2 - 16 * mp.pi**2 * m * n)
        / ((L**2 + 16 * mp.pi**2 * m**2) * (L**2 + 16 * mp.pi**2 * n**2))
    )


def wp(n: int, m: int, L: mp.mpf, perturb_k: Optional[int] = None, perturb: mp.mpf = mp.mpf("0")) -> mp.mpf:
    total = mp.mpf("0")
    for k, mangoldt in prime_powers_up_to(mp.e**L):
        coeff = mangoldt * k ** mp.mpf("-0.5")
        if perturb_k is not None and k == perturb_k:
            coeff += perturb
        total += coeff * q_nm(n, m, mp.log(k), L)
    return total


def rho(x: mp.mpf) -> mp.mpf:
    return mp.e ** (x / 2) / (mp.e**x - mp.e ** (-x))


def alpha_closed(n: int, L: mp.mpf) -> mp.mpf:
    if n == 0:
        return mp.mpf("0")
    z = mp.e ** (-2 * L)
    a = mp.mpc(mp.mpf("0.25"), mp.pi * n / L)
    term = (2 * L / (L + 4 * mp.pi * 1j * n)) * mp.hyp2f1(1, a, a + 1, z)
    return (mp.e ** (-L / 2) * mp.im(term) + mp.mpf("0.5") * mp.im(mp.digamma(a))) / mp.pi


def beta_closed(n: int, L: mp.mpf) -> mp.mpf:
    z = mp.e ** (-2 * L)
    a = mp.mpc(mp.mpf("0.25"), mp.pi * n / L)
    if n == 0:
        f = lambda x: x * rho(x)
        return mp.quad(f, [0, L]) / L
    hyp = mp.hyp2f1(1, a, a + 1, z)
    term1 = -L * mp.e ** (-L / 2) * mp.im((2 * L / (4 * mp.pi * n - 1j * L)) * hyp)
    term2 = -mp.e ** (-L / 2) * mp.re(lerchphi_z_s2_series(z, a)) / 4
    term3 = mp.re(mp.polygamma(1, a)) / 4
    return (term1 + term2 + term3) / L


def lerchphi_z_s2_series(z: mp.mpf, a: mp.mpc) -> mp.mpc:
    """Fast Phi(z, 2, a) for |z| < 1."""
    total = mp.mpc(0)
    zk = mp.mpf(1)
    k = 0
    tol = mp.power(10, -(mp.mp.dps + 20))
    while True:
        term = zk / (a + k) ** 2
        total += term
        if abs(term) < tol:
            return total
        k += 1
        zk *= z
        if k > 100000:
            raise RuntimeError("lerchphi_z_s2_series did not converge")


def cos_minus_one_integral_closed(n: int, L: mp.mpf) -> mp.mpf:
    if n == 0:
        return mp.mpf("0")
    z = mp.e ** (-2 * L)
    a = mp.mpc(mp.mpf("0.25"), mp.pi * n / L)
    hyp = mp.hyp2f1(1, a, a + 1, z)
    h0 = mp.hyp2f1(mp.mpf("0.25"), 1, mp.mpf("1.25"), z)
    term1 = -mp.e ** (-L / 2) * mp.re((2 * L / (L + 4 * mp.pi * 1j * n)) * hyp)
    term2 = 2 * mp.e ** (-L / 2) * h0
    term3 = -mp.mpf("0.5") * (mp.re(mp.digamma(a)) - mp.digamma(mp.mpf("0.25")))
    return term1 + term2 + term3


def exp_correction_integral(L: mp.mpf) -> mp.mpf:
    # Integral of (1 - exp(-x/2))*rho(x), with the removable singularity at x=0.
    f = lambda x: (1 - mp.e ** (-x / 2)) * rho(x)
    return mp.quad(f, [0, L])


def gamma_closed(n: int, L: mp.mpf, exp_corr_cache: Optional[mp.mpf] = None) -> mp.mpf:
    exp_corr = exp_corr_cache if exp_corr_cache is not None else exp_correction_integral(L)
    const = mp.mpf("0.5") * (mp.euler + mp.log(4 * mp.pi * (mp.e**L - 1) / (mp.e**L + 1)))
    return cos_minus_one_integral_closed(n, L) + exp_corr + const


def wr_closed(n: int, m: int, L: mp.mpf, exp_corr_cache: Optional[mp.mpf] = None) -> mp.mpf:
    if n == m:
        return 2 * gamma_closed(n, L, exp_corr_cache) - 2 * beta_closed(n, L)
    return (alpha_closed(m, L) - alpha_closed(n, L)) / (n - m)


def wr_direct(n: int, m: int, L: mp.mpf) -> mp.mpf:
    omega0 = q_nm(n, m, mp.mpf("0"), L)
    const = omega0 * mp.mpf("0.5") * (mp.euler + mp.log(4 * mp.pi * (mp.e**L - 1) / (mp.e**L + 1)))

    def integrand(x: mp.mpf) -> mp.mpf:
        if abs(x) < mp.mpf("1e-40"):
            # Let mp.quad avoid the removable endpoint singularity.
            return mp.mpf("0")
        return (mp.e ** (x / 2) * q_nm(n, m, x, L) - omega0) / (mp.e**x - mp.e ** (-x))

    pieces = [0, L / 8, L / 4, 3 * L / 8, L / 2, 5 * L / 8, 3 * L / 4, 7 * L / 8, L]
    return const + mp.quad(integrand, pieces)


def tau_closed(n: int, m: int, L: mp.mpf, perturb_k: Optional[int] = None, perturb: mp.mpf = mp.mpf("0")) -> mp.mpf:
    exp_corr = exp_correction_integral(L)
    return w02(n, m, L) - wr_closed(n, m, L, exp_corr) - wp(n, m, L, perturb_k, perturb)


def tau_direct(n: int, m: int, L: mp.mpf) -> mp.mpf:
    return w02(n, m, L) - wr_direct(n, m, L) - wp(n, m, L)


def rel_error(a: mp.mpf, b: mp.mpf) -> mp.mpf:
    denom = max(mp.mpf("1"), abs(a), abs(b))
    return abs(a - b) / denom


def build_tau_matrix(lam: mp.mpf, N: int, dps: int) -> mp.matrix:
    mp.mp.dps = dps
    L = 2 * mp.log(lam)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"build_tau_matrix start lambda={mp_to_str(lam, 20)} N={N} dps={dps}")
    exp_corr = exp_correction_integral(L)
    alpha_pos = {n: alpha_closed(n, L) for n in range(0, N + 1)}
    beta_pos = {n: beta_closed(n, L) for n in range(0, N + 1)}
    gamma_pos = {n: gamma_closed(n, L, exp_corr) for n in range(0, N + 1)}
    alpha = {n: (alpha_pos[n] if n >= 0 else -alpha_pos[-n]) for n in range(-N, N + 1)}
    beta = {n: beta_pos[abs(n)] for n in range(-N, N + 1)}
    gamma = {n: gamma_pos[abs(n)] for n in range(-N, N + 1)}
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"build_tau_matrix coefficients ready lambda={mp_to_str(lam, 20)} N={N}")
    pps = prime_powers_up_to(mp.e**L)
    size = 2 * N + 1
    T = mp.matrix(size)
    for ii, n in enumerate(range(-N, N + 1)):
        for jj, m in enumerate(range(-N, N + 1)):
            if n == m:
                wr = 2 * gamma[n] - 2 * beta[n]
            else:
                wr = (alpha[m] - alpha[n]) / (n - m)
            prime = mp.mpf("0")
            for k, mangoldt in pps:
                prime += mangoldt * k ** mp.mpf("-0.5") * q_nm(n, m, mp.log(k), L)
            T[ii, jj] = w02(n, m, L) - wr - prime
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"build_tau_matrix done lambda={mp_to_str(lam, 20)} N={N}")
    return T


def eigsy_sorted(T: mp.matrix) -> Tuple[List[mp.mpf], mp.matrix]:
    vals, vecs = mp.eigsy(T)
    return [vals[i] for i in range(vals.rows)], vecs


def matrix_parity_check(lam: mp.mpf, N: int, dps: int) -> Dict[str, Any]:
    mp.mp.dps = dps
    L = 2 * mp.log(lam)
    pairs = [(0, 0), (1, 2), (2, -1), (3, 3), (-2, 4)]
    errors = []
    for n, m in pairs:
        a = tau_closed(n, m, L)
        b = tau_closed(-n, -m, L)
        errors.append({"n": n, "m": m, "error": rel_error(a, b), "tau": a, "tau_reflected": b})
    return {"max_error": max(e["error"] for e in errors), "pairs": errors}


def run_calibration() -> Tuple[Optional[str], Dict[str, Any]]:
    started = time.time()
    lam = mp.mpf("1.5")
    N = 20
    dps = dps_for_lam(lam)
    mp.mp.dps = dps
    L = 2 * mp.log(lam)
    out: Dict[str, Any] = {"lambda": lam, "N": N, "dps": dps, "checks": {}}

    c1_pairs = []
    for n, m in [(0, 0), (1, 2)]:
        closed = tau_closed(n, m, L)
        direct = tau_direct(n, m, L)
        err = rel_error(closed, direct)
        c1_pairs.append({"n": n, "m": m, "closed": closed, "direct": direct, "rel_error": err})
    out["checks"]["C1"] = {"pairs": c1_pairs, "threshold": "1e-8", "pass": all(p["rel_error"] < mp.mpf("1e-8") for p in c1_pairs)}
    if not out["checks"]["C1"]["pass"]:
        out["elapsed_s"] = time.time() - started
        return "MATRIX_CONVENTION_MISMATCH", out

    c2 = matrix_parity_check(lam, N, dps)
    c2["threshold"] = "1e-40"
    c2["pass"] = c2["max_error"] < mp.mpf("1e-40")
    out["checks"]["C2"] = c2
    if not c2["pass"]:
        out["elapsed_s"] = time.time() - started
        return "MATRIX_CONVENTION_MISMATCH", out

    planted = []
    for n, m in [(0, 0), (1, 2)]:
        closed_bad = tau_closed(n, m, L, perturb_k=2, perturb=mp.mpf("1e-3"))
        direct = tau_direct(n, m, L)
        err = rel_error(closed_bad, direct)
        planted.append({"n": n, "m": m, "planted_rel_error": err})
    c3_pass = any(p["planted_rel_error"] > mp.mpf("1e-8") for p in planted)
    out["checks"]["C3"] = {"pairs": planted, "pass": c3_pass}
    if not c3_pass:
        out["elapsed_s"] = time.time() - started
        return "MATRIX_CONVENTION_MISMATCH", out

    T1 = build_tau_matrix(lam, N, dps)
    vals1, _ = eigsy_sorted(T1)
    dps2 = dps + 80
    T2 = build_tau_matrix(lam, N, dps2)
    vals2, _ = eigsy_sorted(T2)
    mu1a = vals1[0]
    mu1b = vals2[0]
    prec_err = rel_error(mu1a, mu1b)
    out["checks"]["C4"] = {
        "lambda": lam,
        "N": N,
        "dps": dps,
        "dps_plus_80": dps2,
        "mu1_dps": mu1a,
        "mu1_dps_plus_80": mu1b,
        "rel_error": prec_err,
        "threshold": "1e-30",
        "pass": prec_err < mp.mpf("1e-30"),
    }
    out["elapsed_s"] = time.time() - started
    if not out["checks"]["C4"]["pass"]:
        return "PRECISION_UNSTABLE", out
    return None, out


@dataclass
class ProlatePacket:
    coeffs: Dict[str, np.ndarray]
    raw_norms: Dict[str, float]
    b_norm: float
    chi4: float
    validation: Dict[str, Any]


def legendre_x2_matrix(degrees: Sequence[int]) -> np.ndarray:
    idx = {k: i for i, k in enumerate(degrees)}
    M = np.zeros((len(degrees), len(degrees)), dtype=float)
    for l in degrees:
        # x P_l = a_l P_{l+1} + b_l P_{l-1}
        a = (l + 1) / (2 * l + 1)
        b = l / (2 * l + 1) if l > 0 else 0.0
        terms = []
        # x^2 P_l
        lp = l + 1
        terms.append((lp + 1, a * (lp + 1) / (2 * lp + 1)))
        terms.append((lp - 1, a * (lp / (2 * lp + 1))))
        if l > 0:
            lm = l - 1
            terms.append((lm + 1, b * ((lm + 1) / (2 * lm + 1))))
            if lm > 0:
                terms.append((lm - 1, b * (lm / (2 * lm + 1))))
        for k, coef in terms:
            if k in idx:
                # Convert plain Legendre coefficients to orthonormal basis.
                M[idx[k], idx[l]] += coef * math.sqrt((2 * l + 1) / (2 * k + 1))
    return M


def prolate_even_basis(lam_float: float, max_degree: int = 180) -> Tuple[List[int], np.ndarray, np.ndarray]:
    degrees = list(range(0, max_degree + 1, 2))
    c = 2 * math.pi * lam_float * lam_float
    X2 = legendre_x2_matrix(degrees)
    A = np.diag([k * (k + 1) for k in degrees]) + (c * c) * X2
    vals, vecs = np.linalg.eigh((A + A.T) / 2)
    return degrees, vals, vecs


def eval_legendre_combo(t: np.ndarray, degrees: Sequence[int], coeff: np.ndarray, lam_float: float) -> np.ndarray:
    y = np.zeros_like(t, dtype=float)
    for c, k in zip(coeff, degrees):
        # Orthonormal in x: lambda^(-1/2) * sqrt((2k+1)/2) P_k(t).
        y += c * math.sqrt((2 * k + 1) / (2 * lam_float)) * special.eval_legendre(k, t)
    return y


def make_packets(lam_float: float, N: int, quad_order: int = 900) -> ProlatePacket:
    degrees, vals, vecs = prolate_even_basis(lam_float)
    wanted = {0: vecs[:, 0], 2: vecs[:, 1], 4: vecs[:, 2], 6: vecs[:, 3], 8: vecs[:, 4]}
    nodes, weights = np.polynomial.legendre.leggauss(quad_order)

    def h(which: int, x: np.ndarray) -> np.ndarray:
        t = np.asarray(x, dtype=float) / lam_float
        inside = np.abs(t) <= 1 + 1e-14
        out = np.zeros_like(t, dtype=float)
        if np.any(inside):
            out[inside] = eval_legendre_combo(t[inside], degrees, wanted[which], lam_float)
        return out

    integrals = {}
    for which in wanted:
        vals_h = h(which, lam_float * nodes)
        integrals[which] = float(lam_float * np.dot(weights, vals_h))

    # Since h_n are orthonormal, coefficient-space normalization is enough.
    g04_c = np.array([integrals[4], -integrals[0]], dtype=float)
    g04_c = g04_c / np.linalg.norm(g04_c)
    g26_c = np.array([integrals[6], -integrals[2]], dtype=float)
    g26_c = g26_c / np.linalg.norm(g26_c)

    constraints = np.array(
        [
            [integrals[0], integrals[4], integrals[8]],
            [g04_c[0], g04_c[1], 0.0],
        ],
        dtype=float,
    )
    _, _, vh = np.linalg.svd(constraints)
    g048_c = vh[-1, :]
    g048_c = g048_c / np.linalg.norm(g048_c)

    def g_eval(name: str, x: np.ndarray) -> np.ndarray:
        if name == "g04":
            return g04_c[0] * h(0, x) + g04_c[1] * h(4, x)
        if name == "g26":
            return g26_c[0] * h(2, x) + g26_c[1] * h(6, x)
        if name == "g048perp":
            return g048_c[0] * h(0, x) + g048_c[1] * h(4, x) + g048_c[2] * h(8, x)
        raise KeyError(name)

    L = 2 * math.log(lam_float)
    x_nodes = 0.5 * L * (nodes + 1)
    x_weights = 0.5 * L * weights
    u_nodes = np.exp(x_nodes) / lam_float

    def e_values(name: str) -> np.ndarray:
        out = np.zeros_like(u_nodes)
        for i, u in enumerate(u_nodes):
            mmax = int(math.floor(lam_float / u + 1e-12))
            if mmax <= 0:
                continue
            xs = u * np.arange(1, mmax + 1, dtype=float)
            out[i] = math.sqrt(u) * float(np.sum(g_eval(name, xs)))
        return out

    coeffs: Dict[str, np.ndarray] = {}
    raw_norms: Dict[str, float] = {}
    for name in ("g04", "g26", "g048perp"):
        ev = e_values(name)
        raw_norms[name] = float(math.sqrt(max(0.0, np.dot(x_weights, ev * ev))))
        co = []
        for n in range(-N, N + 1):
            phase = np.exp(-2j * math.pi * n * x_nodes / L)
            co.append((1 / math.sqrt(L)) * np.dot(x_weights, ev * phase))
        arr = np.array(co, dtype=np.complex128)
        coeffs[name] = arr / np.linalg.norm(arr)

    b_norm = raw_norms["g04"]
    h4_0 = float(h(4, np.array([0.0]))[0])
    # Fourier at zero in the unitary convention used here is the integral.
    h4_hat0 = integrals[4]
    chi4 = float(h4_hat0 / h4_0) if h4_0 != 0 else float("nan")

    validation = {
        "legendre_max_degree": max(degrees),
        "eigenvalues_even_0_4": [float(vals[i]) for i in range(5)],
        "integrals": integrals,
        "note": "Legendre parity-block eigensolve; scipy pro_ang1 validation is not used for c>10 ladder cells.",
    }
    return ProlatePacket(coeffs=coeffs, raw_norms=raw_norms, b_norm=b_norm, chi4=chi4, validation=validation)


def mp_vec_from_np(arr: np.ndarray) -> mp.matrix:
    v = mp.matrix(len(arr), 1)
    for i, z in enumerate(arr):
        v[i] = mp.mpc(float(np.real(z)), float(np.imag(z)))
    return v


def inner(v: mp.matrix, w: mp.matrix) -> mp.mpc:
    return sum(mp.conj(v[i]) * w[i] for i in range(v.rows))


def mat_vec(T: mp.matrix, v: mp.matrix) -> mp.matrix:
    return T * v


def norm(v: mp.matrix) -> mp.mpf:
    return mp.sqrt(mp.re(inner(v, v)))


def rayleigh(T: mp.matrix, v: mp.matrix) -> mp.mpf:
    return mp.re(inner(v, T * v))


def copy_vec(v: mp.matrix) -> mp.matrix:
    out = mp.matrix(v.rows, 1)
    for i in range(v.rows):
        out[i] = v[i]
    return out


def standard_basis_vec(size: int, i: int) -> mp.matrix:
    v = mp.matrix(size, 1)
    v[i] = mp.mpf(1)
    return v


def subtract_projection_in_place(w: mp.matrix, q: mp.matrix) -> None:
    coeff = inner(q, w)
    for i in range(w.rows):
        w[i] -= coeff * q[i]


def modified_gram_schmidt_mp(
    candidates: Sequence[mp.matrix],
    *,
    locked: Sequence[mp.matrix] = (),
    tol: Optional[mp.mpf] = None,
) -> Tuple[List[mp.matrix], Dict[str, Any]]:
    tol = tol if tol is not None else mp.power(10, -min(80, max(30, mp.mp.dps // 3)))
    basis: List[mp.matrix] = []
    rejected = 0
    accepted_norms: List[mp.mpf] = []
    rejected_norms: List[mp.mpf] = []
    for cand in candidates:
        w = copy_vec(cand)
        # Two passes are cheap here and suppress high-precision GS leakage.
        for _ in range(2):
            for q in locked:
                subtract_projection_in_place(w, q)
            for q in basis:
                subtract_projection_in_place(w, q)
        nrm = norm(w)
        if nrm > tol:
            for i in range(w.rows):
                w[i] /= nrm
            basis.append(w)
            accepted_norms.append(nrm)
        else:
            rejected += 1
            rejected_norms.append(nrm)
    return basis, {
        "accepted": len(basis),
        "rejected": rejected,
        "tol": tol,
        "min_accepted_norm": min(accepted_norms) if accepted_norms else mp.nan,
        "max_rejected_norm": max(rejected_norms) if rejected_norms else mp.mpf("0"),
    }


def max_orthonormality_error(basis: Sequence[mp.matrix]) -> mp.mpf:
    err = mp.mpf("0")
    for i, vi in enumerate(basis):
        for j, vj in enumerate(basis):
            target = mp.mpf(1) if i == j else mp.mpf(0)
            err = max(err, abs(inner(vi, vj) - target))
    return err


def max_cross_orthogonality_error(left: Sequence[mp.matrix], right: Sequence[mp.matrix]) -> mp.mpf:
    err = mp.mpf("0")
    for v in left:
        for w in right:
            err = max(err, abs(inner(v, w)))
    return err


def hermitian_part(A: mp.matrix) -> mp.matrix:
    H = mp.matrix(A.rows, A.cols)
    for i in range(A.rows):
        for j in range(A.cols):
            H[i, j] = (A[i, j] + mp.conj(A[j, i])) / 2
    return H


def hermitian_eigvals_sorted(A: mp.matrix) -> List[mp.mpf]:
    vals, _ = mp.eighe(hermitian_part(A))
    return [mp.re(vals[i]) for i in range(vals.rows)]


def gram_condition_mp(vectors: Sequence[mp.matrix]) -> mp.mpf:
    G = mp.matrix(len(vectors), len(vectors))
    for i, vi in enumerate(vectors):
        for j, vj in enumerate(vectors):
            G[i, j] = inner(vi, vj)
    vals = hermitian_eigvals_sorted(G)
    smallest = min(abs(x) for x in vals)
    if smallest == 0:
        return mp.inf
    return max(abs(x) for x in vals) / smallest


def float64_tail_diagnostic(T: mp.matrix, packet: ProlatePacket, N: int) -> Dict[str, Any]:
    k1_np = packet.coeffs["g04"]
    k2o_np = packet.coeffs["g26"]
    k2e_np = packet.coeffs["g048perp"]
    K = np.column_stack([k1_np, k2o_np, k2e_np])
    Gram = K.conj().T @ K
    gram_cond = float(np.linalg.cond(Gram))
    Q, _ = np.linalg.qr(K)
    T_np = np.array([[float(T[i, j]) for j in range(2 * N + 1)] for i in range(2 * N + 1)], dtype=float)
    GM = Q.conj().T @ T_np @ Q
    lambda_G = np.linalg.eigvalsh((GM + GM.conj().T) / 2)
    R = T_np @ Q - Q @ (Q.conj().T @ T_np @ Q)
    rho_val = float(np.linalg.svd(R, compute_uv=False)[0])
    Pperp = np.eye(2 * N + 1, dtype=np.complex128) - Q @ Q.conj().T
    Tperp = Pperp.conj().T @ T_np @ Pperp
    old_nu = float(np.linalg.eigvalsh((Tperp + Tperp.conj().T) / 2)[0])
    Q_complete, _ = np.linalg.qr(K, mode="complete")
    U_perp = Q_complete[:, K.shape[1] :]
    T_tail = U_perp.conj().T @ T_np @ U_perp
    complement_nu = float(np.linalg.eigvalsh((T_tail + T_tail.conj().T) / 2)[0])
    return {
        "Gram_condition": gram_cond,
        "lambda_G": [float(x) for x in lambda_G],
        "rho": rho_val,
        "nu_float64_projected_full": old_nu,
        "tail_margin_float64_projected_full": float(old_nu - lambda_G[2]),
        "nu_float64_complement_qr": complement_nu,
        "tail_margin_float64_complement_qr": float(complement_nu - lambda_G[2]),
    }


def float64_complement_guess(T: mp.matrix, m_vectors: Sequence[mp.matrix]) -> Optional[float]:
    try:
        K = np.zeros((T.rows, len(m_vectors)), dtype=np.complex128)
        for j, v in enumerate(m_vectors):
            for i in range(T.rows):
                K[i, j] = complex(v[i])
        Q_complete, _ = np.linalg.qr(K, mode="complete")
        U_perp = Q_complete[:, len(m_vectors) :]
        T_np = np.array([[float(T[i, j]) for j in range(T.rows)] for i in range(T.rows)], dtype=float)
        T_tail = U_perp.conj().T @ T_np @ U_perp
        return float(np.linalg.eigvalsh((T_tail + T_tail.conj().T) / 2)[0])
    except Exception:
        return None


def restricted_tail_nu_secular(
    T: mp.matrix,
    constraints: Sequence[mp.matrix],
    approx: Optional[float],
    return_vector: bool = False,
) -> Dict[str, Any]:
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"secular eigsy start size={T.rows} dps={mp.mp.dps}")
    vals, vecs = eigsy_sorted(T)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"secular eigsy done size={T.rows} dps={mp.mp.dps}")
    size = len(vals)
    rank = len(constraints)

    C: List[List[mp.mpc]] = []
    row_norms: List[mp.mpf] = []
    for i in range(size):
        ev = mp.matrix(size, 1)
        for j in range(size):
            ev[j] = vecs[j, i]
        row = [inner(ev, q) for q in constraints]
        C.append(row)
        row_norms.append(sum(abs(z) ** 2 for z in row))
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"secular constraints ready size={T.rows} dps={mp.mp.dps}")

    feasible_tol = mp.power(10, -min(70, max(35, mp.mp.dps // 3)))
    for i, rn in enumerate(row_norms):
        if rn < feasible_tol:
            payload = {
                "method": "secular_restricted_eigenvalue",
                "nu": vals[i],
                "interval_index": i,
                "root_at_unconstrained_eigenvalue": True,
                "row_constraint_norm": rn,
                "unconstrained_lambda": vals[i],
                "eigsy_min": vals[0],
            }
            if return_vector:
                payload["reconstruction"] = {
                    "vector": mp.matrix([[vecs[row, i]] for row in range(size)]),
                    "root_at_unconstrained_eigenvalue": True,
                }
            return payload

    def F_matrix(t: mp.mpf) -> mp.matrix:
        F = mp.matrix(rank, rank)
        for a in range(rank):
            for b in range(rank):
                s = mp.mpc(0)
                for i in range(size):
                    s += mp.conj(C[i][a]) * C[i][b] / (vals[i] - t)
                F[a, b] = s
        return hermitian_part(F)

    def detF(t: mp.mpf) -> mp.mpf:
        return mp.re(mp.det(F_matrix(t)))

    def reconstruct_vector(root: mp.mpf) -> Dict[str, Any]:
        F = F_matrix(root)
        fvals, fvecs = mp.eighe(F)
        alpha_idx = min(range(fvals.rows), key=lambda a: abs(fvals[a]))
        alpha = mp.matrix(rank, 1)
        for a in range(rank):
            alpha[a] = fvecs[a, alpha_idx]
        y: List[mp.mpc] = []
        for i in range(size):
            numerator = mp.mpc(0)
            for a in range(rank):
                numerator += C[i][a] * alpha[a]
            y.append(numerator / (vals[i] - root))
        y_norm = mp.sqrt(sum(abs(z) ** 2 for z in y))
        if y_norm == 0:
            raise RuntimeError("secular reconstruction produced zero vector")
        y = [z / y_norm for z in y]
        x = mp.matrix(size, 1)
        for row in range(size):
            s = mp.mpc(0)
            for i in range(size):
                s += vecs[row, i] * y[i]
            x[row] = s
        x_norm = norm(x)
        for row in range(size):
            x[row] /= x_norm
        return {
            "vector": x,
            "alpha_null_vector": [alpha[a] for a in range(rank)],
            "F_smallest_abs_eigenvalue": fvals[alpha_idx],
        }

    def sign(x: mp.mpf) -> int:
        if x > 0:
            return 1
        if x < 0:
            return -1
        return 0

    interval_order: List[int] = []
    if approx is not None and math.isfinite(approx):
        for j in range(size - 1):
            if float(vals[j]) <= approx <= float(vals[j + 1]):
                interval_order.extend(range(max(0, j - 5), min(size - 1, j + 6)))
                break
        if not interval_order:
            interval_order.extend(range(0, min(size - 1, 20)))
    interval_order.extend(range(0, min(size - 1, 50)))
    seen = set()
    interval_order = [j for j in interval_order if not (j in seen or seen.add(j))]

    last_error: Optional[str] = None
    for j in interval_order:
        gap = vals[j + 1] - vals[j]
        if gap <= 0:
            continue
        max_exp = min(90, max(20, mp.mp.dps // 2))
        for exp in (12, 20, 32, 48, 64, 80, max_exp):
            eps = mp.power(10, -min(exp, max_exp))
            left = vals[j] + gap * eps
            right = vals[j + 1] - gap * eps
            if not (left < right):
                continue
            try:
                f_left = detF(left)
                f_right = detF(right)
            except Exception as e:
                last_error = str(e)
                continue
            s_left = sign(f_left)
            s_right = sign(f_right)
            if s_left == 0:
                root = left
            elif s_right == 0:
                root = right
            elif s_left != s_right:
                lo, hi = left, right
                flo, fhi = f_left, f_right
                for _ in range(min(260, mp.mp.dps + 40)):
                    mid = (lo + hi) / 2
                    fmid = detF(mid)
                    smid = sign(fmid)
                    if smid == 0:
                        lo = hi = mid
                        break
                    if sign(flo) == smid:
                        lo, flo = mid, fmid
                    else:
                        hi, fhi = mid, fmid
                    if abs(hi - lo) <= mp.power(10, -min(90, max(40, mp.mp.dps // 2))) * max(mp.mpf(1), abs(mid)):
                        break
                root = (lo + hi) / 2
            else:
                continue
            payload = {
                "method": "secular_restricted_eigenvalue",
                "nu": root,
                "interval_index": j,
                "interval_left_lambda": vals[j],
                "interval_right_lambda": vals[j + 1],
                "root_at_unconstrained_eigenvalue": False,
                "approx_float64_complement_qr": approx,
                "detF_left": f_left,
                "detF_right": f_right,
                "eigsy_min": vals[0],
            }
            if return_vector:
                payload["reconstruction"] = reconstruct_vector(root)
            return payload

    return {
        "failure_code": "COMPLEMENT_BASIS_CONDITIONING_FAIL",
        "reason": "secular restricted-eigenvalue root was not bracketed",
        "approx_float64_complement_qr": approx,
        "last_error": last_error,
        "first_unconstrained_eigenvalues": vals[:10],
        "first_constraint_row_norms": row_norms[:10],
    }


def complement_tail_diagnostic(T: mp.matrix, m_vectors: Sequence[mp.matrix]) -> Dict[str, Any]:
    size = T.rows
    tol = mp.power(10, -min(80, max(30, mp.mp.dps // 3)))
    q_basis, q_stats = modified_gram_schmidt_mp(m_vectors, tol=tol)
    gram_cond = gram_condition_mp(m_vectors)
    if len(q_basis) != len(m_vectors):
        return {
            "failure_code": "COMPLEMENT_BASIS_CONDITIONING_FAIL",
            "reason": "packet vectors are not independent under high-precision Gram-Schmidt",
            "m_dim": len(m_vectors),
            "q_dim": len(q_basis),
            "gram_condition_mp": gram_cond,
            "q_stats": q_stats,
        }
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"complement q basis ready size={size} dps={mp.mp.dps}")
    expected_dim = size - len(q_basis)
    u_stats = {
        "mode": "implicit_secular_nullspace",
        "accepted": expected_dim,
        "note": "U_perp is represented implicitly as null(Q_M^*) for the secular restricted eigenvalue solve.",
    }

    Tq = [T * q for q in q_basis]
    GM = mp.matrix(len(q_basis), len(q_basis))
    for i, qi in enumerate(q_basis):
        for j, Tqj in enumerate(Tq):
            GM[i, j] = inner(qi, Tqj)
    lambda_G = hermitian_eigvals_sorted(GM)

    approx = float64_complement_guess(T, m_vectors)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"secular root start size={size} dps={mp.mp.dps} approx={approx}")
    secular = restricted_tail_nu_secular(T, q_basis, approx)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"secular root done size={size} dps={mp.mp.dps} failure={secular.get('failure_code')}")
    if secular.get("failure_code"):
        secular.update(
            {
                "m_dim": len(m_vectors),
                "q_dim": len(q_basis),
                "u_perp_dim": expected_dim,
                "expected_u_perp_dim": expected_dim,
                "gram_condition_mp": gram_cond,
                "q_stats": q_stats,
                "u_stats": u_stats,
            }
        )
        return secular
    nu = secular["nu"]
    lambda3_G = lambda_G[2]
    return {
        "method": "mp_complement_basis_secular_tail_block",
        "m_dim": len(m_vectors),
        "q_dim": len(q_basis),
        "u_perp_dim": expected_dim,
        "expected_u_perp_dim": expected_dim,
        "gram_condition_mp": gram_cond,
        "q_orth_error": max_orthonormality_error(q_basis),
        "u_orth_error": "implicit_secular_nullspace",
        "mperp_cross_error": "implicit_secular_nullspace",
        "q_stats": q_stats,
        "u_stats": u_stats,
        "lambda_G": lambda_G,
        "lambda3_G": lambda3_G,
        "nu": nu,
        "tail_margin": nu - lambda3_G,
        "secular": secular,
    }


def run_ladder_cell(lam_sq: int, N: int) -> Dict[str, Any]:
    started = time.time()
    lam = mp.sqrt(lam_sq)
    dps = dps_for_lam(lam)
    mp.mp.dps = dps
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"cell start lambda_sq={lam_sq} N={N} dps={dps}")
    T = build_tau_matrix(lam, N, dps)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"eigsy start lambda_sq={lam_sq} N={N}")
    vals, vecs = eigsy_sorted(T)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"eigsy done lambda_sq={lam_sq} N={N}")
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"packet start lambda_sq={lam_sq} N={N}")
    packet = make_packets(float(mp.sqrt(lam_sq)), N)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"packet done lambda_sq={lam_sq} N={N}")

    k1 = mp_vec_from_np(packet.coeffs["g04"])
    k2o = mp_vec_from_np(packet.coeffs["g26"])
    k2e = mp_vec_from_np(packet.coeffs["g048perp"])

    a1 = rayleigh(T, k1)
    a2o = rayleigh(T, k2o)
    a2e = rayleigh(T, k2e)
    eta1 = norm(T * k1 - a1 * k1)
    eta2o = norm(T * k2o - a2o * k2o)
    eta2e = norm(T * k2e - a2e * k2e)
    mu1, mu2, mu3 = vals[0], vals[1], vals[2]
    Delta = mu2 - mu1

    xi1_np = np.array([float(vecs[i, 0]) for i in range(2 * N + 1)])
    xi2_np = np.array([float(vecs[i, 1]) for i in range(2 * N + 1)])
    def parity(x: np.ndarray) -> float:
        return float(sum(x[i] * x[-i - 1] for i in range(len(x))))

    overlaps = {
        "xi1_k1": float(abs(np.vdot(xi1_np, packet.coeffs["g04"]))),
        "xi2_k2_odd": float(abs(np.vdot(xi2_np, packet.coeffs["g26"]))),
        "xi2_k2_even": float(abs(np.vdot(xi2_np, packet.coeffs["g048perp"]))),
    }

    float_tail = float64_tail_diagnostic(T, packet, N)
    gram_cond = float_tail["Gram_condition"]
    if not np.isfinite(gram_cond) or gram_cond > 1e12:
        return {
            "lambda_sq": lam_sq,
            "N": N,
            "failure_code": "NUMERICAL_CONDITIONING_INVALID",
            "gram_condition": gram_cond,
            "elapsed_s": time.time() - started,
        }
    tail_diag = complement_tail_diagnostic(T, [k1, k2o, k2e])
    if tail_diag.get("failure_code"):
        return {
            "lambda_sq": lam_sq,
            "N": N,
            "failure_code": tail_diag["failure_code"],
            "tail_diagnostic": tail_diag,
            "elapsed_s": time.time() - started,
        }
    lambda_G_mp = tail_diag["lambda_G"]
    lambda_G = [float(x) for x in lambda_G_mp]
    rho_val = float_tail["rho"]
    nu = tail_diag["nu"]

    LB_2D_odd = a2o - a1 - mp.sqrt(eta1**2 + eta2o**2)
    LB_2D_even = a2e - a1 - mp.sqrt(eta1**2 + eta2e**2)
    LB_3D = lambda_G_mp[1] - a1 - mp.mpf(rho_val)
    b = mp.mpf(packet.b_norm)
    W_actual = b * mp.sqrt(lam) * eta1 / Delta if Delta != 0 else mp.nan
    W_bound = b * mp.sqrt(lam) * eta1 / LB_3D if LB_3D != 0 else mp.nan
    leakage_ratio = eta1 / (1 - mp.mpf(packet.chi4)) if packet.chi4 != 1 else mp.nan
    E = mp.e ** (-4 * mp.pi * lam * lam)

    return {
        "lambda_sq": lam_sq,
        "lambda": lam,
        "N": N,
        "dps": dps,
        "a1": a1,
        "a2_odd": a2o,
        "a2_even": a2e,
        "eta1": eta1,
        "eta2_odd": eta2o,
        "eta2_even": eta2e,
        "mu1": mu1,
        "mu2": mu2,
        "mu3": mu3,
        "Delta": Delta,
        "mu1_over_E": mu1 / E,
        "mu2_over_E": mu2 / E,
        "Delta_over_E": Delta / E,
        "parity_xi1": parity(xi1_np),
        "parity_xi2": parity(xi2_np),
        "overlaps": overlaps,
        "raw_norms": packet.raw_norms,
        "b": packet.b_norm,
        "b_sqrt_lambda": packet.b_norm * float(mp.sqrt(lam)),
        "Gram_condition": gram_cond,
        "lambda_G": [float(x) for x in lambda_G],
        "rho": rho_val,
        "nu": nu,
        "tail_margin": nu - lambda_G_mp[2],
        "old_nu_float64_projected_full": float_tail["nu_float64_projected_full"],
        "old_tail_margin_float64_projected_full": float_tail["tail_margin_float64_projected_full"],
        "tail_diagnostic": tail_diag,
        "LB_2D_odd": LB_2D_odd,
        "LB_2D_even": LB_2D_even,
        "LB_3D": LB_3D,
        "W_actual": W_actual,
        "W_bound": W_bound,
        "chi4": packet.chi4,
        "eta1_over_1_minus_chi4": leakage_ratio,
        "prolate_validation": packet.validation,
        "elapsed_s": time.time() - started,
    }


def fit_slope(rows: List[Dict[str, Any]], key: str) -> Dict[str, Any]:
    xs = []
    ys = []
    for r in rows:
        if r.get("N") != 120:
            continue
        try:
            y = abs(float(r[key]))
            x = float(r["lambda"])
        except Exception:
            continue
        if y > 0 and math.isfinite(y):
            xs.append(math.log(x))
            ys.append(math.log(y))
    if len(xs) < 3:
        return {"key": key, "slope": None, "stderr": None, "n": len(xs)}
    X = np.vstack([np.ones(len(xs)), xs]).T
    beta, *_ = np.linalg.lstsq(X, np.array(ys), rcond=None)
    resid = np.array(ys) - X @ beta
    dof = max(1, len(xs) - 2)
    sigma2 = float(np.dot(resid, resid) / dof)
    cov = sigma2 * np.linalg.inv(X.T @ X)
    return {"key": key, "slope": float(beta[1]), "stderr": float(math.sqrt(cov[1, 1])), "n": len(xs)}


def check_n_stabilization(rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    target = [r for r in rows if r.get("lambda_sq") == 14]
    byN = {r["N"]: r for r in target}
    checks = {}
    ok = True
    for key in ("mu1", "mu2", "Delta", "W_actual", "nu"):
        if 90 not in byN or 120 not in byN:
            ok = False
            continue
        a = abs(float(byN[90][key]))
        b = abs(float(byN[120][key]))
        drift = abs(a - b) / max(1e-300, abs(b))
        checks[key] = drift
        if drift >= 0.01:
            ok = False
    return {"lambda_sq": 14, "drift_90_to_120": checks, "pass": ok}


def run_nu_complement_single(lam_sq: int, N: int, dps: int) -> Dict[str, Any]:
    started = time.time()
    lam = mp.sqrt(lam_sq)
    mp.mp.dps = dps
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"nu_complement start lambda_sq={lam_sq} N={N} dps={dps}")
    T = build_tau_matrix(lam, N, dps)
    packet = make_packets(float(mp.sqrt(lam_sq)), N)
    k1 = mp_vec_from_np(packet.coeffs["g04"])
    k2o = mp_vec_from_np(packet.coeffs["g26"])
    k2e = mp_vec_from_np(packet.coeffs["g048perp"])
    old_tail = float64_tail_diagnostic(T, packet, N)
    new_tail = complement_tail_diagnostic(T, [k1, k2o, k2e])
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"nu_complement done lambda_sq={lam_sq} N={N} dps={dps}")
    return {
        "lambda_sq": lam_sq,
        "lambda": lam,
        "N": N,
        "dps": dps,
        "old_float64_projected_full": old_tail,
        "new_complement_tail": new_tail,
        "elapsed_s": time.time() - started,
    }


def classify_nu_complement(base: Dict[str, Any], plus: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
    base_tail = base.get("new_complement_tail", {})
    plus_tail = plus.get("new_complement_tail", {})
    if base_tail.get("failure_code") or plus_tail.get("failure_code"):
        return "COMPLEMENT_BASIS_CONDITIONING_FAIL", {
            "base_failure": base_tail.get("failure_code"),
            "plus_failure": plus_tail.get("failure_code"),
        }

    nu_base = base_tail["nu"]
    nu_plus = plus_tail["nu"]
    margin_base = base_tail["tail_margin"]
    margin_plus = plus_tail["tail_margin"]
    nu_rel = rel_error(nu_base, nu_plus)
    margin_rel = rel_error(margin_base, margin_plus)
    threshold = mp.mpf("1e-30")
    if nu_rel >= threshold or margin_rel >= threshold:
        return "NU_PRECISION_UNSTABLE", {
            "nu_rel_error": nu_rel,
            "tail_margin_rel_error": margin_rel,
            "threshold": threshold,
        }
    if margin_plus >= 0:
        return "NU_FLOOR_FIXED_TAIL_PASS", {
            "nu_rel_error": nu_rel,
            "tail_margin_rel_error": margin_rel,
            "threshold": threshold,
        }
    return "NU_FLOOR_FIXED_TAIL_FAIL", {
        "nu_rel_error": nu_rel,
        "tail_margin_rel_error": margin_rel,
        "threshold": threshold,
    }


def write_nu_complement_audit(payload: Dict[str, Any]) -> None:
    verdict = payload["verdict"]
    base = payload["runs"]["dps"]
    plus = payload["runs"]["dps_plus_80"]

    def row(label: str, run: Dict[str, Any]) -> str:
        old = run["old_float64_projected_full"]
        new = run["new_complement_tail"]
        if new.get("failure_code"):
            return (
                f"| {label} | {run['dps']} | {old.get('nu_float64_projected_full')} | "
                f"{new.get('failure_code')} | NA | NA | NA | {run.get('elapsed_s')} |"
            )
        return (
            f"| {label} | {run['dps']} | {old.get('nu_float64_projected_full')} | "
            f"{mp_to_str(new.get('nu'))} | {mp_to_str(new.get('lambda3_G'))} | "
            f"{mp_to_str(new.get('tail_margin'))} | {new.get('u_perp_dim')} | {run.get('elapsed_s')} |"
        )

    lines = [
        "# Route B TwoLevelSpectralLadder Nu Complement Audit",
        "",
        "Status: A-only instrument repair diagnostic. Not a proof of RH. Not a Route B kill.",
        "Phase 2 was not run. The full ladder was not rerun. QW formulas and packet definitions were not changed.",
        "",
        "## Proshka Route Review",
        "",
        "- Next gate: A.",
        "- `FAILURE_CODE = N_LIMIT_NOT_STABLE`.",
        "- `PRIMARY_DIAGNOSIS = NUMERICAL_FLOOR_IN_NU`.",
        "- `SECONDARY_DIAGNOSIS = BASIS_TRUNCATION_NOT_STABLE_PENDING_PACKET_PRECISION`.",
        "- Route B status: not killed until high-precision complement-basis `nu` is recomputed.",
        "",
        "## Verdict",
        "",
        f"`{verdict}`",
        "",
        "## Diagnostic Runs",
        "",
        "| run | dps | old full-projection float64 nu | new complement nu | lambda3_G | tail_margin | U_perp dim | elapsed_s |",
        "|---|---:|---:|---:|---:|---:|---:|---:|",
        row("base", base),
        row("dps+80", plus),
        "",
        "## Precision Check",
        "",
        "```json",
        json.dumps(json_safe(payload["precision_check"]), indent=2, sort_keys=True),
        "```",
        "",
        "## Conditioning",
        "",
    ]
    for label, run in (("base", base), ("dps+80", plus)):
        new = run["new_complement_tail"]
        lines += [
            f"### {label}",
            "",
            "```json",
            json.dumps(
                json_safe(
                    {
                        "gram_condition_mp": new.get("gram_condition_mp"),
                        "q_orth_error": new.get("q_orth_error"),
                        "u_orth_error": new.get("u_orth_error"),
                        "mperp_cross_error": new.get("mperp_cross_error"),
                        "q_stats": new.get("q_stats"),
                        "u_stats": new.get("u_stats"),
                    }
                ),
                indent=2,
                sort_keys=True,
            ),
            "```",
            "",
        ]
    lines += [
        "## Next Step",
        "",
    ]
    if verdict == "NU_FLOOR_FIXED_TAIL_PASS":
        lines.append("Tail `NO` was an instrument artifact. Next gate is packet/E-map precision audit for the remaining N drift.")
    elif verdict == "NU_FLOOR_FIXED_TAIL_FAIL":
        lines.append("Tail failure remains after the complement-basis repair. Inspect the rogue tail eigenvector before any broader Route B claim.")
    elif verdict == "NU_PRECISION_UNSTABLE":
        lines.append("The repaired tail eigensolve is still precision-unstable. Do not interpret the tail sign mathematically.")
    else:
        lines.append("Complement-basis construction failed conditioning/dimension checks. Fix basis/Gram representation before any tail interpretation.")
    lines.append("")
    NU_COMPLEMENT_AUDIT.write_text("\n".join(lines), encoding="utf-8")


def run_nu_complement_audit(lam_sq: int, N: int) -> str:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    lam = mp.sqrt(lam_sq)
    dps = dps_for_lam(lam)
    base = run_nu_complement_single(lam_sq, N, dps)
    plus = run_nu_complement_single(lam_sq, N, dps + 80)
    verdict, precision_check = classify_nu_complement(base, plus)
    payload = {
        "verdict": verdict,
        "runs": {"dps": base, "dps_plus_80": plus},
        "precision_check": precision_check,
    }
    write_json(OUT_DIR / f"nu_complement_lambda_sq_{lam_sq}_N_{N}.json", payload)
    write_nu_complement_audit(payload)
    return verdict


def project_to_mperp(v: mp.matrix, q_basis: Sequence[mp.matrix]) -> mp.matrix:
    out = copy_vec(v)
    for q in q_basis:
        subtract_projection_in_place(out, q)
    return out


def parity_score(v: mp.matrix) -> mp.mpc:
    return sum(mp.conj(v[i]) * v[v.rows - 1 - i] for i in range(v.rows))


def coefficient_rows(v: mp.matrix, N: int) -> List[Dict[str, Any]]:
    rows = []
    for i in range(v.rows):
        n = i - N
        rows.append({"n": n, "re": mp.re(v[i]), "im": mp.im(v[i]), "abs": abs(v[i])})
    return rows


def top_coefficients(v: mp.matrix, N: int, limit: int = 24) -> List[Dict[str, Any]]:
    rows = coefficient_rows(v, N)
    rows.sort(key=lambda r: float(r["abs"]), reverse=True)
    return rows[:limit]


def mass_bands(v: mp.matrix, N: int) -> Dict[str, Any]:
    bands = {
        "low_abs_n_le_N_over_3": mp.mpf("0"),
        "mid_N_over_3_lt_abs_n_le_2N_over_3": mp.mpf("0"),
        "high_abs_n_gt_2N_over_3": mp.mpf("0"),
    }
    for i in range(v.rows):
        n_abs = abs(i - N)
        mass = abs(v[i]) ** 2
        if n_abs <= N / 3:
            bands["low_abs_n_le_N_over_3"] += mass
        elif n_abs <= 2 * N / 3:
            bands["mid_N_over_3_lt_abs_n_le_2N_over_3"] += mass
        else:
            bands["high_abs_n_gt_2N_over_3"] += mass
    return bands


def common_index_overlap(v_small: mp.matrix, N_small: int, v_big: mp.matrix, N_big: int) -> Dict[str, Any]:
    common = 2 * N_small + 1
    offset = N_big - N_small
    big_common = mp.matrix(common, 1)
    small_common = mp.matrix(common, 1)
    for i in range(common):
        small_common[i] = v_small[i]
        big_common[i] = v_big[i + offset]
    n_small = norm(small_common)
    n_big = norm(big_common)
    if n_small == 0 or n_big == 0:
        return {"overlap_abs": mp.nan, "big_common_mass": n_big**2, "small_common_mass": n_small**2}
    for i in range(common):
        small_common[i] /= n_small
        big_common[i] /= n_big
    return {
        "overlap_abs": abs(inner(small_common, big_common)),
        "big_common_mass": n_big**2,
        "small_common_mass": n_small**2,
    }


def run_rogue_tail_single(lam_sq: int, N: int, dps: int, include_coefficients: bool = True) -> Tuple[Dict[str, Any], mp.matrix]:
    started = time.time()
    lam = mp.sqrt(lam_sq)
    mp.mp.dps = dps
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"rogue_tail start lambda_sq={lam_sq} N={N} dps={dps}")
    T = build_tau_matrix(lam, N, dps)
    packet = make_packets(float(mp.sqrt(lam_sq)), N)
    k1 = mp_vec_from_np(packet.coeffs["g04"])
    k2o = mp_vec_from_np(packet.coeffs["g26"])
    k2e = mp_vec_from_np(packet.coeffs["g048perp"])
    m_vectors = [k1, k2o, k2e]
    q_basis, q_stats = modified_gram_schmidt_mp(m_vectors)
    if len(q_basis) != 3:
        payload = {
            "lambda_sq": lam_sq,
            "N": N,
            "dps": dps,
            "failure_code": "ROGUE_AUDIT_BLOCKED",
            "reason": "M packet vectors did not orthonormalize to dimension 3",
            "q_stats": q_stats,
            "elapsed_s": time.time() - started,
        }
        return payload, mp.matrix(0, 1)
    approx = float64_complement_guess(T, m_vectors)
    secular = restricted_tail_nu_secular(T, q_basis, approx, return_vector=True)
    if secular.get("failure_code"):
        payload = {
            "lambda_sq": lam_sq,
            "N": N,
            "dps": dps,
            "failure_code": "ROGUE_AUDIT_BLOCKED",
            "secular_failure": secular,
            "elapsed_s": time.time() - started,
        }
        return payload, mp.matrix(0, 1)
    w = secular["reconstruction"]["vector"]
    nu = secular["nu"]
    Tw = T * w
    projected_Tw = project_to_mperp(Tw, q_basis)
    residual = projected_Tw - nu * w
    ray = rayleigh(T, w)
    q_orth = [abs(inner(q, w)) for q in q_basis]
    m_orth = [abs(inner(m, w)) for m in m_vectors]
    pscore = parity_score(w)
    Tq = [T * q for q in q_basis]
    GM = mp.matrix(len(q_basis), len(q_basis))
    for i, qi in enumerate(q_basis):
        for j, Tqj in enumerate(Tq):
            GM[i, j] = inner(qi, Tqj)
    lambda_G = hermitian_eigvals_sorted(GM)
    payload = {
        "lambda_sq": lam_sq,
        "lambda": lam,
        "N": N,
        "dps": dps,
        "nu": nu,
        "rayleigh": ray,
        "rayleigh_minus_nu": ray - nu,
        "lambda_G": lambda_G,
        "lambda3_G": lambda_G[2] if len(lambda_G) >= 3 else mp.nan,
        "tail_margin": nu - lambda_G[2] if len(lambda_G) >= 3 else mp.nan,
        "norm": norm(w),
        "projected_residual_norm": norm(residual),
        "projected_residual_over_abs_nu": norm(residual) / max(abs(nu), mp.mpf("1e-300")),
        "q_orthogonality_abs": q_orth,
        "m_orthogonality_abs": m_orth,
        "max_q_orthogonality_abs": max(q_orth),
        "max_m_orthogonality_abs": max(m_orth),
        "parity_score": pscore,
        "parity_score_real": mp.re(pscore),
        "parity_score_abs": abs(pscore),
        "top_coefficients": top_coefficients(w, N),
        "mass_bands": mass_bands(w, N),
        "admissibility": {
            "boundary_null": "UNKNOWN",
            "moment_residual": "UNKNOWN",
            "reason": "No separate boundary/admissibility receiver is implemented in this pilot script.",
        },
        "known_prolate_branch_overlap": {
            "status": "MISSING_PROLATE_COMPARISON_BASIS",
            "reason": "Current packet builder exposes only g04, g26, and g048perp; additional candidate packets were not defined without changing the model.",
        },
        "secular": {k: v for k, v in secular.items() if k != "reconstruction"},
        "reconstruction": {
            "F_smallest_abs_eigenvalue": secular["reconstruction"].get("F_smallest_abs_eigenvalue"),
            "root_at_unconstrained_eigenvalue": secular["reconstruction"].get("root_at_unconstrained_eigenvalue", False),
        },
        "elapsed_s": time.time() - started,
    }
    if include_coefficients:
        payload["coefficients"] = coefficient_rows(w, N)
    append_log(OUT_DIR / "routeb_ladder_pilot.log", f"rogue_tail done lambda_sq={lam_sq} N={N} dps={dps}")
    return payload, w


def classify_rogue_tail(payload: Dict[str, Any]) -> str:
    base = payload["runs"]["N120_dps"]
    plus = payload["runs"]["N120_dps_plus_80"]
    nstab = payload["comparisons"]["N90_vs_N120_common"]
    dps_overlap = payload["comparisons"]["dps197_vs_dps277_N120"].get("overlap_abs")
    if base.get("failure_code") or plus.get("failure_code"):
        return "ROGUE_AUDIT_BLOCKED"
    if float(base.get("projected_residual_norm", mp.inf)) > 1e-30:
        return "ROGUE_NUMERICAL_ARTIFACT"
    if float(base.get("max_m_orthogonality_abs", mp.inf)) > 1e-30:
        return "ROGUE_NUMERICAL_ARTIFACT"
    if dps_overlap is not None and float(dps_overlap) < 0.999:
        return "ROGUE_NUMERICAL_ARTIFACT"
    if nstab.get("overlap_abs") is not None and float(nstab["overlap_abs"]) < 0.95:
        return "ROGUE_BASIS_TRUNCATION_ARTIFACT"
    return "MISSING_PROLATE_COMPARISON_BASIS"


def write_rogue_tail_audit(payload: Dict[str, Any]) -> None:
    verdict = payload["verdict"]
    base = payload["runs"]["N120_dps"]
    plus = payload["runs"]["N120_dps_plus_80"]
    n90 = payload["runs"]["N90_dps"]
    lines = [
        "# Route B TwoLevelSpectralLadder Rogue Tail Audit",
        "",
        "Status: diagnostic only. Not a proof of RH. Not a Route B kill.",
        "Phase 2 was not run. The full ladder was not rerun. QW formulas and packet definitions were not changed.",
        "",
        "## Headline",
        "",
        f"1. Is `w_tail` a valid high-precision complement eigenvector? [{'NO' if base.get('failure_code') else 'YES'}]",
        "2. Is `w_tail` admissible / boundary-null? [UNKNOWN]",
        "3. Is `w_tail` explained by a missing prolate branch? [UNKNOWN]",
        f"4. Verdict code: `{verdict}`",
        "",
        "## Current Status Codes",
        "",
        "```text",
        "FAILURE_CODE = N_LIMIT_NOT_STABLE",
        "PRIMARY_DIAGNOSIS = NU_FLOOR_FIXED_TAIL_FAIL",
        "SECONDARY_DIAGNOSIS = BASIS_TRUNCATION_NOT_STABLE_PENDING_PACKET_PRECISION",
        "NEXT_GATE = RogueTailEigenvectorAudit",
        "```",
        "",
        "## N120 Precision Runs",
        "",
        "| run | dps | nu | lambda3_G | tail_margin | residual | max M-orth | parity real | elapsed_s |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for label, run in (("base", base), ("dps+80", plus)):
        lines.append(
            f"| {label} | {run.get('dps')} | {mp_to_str(run.get('nu'))} | "
            f"{mp_to_str(run.get('lambda3_G'))} | {mp_to_str(run.get('tail_margin'))} | "
            f"{mp_to_str(run.get('projected_residual_norm'))} | {mp_to_str(run.get('max_m_orthogonality_abs'))} | "
            f"{mp_to_str(run.get('parity_score_real'))} | {run.get('elapsed_s')} |"
        )
    lines += [
        "",
        "## N-Stability Vector Check",
        "",
        "```json",
        json.dumps(json_safe(payload["comparisons"]), indent=2, sort_keys=True),
        "```",
        "",
        "## Localization",
        "",
        "### N120 base mass bands",
        "",
        "```json",
        json.dumps(json_safe(base.get("mass_bands", {})), indent=2, sort_keys=True),
        "```",
        "",
        "### N120 base top coefficients",
        "",
        "```json",
        json.dumps(json_safe(base.get("top_coefficients", [])), indent=2, sort_keys=True),
        "```",
        "",
        "## Admissibility And Missing Branch Checks",
        "",
        "```json",
        json.dumps(
            json_safe(
                {
                    "admissibility": base.get("admissibility"),
                    "known_prolate_branch_overlap": base.get("known_prolate_branch_overlap"),
                }
            ),
            indent=2,
            sort_keys=True,
        ),
        "```",
        "",
        "## Interpretation",
        "",
    ]
    if verdict == "ROGUE_BASIS_TRUNCATION_ARTIFACT":
        lines.append("The rogue direction is not stable between N=90 and N=120; classify as a basis truncation artifact before any model-kill claim.")
    elif verdict == "MISSING_PROLATE_COMPARISON_BASIS":
        lines.append("The rogue vector passes the numerical complement-eigenvector checks, but the pilot lacks additional prolate comparison packets and admissibility receivers. Do not confirm a genuine rogue state yet.")
    elif verdict == "ROGUE_NUMERICAL_ARTIFACT":
        lines.append("The reconstructed vector failed numerical validity checks; repair the eigensolve/reconstruction before interpretation.")
    else:
        lines.append("See verdict code above; do not promote beyond this diagnostic without Proshka review.")
    lines.append("")
    lines += [
        "## Output JSON",
        "",
        f"- `out/rogue_tail_lambda_sq_{base.get('lambda_sq')}_N_120.json`",
        f"- `out/rogue_tail_lambda_sq_{n90.get('lambda_sq')}_N_90.json`",
        "",
    ]
    ROGUE_TAIL_AUDIT.write_text("\n".join(lines), encoding="utf-8")


def run_rogue_tail_audit(lam_sq: int, N: int) -> str:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    lam = mp.sqrt(lam_sq)
    dps = dps_for_lam(lam)
    base, w_base = run_rogue_tail_single(lam_sq, N, dps, include_coefficients=True)
    plus, w_plus = run_rogue_tail_single(lam_sq, N, dps + 80, include_coefficients=False)
    n_small = 90 if N >= 120 else max(10, N - 30)
    small, w_small = run_rogue_tail_single(lam_sq, n_small, dps, include_coefficients=False)
    comparisons = {
        "dps197_vs_dps277_N120": {
            "overlap_abs": abs(inner(w_base, w_plus)) if w_base.rows == w_plus.rows and w_base.rows else mp.nan,
        },
        "N90_vs_N120_common": common_index_overlap(w_small, n_small, w_base, N) if w_small.rows and w_base.rows else {},
    }
    payload = {
        "runs": {"N120_dps": base, "N120_dps_plus_80": plus, "N90_dps": small},
        "comparisons": comparisons,
    }
    verdict = classify_rogue_tail(payload)
    payload["verdict"] = verdict
    write_json(OUT_DIR / f"rogue_tail_lambda_sq_{lam_sq}_N_{N}.json", payload)
    write_json(OUT_DIR / f"rogue_tail_lambda_sq_{lam_sq}_N_{n_small}.json", {"run": small})
    write_rogue_tail_audit(payload)
    return verdict


def search_repo_definitions() -> str:
    log_path = OUT_DIR / "definition_search.log"
    if log_path.exists():
        log_path.unlink()
    queries = [
        "QW_lambda|QW\\\\b|pro_ang1|PSWF|E-map|E_map|k_lambda|b_lambda|g04|g26|g048|TwoLevelSpectralLadder",
        "Zeta spectral triples|2511\\\\.22755|alpha_L|beta_L|gamma_L|Hurwitz-Lerch|QW N",
    ]
    for q in queries:
        append_log(log_path, f"$ rg -n {q!r} ...")
        cmd = [
            "rg",
            "-n",
            q,
            "q3.lean.aristotle",
            "docs/trackB",
            "full/sections",
            "-g",
            "!q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/node.md",
            "-g",
            "!q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_ladder_pilot.py",
            "-g",
            "!q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/report.md",
            "-g",
            "!q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/**",
        ]
        proc = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        lines = proc.stdout.splitlines()
        append_log(log_path, "\n".join(lines[:200]) if lines else "(no hits)")
        if len(lines) > 200:
            append_log(log_path, f"... truncated {len(lines) - 200} additional hits")
    return log_path.read_text(encoding="utf-8")


def write_report(
    failure_code: Optional[str],
    definitions_log: str,
    calibration: Dict[str, Any],
    ladder: List[Dict[str, Any]],
    fits: Dict[str, Any],
    notes: Optional[List[str]] = None,
) -> None:
    notes = notes or []
    if failure_code and not ladder:
        odd = "UNKNOWN; parity(xi2)=NA; overlaps=NA; slopes=NA"
        tail = "UNKNOWN; margin=NA"
        wline = "UNKNOWN; value NA +/- NA"
    elif not ladder:
        odd = "UNKNOWN; parity(xi2)=NA; overlaps=NA; slopes=NA"
        tail = "UNKNOWN; margin=NA"
        wline = "UNKNOWN; value NA +/- NA"
    else:
        row120 = [r for r in ladder if r.get("N") == 120]
        last = row120[-1] if row120 else (ladder[-1] if ladder else {})
        odd_active = "UNKNOWN"
        if last:
            oo = last.get("overlaps", {})
            odd_active = "YES" if oo.get("xi2_k2_odd", 0) > oo.get("xi2_k2_even", 0) else "NO"
        odd_fit = fits.get("mu2", {})
        wfit = fits.get("W_actual", {})
        odd = (
            f"{odd_active}; parity(xi2)={last.get('parity_xi2', 'NA')}; "
            f"overlaps={last.get('overlaps', 'NA')}; slopes={odd_fit.get('slope', 'NA')} +/- {odd_fit.get('stderr', 'NA')}"
        )
        margin = last.get("tail_margin", "NA")
        tail_ok = "YES" if isinstance(margin, (int, float)) and margin >= 0 else "NO"
        tail = f"{tail_ok}; margin={margin}"
        slope = wfit.get("slope")
        if slope is None:
            wclass = "UNKNOWN"
        elif abs(slope + 3.5) < 1.0:
            wclass = "-3.5"
        elif abs(slope + 7.5) < 1.0:
            wclass = "-7.5"
        else:
            wclass = "other"
        wline = f"{wclass}; value {slope} +/- {wfit.get('stderr')}"

    lines = [
        f"1. Does k2_odd set mu2? [{odd}]",
        f"2. Tail: nu >= lambda3_G + margin? [{tail}]",
        f"3. W_actual decay slope: [{wline}]",
        "",
        "# Route B TwoLevelSpectralLadder Pilot Report",
        "",
        "Status: NOT a proof of RH. Diagnostic Route B/G4 numerical falsifier only.",
        "",
        "## Verdict",
    ]
    if failure_code:
        lines.append(f"FAILURE_CODE: {failure_code}")
    elif not ladder:
        lines.append("IN_PROGRESS: calibration passed; ladder not run in this invocation.")
    else:
        lines.append("PASS")
    lines += [
        "",
        "## Files searched and definitions used",
        "",
        "- Search log: `ACTIVE/requests/routeB_twolevel_spectral_ladder/out/definition_search.log`.",
        "- No executable repo implementation of `QW_lambda`, prolate packet, E-map, `k_lambda`, or `b_lambda` was used.",
        "- Local source formulas used: `q3.lean.aristotle/literature/zotero/H8ULBMAL/fulltext.md` (arXiv:2511.22755), especially Sections 2.2, 3.1, 4.1-4.3, and 5.1.",
        "- Implementation file: `ACTIVE/requests/routeB_twolevel_spectral_ladder/routeb_ladder_pilot.py`.",
        "",
        "## Conventions",
        "",
        "- `L = 2*log(lambda)`, basis indices are `n=-N..N`, and `T=QW_lambda^N` is assembled as `W02 - WR - WP`.",
        "- `WR` uses the Prop. 4.2 decomposed coefficients `alpha_L`, `beta_L`, `gamma_L`; `Phi(z,2,a)` is evaluated by its fast `|z|<1` series.",
        "- `WP` sums prime powers `1 < k <= exp(L)` with weight `Lambda(k)*k^(-1/2)`.",
        "- Packet vectors are built from the MATH SPEC zero-integral prolate combinations; `b` is the direct quadrature norm of `E(g04)` and is not fitted.",
        "- Numerical evidence only: no RH claim and no zero-side matching.",
        "",
        "## Calibration log",
        "",
        "```json",
        json.dumps(json_safe(calibration), indent=2, sort_keys=True),
        "```",
        "",
    ]
    if ladder:
        lines += [
            "## N-stabilization table (lambda=sqrt(14))",
            "",
            "```json",
            json.dumps(json_safe(fits.get("N_stabilization", {})), indent=2, sort_keys=True),
            "```",
            "",
            "## Full ladder table",
            "",
        ]
        for r in ladder:
            lines.append(
                f"- lambda=sqrt({r.get('lambda_sq')}), N={r.get('N')}, "
                f"dps={r.get('dps')}, elapsed_s={r.get('elapsed_s')}, "
                f"mu1={mp_to_str(r.get('mu1'))}, mu2={mp_to_str(r.get('mu2'))}, "
                f"Delta={mp_to_str(r.get('Delta'))}, nu={r.get('nu')}, W_actual={mp_to_str(r.get('W_actual'))}, "
                f"json=`out/lambda_sq_{r.get('lambda_sq')}_N_{r.get('N')}.json`"
            )
        lines += ["", "## Fits", "", "```json", json.dumps(json_safe(fits), indent=2, sort_keys=True), "```", ""]
    if notes:
        lines += ["## Notes", ""]
        lines.extend(f"- {n}" for n in notes)
        lines.append("")
    lines += [
        "## Next exact theorem/gap suggestion",
        "",
    ]
    if failure_code == "MATRIX_CONVENTION_MISMATCH":
        lines.append("Resolve the matrix convention mismatch before any ladder run; do not interpret spectral quantities.")
    elif failure_code == "PRECISION_UNSTABLE":
        lines.append("Stabilize multiprecision matrix assembly/eigensolve before ladder; do not fit exponents.")
    elif failure_code:
        lines.append("Use the failure code above as the next exact blocker.")
    else:
        lines.append("Promote only the observed numerical theorem shape; no RH claim and no zero-side matching.")
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--calibration-only", action="store_true")
    parser.add_argument("--reuse-calibration", action="store_true")
    parser.add_argument("--report-from-summary", action="store_true")
    parser.add_argument("--nu-complement-diagnostic", action="store_true")
    parser.add_argument("--rogue-tail-audit", action="store_true")
    parser.add_argument("--lambda-sq", type=int, default=14)
    parser.add_argument("--N", "--n", dest="N", type=int, default=120)
    args = parser.parse_args()

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    if args.nu_complement_diagnostic:
        verdict = run_nu_complement_audit(args.lambda_sq, args.N)
        print(verdict)
        return 0
    if args.rogue_tail_audit:
        verdict = run_rogue_tail_audit(args.lambda_sq, args.N)
        print(verdict)
        return 0

    definitions_log = search_repo_definitions()
    if args.report_from_summary:
        calibration_path = OUT_DIR / "calibration.json"
        summary_path = OUT_DIR / "phase1_summary.json"
        if not calibration_path.exists() or not summary_path.exists():
            raise SystemExit("Missing calibration.json or phase1_summary.json")
        cached = json.loads(calibration_path.read_text(encoding="utf-8"))
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
        write_report(
            summary.get("failure_code"),
            definitions_log,
            cached.get("calibration", {}),
            summary.get("ladder", []),
            summary.get("fits", {}),
            [],
        )
        return 1 if summary.get("failure_code") else 0
    calibration_path = OUT_DIR / "calibration.json"
    if args.reuse_calibration and calibration_path.exists():
        cached = json.loads(calibration_path.read_text(encoding="utf-8"))
        failure = cached.get("failure_code")
        calibration = cached.get("calibration", {})
    else:
        failure, calibration = run_calibration()
        write_json(calibration_path, {"failure_code": failure, "calibration": calibration})
    if failure:
        write_report(failure, definitions_log, calibration, [], {}, [])
        return 1
    if args.calibration_only:
        write_report(None, definitions_log, calibration, [], {}, ["Calibration-only run completed; ladder not started by flag."])
        return 0

    ladder: List[Dict[str, Any]] = []
    failure_code: Optional[str] = None
    for lam_sq in (12, 13, 14):
        for N in (60, 90, 120):
            cell = run_ladder_cell(lam_sq, N)
            write_json(OUT_DIR / f"lambda_sq_{lam_sq}_N_{N}.json", cell)
            ladder.append(cell)
            if cell.get("failure_code"):
                failure_code = str(cell["failure_code"])
                break
        if failure_code:
            break

    fits: Dict[str, Any] = {}
    if not failure_code:
        nstab = check_n_stabilization(ladder)
        fits["N_stabilization"] = nstab
        if not nstab["pass"]:
            failure_code = "N_LIMIT_NOT_STABLE"
        for key in ("mu1", "mu2", "Delta", "nu", "eta1_over_1_minus_chi4", "W_actual", "W_bound", "b"):
            fits[key] = fit_slope(ladder, key)
        if not failure_code:
            last120 = [r for r in ladder if r.get("N") == 120]
            if any(float(r.get("tail_margin", -1)) < 0 for r in last120):
                failure_code = "ROGUE_STATE_BELOW_LADDER"
            w_slope = fits.get("W_actual", {}).get("slope")
            if not failure_code and (w_slope is None or w_slope >= 0):
                failure_code = "W_NOT_DECAYING"

    write_json(OUT_DIR / "phase1_summary.json", {"failure_code": failure_code, "ladder": ladder, "fits": fits})
    write_report(failure_code, definitions_log, calibration, ladder, fits, [])
    return 1 if failure_code else 0


if __name__ == "__main__":
    raise SystemExit(main())
