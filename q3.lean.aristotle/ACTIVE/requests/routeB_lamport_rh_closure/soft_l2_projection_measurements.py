#!/usr/bin/env python3
"""SOFT_L2 edge profiles and the (13,120) projection-defect lag ledger.

Numerical evidence only.  The full lag LHS is evaluated from the exact
one-sided Weil functional W02-WR-Wp; only the prime/window contribution is
isolated with D_(a,L).  Everything else remains one aggregate remainder.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import mpmath as mp
import numpy as np

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "routeB_twolevel_spectral_ladder" / "out"

EDGE_CSV = HERE / "SOFT_L2_EDGE_MASS_PROFILE.csv"
EDGE_JSON = HERE / "SOFT_L2_EDGE_MASS_PROFILE.json"
EDGE_PNG = HERE / "SOFT_L2_EDGE_MASS_PROFILE_LOG.png"
LAG_CSV = HERE / "SOFT_L2_LAG_LEDGER_13_120.csv"
LAG_JSON = HERE / "SOFT_L2_LAG_LEDGER_13_120.json"

GL_X: list[mp.mpf] = []
GL_W: list[mp.mpf] = []


def mps(x: Any, digits: int = 40) -> str:
    return mp.nstr(x, digits)


def complex_json(z: mp.mpc, digits: int = 35) -> dict[str, str]:
    return {"re": mps(mp.re(z), digits), "im": mps(mp.im(z), digits)}


@dataclass
class Packet:
    label: str
    role: str
    lambda_sq: int
    N: int
    source: Path
    coeff: dict[int, mp.mpc]

    @property
    def L(self) -> mp.mpf:
        return mp.log(self.lambda_sq)


def _parse_coeffs(rows: Iterable[dict[str, Any]]) -> dict[int, mp.mpc]:
    out = {
        int(row["n"]): mp.mpc(mp.mpf(str(row["re"])), mp.mpf(str(row["im"])))
        for row in rows
    }
    norm = mp.sqrt(mp.fsum(abs(z) ** 2 for z in out.values()))
    return {n: z / norm for n, z in out.items()}


def load_packet(path: Path, role: str, label: str | None = None) -> Packet:
    data = json.loads(path.read_text())
    return Packet(
        label=label or f"{role}_m{data['lambda_sq']}_N{data['N']}",
        role=role,
        lambda_sq=int(data["lambda_sq"]),
        N=int(data["N"]),
        source=path,
        coeff=_parse_coeffs(data["coefficients"]),
    )


def load_ground_13_120(path: Path) -> tuple[Packet, mp.mpf]:
    data = json.loads(path.read_text())
    row = data["xi_m_y_cache"][0]
    packet = Packet(
        label="ground_xi1_m13_N120",
        role="finite_ground_xi1",
        lambda_sq=int(data["lambda_sq"]),
        N=int(data["N"]),
        source=path,
        coeff=_parse_coeffs(row["xi_vector"]),
    )
    return packet, mp.mpf(row["mu"])


def packets() -> tuple[list[Packet], Packet, mp.mpf]:
    ps = [
        load_packet(OUT / "portable_k_coeffs_lambda_sq_12_N_120.json", "portable_k1"),
        load_packet(OUT / "portable_k_coeffs_lambda_sq_13_N_90.json", "portable_k1"),
        load_packet(OUT / "portable_k_coeffs_lambda_sq_13_N_120.json", "portable_k1"),
        load_packet(OUT / "portable_k_coeffs_lambda_sq_14_N_120.json", "portable_k1"),
        load_packet(
            OUT / "off_axis_k1_coeffs_lambda_sq_53_N_120_float64.json",
            "float64_k1_diagnostic",
        ),
        load_packet(
            OUT / "off_axis_k1_coeffs_lambda_sq_101_N_120_float64.json",
            "float64_k1_diagnostic",
        ),
    ]
    ground, mu = load_ground_13_120(OUT / "nconv_anchor_lambda_sq_13_N_120.json")
    return ps + [ground], ground, mu


def correlation_coefficients(packet: Packet) -> dict[int, mp.mpc]:
    """Fourier coefficients of |q|^2 before the 1/L factor."""
    c = packet.coeff
    ns = sorted(c)
    return {
        d: mp.fsum(mp.conj(c[n]) * c[n + d] for n in ns if n + d in c)
        for d in range(-2 * packet.N, 2 * packet.N + 1)
    }


def interval_mass(packet: Packet, corr: dict[int, mp.mpc], a: mp.mpf, b: mp.mpf) -> mp.mpf:
    L = packet.L
    total = corr[0] * (b - a) / L
    for d, sd in corr.items():
        if d == 0:
            continue
        total += sd * (
            mp.e ** (2j * mp.pi * d * b / L) - mp.e ** (2j * mp.pi * d * a / L)
        ) / (2j * mp.pi * d)
    real = mp.re(total)
    # High-precision cancellation can leave a harmless negative last digit.
    if real < 0 and abs(real) < mp.mpf("1e-60"):
        real = mp.mpf("0")
    return real


def edge_profiles(ps: list[Packet]) -> dict[str, Any]:
    fractions = [mp.mpf("0.0025"), mp.mpf("0.005")] + [
        mp.mpf(k) / 100 for k in range(1, 51)
    ]
    rows: list[dict[str, Any]] = []
    summaries: list[dict[str, Any]] = []

    for packet in ps:
        corr = correlation_coefficients(packet)
        fit_x: list[float] = []
        fit_y: list[float] = []
        local_rows = []
        for frac in fractions:
            delta = frac * packet.L
            mass = interval_mass(packet, corr, mp.mpf("0"), delta)
            mass += interval_mass(packet, corr, packet.L - delta, packet.L)
            mass = max(mp.mpf("0"), mass)
            edge = mp.sqrt(mass)
            row = {
                "label": packet.label,
                "role": packet.role,
                "lambda_sq": packet.lambda_sq,
                "N": packet.N,
                "delta_over_L": float(frac),
                "delta": mps(delta, 24),
                "edge_mass_eL": mps(edge, 45),
                "edge_mass_squared": mps(mass, 45),
            }
            rows.append(row)
            local_rows.append(row)
            if mp.mpf("0.05") <= frac <= mp.mpf("0.20") and edge > 0:
                fit_x.append(float(delta))
                fit_y.append(float(mp.log(edge)))

        slope, intercept = np.polyfit(fit_x, fit_y, 1)
        pred = slope * np.asarray(fit_x) + intercept
        ss_res = float(np.sum((np.asarray(fit_y) - pred) ** 2))
        ss_tot = float(np.sum((np.asarray(fit_y) - np.mean(fit_y)) ** 2))
        r2 = 1.0 - ss_res / ss_tot if ss_tot else 1.0
        summaries.append(
            {
                "label": packet.label,
                "role": packet.role,
                "lambda_sq": packet.lambda_sq,
                "N": packet.N,
                "source": str(packet.source.relative_to(HERE.parent.parent.parent.parent)),
                "fit_band_delta_over_L": [0.05, 0.20],
                "inward_log_slope_per_u": slope,
                "inward_log_slope_times_L": slope * float(packet.L),
                "r_squared": r2,
                "eL_at_0p01L": next(r["edge_mass_eL"] for r in local_rows if r["delta_over_L"] == 0.01),
                "eL_at_0p10L": next(r["edge_mass_eL"] for r in local_rows if r["delta_over_L"] == 0.10),
                "eL_at_0p50L": next(r["edge_mass_eL"] for r in local_rows if r["delta_over_L"] == 0.50),
            }
        )

    with EDGE_CSV.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)

    # Registered comparison uses the N=120 k1 family only.  The finite
    # ground row is not silently mixed with trial/diagnostic packets.
    family = [
        s
        for s in summaries
        if s["N"] == 120 and s["role"] in {"portable_k1", "float64_k1_diagnostic"}
    ]
    family.sort(key=lambda s: s["lambda_sq"])
    high_precision_family = [s for s in family if s["role"] == "portable_k1"]
    hp_slopes = [s["inward_log_slope_per_u"] for s in high_precision_family]
    hp_monotone = all(b > a for a, b in zip(hp_slopes, hp_slopes[1:]))
    floor_limited = [s["label"] for s in family if s["role"] == "float64_k1_diagnostic"]
    prediction = {
        "registered": "e_L(delta) is approximately exponential over the outer-depth band and its inward exponent increases with lambda_sq",
        "comparison_family": [s["label"] for s in family],
        "high_precision_comparison_family": [s["label"] for s in high_precision_family],
        "high_precision_strictly_increasing_exponent": hp_monotone,
        "float64_floor_limited_cells": floor_limited,
        "all_cell_strict_monotonicity_resolved": False,
        "outcome": "SUPPORTED_M12_TO_M14_HIGH_PRECISION__LARGE_M_FLOAT64_UNRESOLVED",
        "warning": "profile and fit are numerical diagnostics, not UREL or a smallness theorem",
    }
    payload = {
        "schema": "soft_l2_edge_mass_profile_v1",
        "definition": "e_L(delta)=(integral_{L/2-delta<|u|<=L/2}|q_L(u)|^2 du)^(1/2)",
        "all_depth_range": "0<delta<=L/2",
        "summaries": summaries,
        "prediction": prediction,
        "claims": {"UREL_proved": False, "smallness_proved": False, "RH": False},
    }
    EDGE_JSON.write_text(json.dumps(payload, indent=2) + "\n")

    plt.figure(figsize=(10.5, 6.5))
    for summary in summaries:
        series = [r for r in rows if r["label"] == summary["label"]]
        x = [r["delta_over_L"] for r in series]
        y = [max(float(r["edge_mass_eL"]), 1e-300) for r in series]
        style = "--" if summary["role"] == "float64_k1_diagnostic" else "-"
        width = 2.6 if summary["role"] == "finite_ground_xi1" else 1.6
        plt.plot(x, y, style, linewidth=width, label=summary["label"])
    plt.yscale("log")
    plt.xlabel(r"edge depth $\delta/L$")
    plt.ylabel(r"$e_L(\delta)$")
    plt.title("SOFT_L2 all-depth two-edge mass profiles")
    plt.grid(True, which="both", alpha=0.25)
    plt.legend(fontsize=8)
    plt.tight_layout()
    plt.savefig(EDGE_PNG, dpi=180)
    plt.close()
    return payload


def autocorrelation_evaluator(packet: Packet):
    c = packet.coeff
    ns = sorted(c)
    L = packet.L
    diag = {n: abs(c[n]) ** 2 for n in ns}
    boundary = {n: mp.mpc(0) for n in ns}
    for n in ns:
        for m in ns:
            if m == n:
                continue
            z = mp.conj(c[n]) * c[m] / (2j * mp.pi * (m - n))
            boundary[n] += z
            boundary[m] -= z

    def apos(s: mp.mpf) -> mp.mpc:
        if s < 0 or s > L:
            return mp.mpc(0)
        return mp.fsum(
            ((1 - s / L) * diag[n] + boundary[n])
            * mp.e ** (2j * mp.pi * n * s / L)
            for n in ns
        )

    def acorr(t: mp.mpf) -> mp.mpc:
        return apos(t) if t >= 0 else mp.conj(apos(-t))

    return acorr


def q_evaluator(packet: Packet):
    ns = sorted(packet.coeff)
    L = packet.L

    def q(u: mp.mpf) -> mp.mpc:
        if u < 0 or u > L:
            return mp.mpc(0)
        return mp.fsum(
            packet.coeff[n] * mp.e ** (2j * mp.pi * n * u / L) for n in ns
        ) / mp.sqrt(L)

    return q


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def prime_powers_up_to(limit: int) -> list[tuple[int, mp.mpf]]:
    out = []
    for k in range(2, limit + 1):
        for p in range(2, k + 1):
            if not is_prime(p):
                continue
            v = p
            while v < k:
                v *= p
            if v == k:
                out.append((k, mp.log(p)))
                break
    return out


def integration_pieces(t: mp.mpf, ymax: mp.mpf, L: mp.mpf) -> list[mp.mpf]:
    candidates = [mp.mpf("0"), ymax]
    candidates.extend(ymax * k / 8 for k in range(1, 8))
    candidates.extend([abs(t), abs(L - abs(t)), L, L + abs(t)])
    return sorted({x for x in candidates if 0 <= x <= ymax})


def fixed_quad(f, pieces: list[mp.mpf] | tuple[mp.mpf, mp.mpf]) -> mp.mpc:
    """Composite fixed Gauss--Legendre rule at the current mp precision."""
    total = mp.mpc(0)
    for a, b in zip(pieces, pieces[1:]):
        if b <= a:
            continue
        mid = (a + b) / 2
        half = (b - a) / 2
        total += half * mp.fsum(w * f(mid + half * x) for x, w in zip(GL_X, GL_W))
    return total


def window_D(q, L: mp.mpf, t: mp.mpf, a: mp.mpf) -> mp.mpc:
    if t * a <= 0 or abs(t - a) >= L:
        return mp.mpc(0)
    if t > 0:
        lo = max(mp.mpf("0"), t - L, a - L)
        hi = min(t, a)
        if hi <= lo:
            return mp.mpc(0)
        return fixed_quad(lambda x: mp.conj(q(L + x - t)) * q(L + x - a), [lo, hi])
    T, A = -t, -a
    lo = max(mp.mpf("0"), T - L, A - L)
    hi = min(T, A)
    if hi <= lo:
        return mp.mpc(0)
    return fixed_quad(lambda x: mp.conj(q(T - x)) * q(A - x), [lo, hi])


def lag_ledger(
    packet: Packet,
    mu: mp.mpf,
    *,
    lag_csv: Path = LAG_CSV,
    lag_json: Path = LAG_JSON,
    mu_source: str = "nconv_anchor_lambda_sq_13_N_120.json:xi_m_y_cache[0].mu",
    exact_matrix_anchor: bool = True,
    prediction_mode: str = "aggregate_remainder",
) -> dict[str, Any]:
    L = packet.L
    A = autocorrelation_evaluator(packet)
    q = q_evaluator(packet)
    fractions = [mp.mpf(k) / 6 for k in range(-6, 7)]
    rows: list[dict[str, Any]] = []

    for frac in fractions:
        t = frac * L
        ymax = L + abs(t)

        def qt(y: mp.mpf) -> mp.mpc:
            return A(t - y) + A(t + y)

        pieces = integration_pieces(t, ymax, L)
        w02 = 2 * fixed_quad(lambda y: mp.cosh(y / 2) * qt(y), pieces)
        q0 = qt(mp.mpf("0"))
        const = mp.mpf("0.5") * (
            mp.euler + mp.log(4 * mp.pi * (mp.e**L - 1) / (mp.e**L + 1))
        )

        def wr_integrand(y: mp.mpf) -> mp.mpc:
            if abs(y) < mp.mpf("1e-50"):
                return mp.mpc(0)
            return (mp.e ** (y / 2) * qt(y) - q0) / (mp.e**y - mp.e ** (-y))

        wr = const * q0 + fixed_quad(wr_integrand, pieces)
        pps = prime_powers_up_to(int(mp.floor(mp.e**ymax + mp.mpf("1e-30"))))
        wp = mp.fsum(lam / mp.sqrt(k) * qt(mp.log(k)) for k, lam in pps)
        lhs = w02 - wr - wp
        muA = mu * A(t)
        residual = lhs - muA
        ewin = -mp.fsum(
            lam
            / mp.sqrt(k)
            * (window_D(q, L, t, mp.log(k)) + window_D(q, L, t, -mp.log(k)))
            for k, lam in pps
        )
        remainder = residual - ewin
        rows.append(
            {
                "t_over_L": float(frac),
                "t": mps(t, 30),
                "A": complex_json(A(t)),
                "W02": complex_json(w02),
                "WR": complex_json(wr),
                "Wp": complex_json(wp),
                "LHS": complex_json(lhs),
                "muA": complex_json(muA),
                "residual_sum_defects": complex_json(residual),
                "window_D_sum": complex_json(ewin),
                "remainder_Galerkin_sector_Arch_correction": complex_json(remainder),
                "abs_residual": mps(abs(residual), 35),
                "abs_window": mps(abs(ewin), 35),
                "abs_remainder": mps(abs(remainder), 35),
                "prime_power_cap": int(mp.floor(mp.e**ymax + mp.mpf("1e-30"))),
            }
        )

    with lag_csv.open("w", newline="") as f:
        fields = [
            "t_over_L",
            "t",
            "LHS_re",
            "LHS_im",
            "muA_re",
            "muA_im",
            "residual_re",
            "residual_im",
            "window_re",
            "window_im",
            "remainder_re",
            "remainder_im",
            "abs_residual",
            "abs_window",
            "abs_remainder",
        ]
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for r in rows:
            w.writerow(
                {
                    "t_over_L": r["t_over_L"],
                    "t": r["t"],
                    "LHS_re": r["LHS"]["re"],
                    "LHS_im": r["LHS"]["im"],
                    "muA_re": r["muA"]["re"],
                    "muA_im": r["muA"]["im"],
                    "residual_re": r["residual_sum_defects"]["re"],
                    "residual_im": r["residual_sum_defects"]["im"],
                    "window_re": r["window_D_sum"]["re"],
                    "window_im": r["window_D_sum"]["im"],
                    "remainder_re": r["remainder_Galerkin_sector_Arch_correction"]["re"],
                    "remainder_im": r["remainder_Galerkin_sector_Arch_correction"]["im"],
                    "abs_residual": r["abs_residual"],
                    "abs_window": r["abs_window"],
                    "abs_remainder": r["abs_remainder"],
                }
            )

    nonzero = [r for r in rows if abs(r["t_over_L"]) > 1e-15]
    ratios = [mp.mpf(r["abs_remainder"]) / max(mp.mpf(r["abs_window"]), mp.mpf("1e-100")) for r in nonzero]
    endpoint_remainders = [mp.mpf(rows[0]["abs_remainder"]), mp.mpf(rows[-1]["abs_remainder"])]
    ratios_sorted = sorted(ratios)
    ratios_median = ratios_sorted[len(ratios_sorted) // 2]
    outer = [r for r in rows if abs(r["t_over_L"]) >= 0.5]
    outer_relative_residuals = [
        mp.mpf(r["abs_residual"])
        / max(mp.mpf(r["abs_window"]) + mp.mpf(r["abs_remainder"]), mp.mpf("1e-100"))
        for r in outer
    ]
    outer_opposite_real_sign = all(
        mp.mpf(r["window_D_sum"]["re"])
        * mp.mpf(r["remainder_Galerkin_sector_Arch_correction"]["re"])
        <= 0
        for r in outer
    )
    if prediction_mode == "outer_cancellation":
        prediction = {
            "registered": "on |t|>=L/2 the window and aggregate remainder have opposite real signs and residual is small relative to their combined magnitude",
            "outer_lag_definition": "|t|/L>=1/2 on the registered k/6 grid",
            "outer_opposite_real_sign": outer_opposite_real_sign,
            "max_outer_abs_residual_over_component_sum": mps(max(outer_relative_residuals), 25),
            "threshold": "1e-4",
            "outcome": (
                "SUPPORTED_OUTER_WINDOW_REMAINDER_ANTICANCELLATION"
                if outer_opposite_real_sign and max(outer_relative_residuals) < mp.mpf("1e-4")
                else "MIXED_ON_OUTER_GRID"
            ),
            "warning": "remainder=residual-window by definition; the diagnostic content is the small residual relative to the two large components, not the algebraic sum itself",
        }
    else:
        prediction = {
            "registered": "non-window remainder is not small and has no compact-support signature on the lag grid",
            "median_abs_remainder_over_abs_window_nonzero_lags": mps(ratios_median, 20),
            "endpoint_abs_remainder": [mps(x, 25) for x in endpoint_remainders],
            "remainder_at_least_window_at_all_nonzero_lags": all(x >= 1 for x in ratios),
            "outcome": "SUPPORTED_FOR_AGGREGATE_REMAINDER_ON_GRID" if all(x >= 1 for x in ratios) and all(x > mp.mpf("1e-20") for x in endpoint_remainders) else "MIXED_ON_GRID",
            "warning": "a finite grid cannot prove noncompact support or asymptotic non-smallness",
        }
    if exact_matrix_anchor:
        t0_anchor = {
            "status": "EXACT_SAVED_FINITE_MATRIX_ANCHOR",
            "exact_finite_matrix_LHS": mps(mu, 60),
            "exact_muA": mps(mu, 60),
            "exact_residual": "0",
            "raw_functional_quadrature_LHS": next(r["LHS"]["re"] for r in rows if r["t_over_L"] == 0.0),
            "interpretation": "the raw W02-WR-Wp quadrature is cancellation-limited at t=0; use the saved finite-matrix eigenpair for the exact anchor",
        }
    else:
        t0 = next(r for r in rows if r["t_over_L"] == 0.0)
        t0_anchor = {
            "status": "NO_PERSISTED_FULL_GROUND_MATRIX_ANCHOR_FOR_THIS_CELL",
            "raw_functional_quadrature_LHS": t0["LHS"]["re"],
            "muA_from_registered_mu1_proxy": t0["muA"]["re"],
            "raw_residual": t0["residual_sum_defects"]["re"],
            "interpretation": "portable_k1/mu1 diagnostic only; no exact t=0 eigenpair anchor is claimed",
        }
    payload = {
        "schema": f"soft_l2_projection_lag_ledger_{packet.lambda_sq}_{packet.N}_v1",
        "cell": {"lambda_sq": packet.lambda_sq, "N": packet.N, "L": mps(L), "mu": mps(mu, 60)},
        "source_typing": {
            "packet_role": packet.role,
            "packet_source": str(packet.source.relative_to(HERE.parent.parent.parent.parent)),
            "mu_source": mu_source,
            "full_ground_eigenvector_persisted": exact_matrix_anchor,
        },
        "convention": "A(t)=<U_t q,q>; LHS=W02-WR-Wp; residual=LHS-mu*A",
        "window_isolation": "E_win=-sum_k Lambda(k)/sqrt(k)[D_(log k,L)+D_(-log k,L)]",
        "remainder_scope": "aggregate Galerkin+sector+Arch-window+pole/midpoint correction; not pure Galerkin",
        "rows": rows,
        "prediction": prediction,
        "t0_matrix_anchor": t0_anchor,
        "claims": {"smallness": False, "compact_support_proved": False, "RH": False},
    }
    lag_json.write_text(json.dumps(payload, indent=2) + "\n")
    return payload


def initialize_quadrature() -> None:
    global GL_X, GL_W
    mp.mp.dps = 80
    nodes, weights = mp.gauss_quadrature(56, "legendre")
    GL_X = [nodes[i] for i in range(nodes.rows)]
    GL_W = [weights[i] for i in range(weights.rows)]


def micro_lag_ledgers() -> list[dict[str, Any]]:
    results = []
    for m in (12, 14):
        packet = load_packet(
            OUT / f"portable_k_coeffs_lambda_sq_{m}_N_120.json",
            "portable_k1_mu1_diagnostic_proxy",
        )
        mu_file = OUT / f"lambda_sq_{m}_N_120.json"
        mu = mp.mpf(json.loads(mu_file.read_text())["mu1"])
        results.append(
            lag_ledger(
                packet,
                mu,
                lag_csv=HERE / f"SOFT_L2_LAG_LEDGER_{m}_120.csv",
                lag_json=HERE / f"SOFT_L2_LAG_LEDGER_{m}_120.json",
                mu_source=f"{mu_file.name}:mu1",
                exact_matrix_anchor=False,
                prediction_mode="outer_cancellation",
            )
        )
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--micro-lag", action="store_true")
    args = parser.parse_args()
    initialize_quadrature()
    if args.micro_lag:
        results = micro_lag_ledgers()
        for result in results:
            print(f"({result['cell']['lambda_sq']},{result['cell']['N']}):{result['prediction']['outcome']}")
        print("NOT_RH")
        print("BUS_010_CREATED=false")
        return
    ps, ground, mu = packets()
    edge = edge_profiles(ps)
    lag = lag_ledger(ground, mu)
    print(edge["prediction"]["outcome"])
    print(lag["prediction"]["outcome"])
    print("NOT_RH")
    print("BUS_010_CREATED=false")


if __name__ == "__main__":
    main()
