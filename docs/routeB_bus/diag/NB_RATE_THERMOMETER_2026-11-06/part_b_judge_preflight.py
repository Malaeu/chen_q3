#!/usr/bin/env python3
"""Preflight J3/J4/J5 without starting the 1e8 scientific run.

Run from the repository with:
    uv run --with mpmath python docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06/part_b_judge_preflight.py

J5's literal plant is evaluated from its convergent Dirichlet series.  The
centered companion is diagnostic only; it does not replace the registered J5
statistic or change its score.
"""
from __future__ import annotations

import csv
import json
import math
from pathlib import Path

import mpmath as mp


OUT = Path(__file__).resolve().parent
PUBLISHED_A084237 = [
    1, -1, 1, 2, -23, -48, 212, 1037, 1928, -222,
    -33722, -87856, 62366, 599582, -875575, -3216373,
    -3195437, -21830254, -46758740, 899990187,
]


def mobius_linear(nmax: int) -> list[int]:
    """Euler sieve, used only for the small J3/J4 preflight here."""
    mu = [0] * (nmax + 1)
    lp = [0] * (nmax + 1)
    primes: list[int] = []
    if nmax >= 1:
        mu[1] = 1
    for n in range(2, nmax + 1):
        if lp[n] == 0:
            lp[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p > lp[n] or n * p > nmax:
                break
            lp[n * p] = p
            if p == lp[n]:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]
    return mu


def kahan_sum(values) -> float:
    total = 0.0
    corr = 0.0
    for x in values:
        y = x - corr
        t = total + y
        corr = (t - total) - y
        total = t
    return total


def head_m1_and_coefficients(N: int, mu: list[int]) -> tuple[float, list[tuple[int, float]]]:
    """L6 exact-head coefficients; returned in the literal residue basis."""
    m1 = kahan_sum(mu[d] / d for d in range(1, N))
    coeffs = [(n, float(-mu[n])) for n in range(2, N)]
    coeffs.append((N, float(N * m1)))
    return m1, coeffs


def head_residual_k(N: int, k: int, mu: list[int], m1: float | None = None) -> float:
    """Evaluate 1-H_N(k) from an integer-floor identity (L6), all k>=1."""
    if m1 is None:
        m1, _ = head_m1_and_coefficients(N, mu)
    mobius_floor = sum(mu[n] * (k // n) for n in range(2, min(N - 1, k) + 1))
    return 1.0 - k - mobius_floor + N * m1 * (k // N)


def head_error_partial_interval(N: int, K: int, mu: list[int]) -> tuple[float, float]:
    """Partial head norm and rigorous omitted-tail bound from source L14.

    This returns [partial, partial+tail_bound], never labels the partial sum
    as the full E_N^h.  The source bound |R_N^h(k)|<=3N implies the explicit
    tail <= 9N^2/(K+1).  At large N this can be too crude to certify J2.
    """
    if K < N:
        raise ValueError("K must include the exact head endpoint N")
    m1, _ = head_m1_and_coefficients(N, mu)
    part = kahan_sum(head_residual_k(N, k, mu, m1) ** 2 / (k * (k + 1))
                     for k in range(N, K + 1))
    tail_bound = 9.0 * N * N / (K + 1)
    return part, tail_bound


def j3_head_check() -> dict:
    ns = [2, 3, 5, 10, 20, 50, 100, 200, 500]
    mu = mobius_linear(max(ns))
    rows = []
    for n in ns:
        # m_1(N-1) = sum_{d < N} mu(d)/d; source coefficients are
        # c_d=-mu(d), d<N, and c_N=N*m_1(N-1).
        m1, coeffs = head_m1_and_coefficients(n, mu)
        worst = 0.0
        worst_k = None
        for k in range(1, n):
            h = kahan_sum(c * ((k % d) / d) for d, c in coeffs)
            err = abs(h - 1.0)
            if err > worst:
                worst, worst_k = err, k
        rows.append({"N": n, "max_abs_H_minus_1": worst, "worst_k": worst_k,
                     "pass_1e-12": worst <= 1e-12})
    return {"status": "PASS" if all(x["pass_1e-12"] for x in rows) else "FAIL",
            "identity": "H_N(k)=1 for 1<=k<N; L6 coefficients",
            "checked_N": ns, "rows": rows}


def j4_small_check() -> dict:
    # The full scientific run will check every 10^j through 10^8.  This
    # preflight validates the indexing and sign convention against the first
    # published A084237 terms without doing that run.
    mu = mobius_linear(1000)
    running = 0
    values = {}
    targets = {10: PUBLISHED_A084237[1],
               100: PUBLISHED_A084237[2],
               1000: PUBLISHED_A084237[3]}
    for n in range(1, 1001):
        running += mu[n]
        if n in targets:
            values[n] = running
    checks = [{"x": n, "computed": values[n], "published": targets[n],
               "pass": values[n] == targets[n]} for n in targets]
    return {"status": "PASS" if all(x["pass"] for x in checks) else "FAIL",
            "source": "OEIS A084237, a(j)=M(10^j)",
            "scope": "preflight exponents j=1,2,3 only; full J4 awaits scientific run",
            "checks": checks}


def b1_exact_witness() -> dict:
    """Exact early counterexample to the preregistered all-N B1 bound."""
    # M(1)=1 and M(2)=0, so gamma(2)=1/2 and gamma(3)=1/2.
    rows = [
        {"N": 2, "M_values_used": [1], "gamma_exact": "1/2",
         "sqrtN_abs_gamma_exact": "sqrt(2)/2", "value": math.sqrt(2) / 2},
        {"N": 3, "M_values_used": [1, 0], "gamma_exact": "1/2",
         "sqrtN_abs_gamma_exact": "sqrt(3)/2", "value": math.sqrt(3) / 2},
    ]
    return {
        "prediction": "max_{N<=1e8} sqrt(N)*|gamma(N)| <= 0.6",
        "score": "MISS",
        "status": "EXACT_COUNTEREXAMPLE",
        "witnesses": rows,
        "reason": "Either exact witness exceeds 0.6; no claim about the actual maximum is made.",
    }


def plant_constant(j_terms: int = 48) -> tuple[mp.mpf, mp.mpf]:
    """Return unscaled C and the explicit geometric-series remainder bound.

    For k>=2, 1/(1+1/k)=sum_{j>=0}(-1)^j/k^j.  The k=1 term
    contributes 1/2.  Truncating after j_terms terms has absolute remainder
    at most zeta(1.2+j_terms)-1.  The actual planted gamma limit is 0.01*C.
    """
    mp.mp.dps = 70
    total = mp.mpf("0.5")
    for j in range(j_terms):
        term = mp.zeta(mp.mpf("1.2") + j - 14j) - 1
        total += term if j % 2 == 0 else -term
    bound = mp.zeta(mp.mpf("1.2") + j_terms) - 1
    return mp.re(total), bound


def centered_tail(N: int, j_terms: int = 5) -> tuple[mp.mpf, mp.mpf]:
    """Approximate sum_{k>=N} f(k), plus a rigorous absolute error bound.

    f(x)=x^0.8/[x(x+1)] exp(i*14 log x).  Euler's trapezoidal formula gives
    sum_{k>=N}f(k)=integral_N^inf f(x)dx+f(N)/2+R, with
    |R| <= (1/8) integral_N^inf |f''(x)| dx.  For x>=1 the latter is at
    most 13.3*N^-2.2.  The integral is expanded geometrically; after J terms
    its remainder is at most N^(-0.2-J)/(0.2+J).
    """
    x = mp.mpf(N)
    omega = mp.mpf(14)
    integral = mp.mpc(0)
    for j in range(j_terms):
        alpha = mp.mpf("0.2") + j
        integral += (-1) ** j * mp.power(x, -alpha + 1j * omega) / (alpha - 1j * omega)
    f_at_n = mp.power(x, mp.mpf("-1.2") + 1j * omega) / (1 + 1 / x)
    approx = mp.re(integral + f_at_n / 2)
    integral_error = mp.power(x, -mp.mpf("0.2") - j_terms) / (mp.mpf("0.2") + j_terms)
    # |f''| <= 232.8*x^-3.2, and 232.8/(8*2.2) < 13.23.
    trapezoid_error = mp.mpf("13.23") * mp.power(x, mp.mpf("-2.2"))
    return approx, integral_error + trapezoid_error


def linear_slope(xs: list[float], ys: list[float]) -> float:
    lx = [math.log(x) for x in xs]
    ly = [math.log(max(y, 1e-300)) for y in ys]
    mx = sum(lx) / len(lx)
    my = sum(ly) / len(ly)
    return sum((x - mx) * (y - my) for x, y in zip(lx, ly)) / sum((x - mx) ** 2 for x in lx)


def write_svg(rows: list[dict], path: Path) -> None:
    """Small dependency-free log-log plot for the literal and centered plants."""
    W, H = 920, 600
    left, right, top, bottom = 95, 35, 45, 85
    xs = [float(r["N"]) for r in rows]
    series = [
        ("literal |sqrt(N) gamma_plant|", [float(r["literal_root_abs"]) for r in rows], "#b43c3c"),
        ("centered |sqrt(N)(gamma_plant-C)|", [float(r["centered_root_abs"]) for r in rows], "#246b8e"),
        ("centered N^0.3 amplitude envelope", [float(r["envelope"]) for r in rows], "#568b51"),
    ]
    lx0, lx1 = math.log10(min(xs)), math.log10(max(xs))
    vals = [y for _, ys, _ in series for y in ys if math.isfinite(y) and y > 0]
    ly0, ly1 = math.log10(min(vals)) - 0.15, math.log10(max(vals)) + 0.15
    plot_w, plot_h = W - left - right, H - top - bottom
    def xy(x, y):
        return (left + (math.log10(x) - lx0) / (lx1 - lx0) * plot_w,
                top + (ly1 - math.log10(max(y, 1e-300))) / (ly1 - ly0) * plot_h)
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
           '<rect width="100%" height="100%" fill="white"/>',
           '<text x="460" y="25" text-anchor="middle" font-family="sans-serif" font-size="18">J5 literal plant and centered companion (log-log)</text>']
    for decade in range(int(lx0), int(lx1) + 1):
        x = 10 ** decade
        px, _ = xy(x, 10 ** ly0)
        out.append(f'<line x1="{px:.2f}" y1="{top}" x2="{px:.2f}" y2="{top+plot_h}" stroke="#ddd"/>')
        out.append(f'<text x="{px:.2f}" y="{top+plot_h+24}" text-anchor="middle" font-family="sans-serif" font-size="12">10^{decade}</text>')
    for decade in range(math.floor(ly0), math.ceil(ly1) + 1):
        y = 10 ** decade
        _, py = xy(10 ** lx0, y)
        out.append(f'<line x1="{left}" y1="{py:.2f}" x2="{left+plot_w}" y2="{py:.2f}" stroke="#ddd"/>')
        out.append(f'<text x="{left-12}" y="{py+4:.2f}" text-anchor="end" font-family="sans-serif" font-size="12">10^{decade}</text>')
    for name, ys, color in series:
        points = [xy(x, y) for x, y in zip(xs, ys)]
        out.append(f'<polyline fill="none" stroke="{color}" stroke-width="2" points="' + " ".join(f"{a:.2f},{b:.2f}" for a, b in points) + '"/>')
    out.extend([f'<line x1="{left}" y1="{top}" x2="{left}" y2="{top+plot_h}" stroke="#333"/>',
                f'<line x1="{left}" y1="{top+plot_h}" x2="{left+plot_w}" y2="{top+plot_h}" stroke="#333"/>',
                '<text x="460" y="575" text-anchor="middle" font-family="sans-serif" font-size="14">N</text>',
                '<text x="20" y="300" transform="rotate(-90 20 300)" text-anchor="middle" font-family="sans-serif" font-size="14">absolute scaled value</text>'])
    for idx, (name, _, color) in enumerate(series):
        y = 50 + idx * 22
        out.append(f'<line x1="570" y1="{y}" x2="600" y2="{y}" stroke="{color}" stroke-width="3"/>')
        out.append(f'<text x="608" y="{y+4}" font-family="sans-serif" font-size="12">{name}</text>')
    out.append('</svg>')
    path.write_text("\n".join(out) + "\n", encoding="utf-8")


def j5_preflight() -> dict:
    C, C_bound = plant_constant(64)
    ns = sorted({round(10 ** (6 + 2 * i / 200)) for i in range(201)})
    scale = mp.mpf("0.01")
    rows = []
    for N in ns:
        tail, tail_bound = centered_tail(N)
        gamma_prefix = scale * (C - tail)
        centered = -scale * tail
        envelope = scale / mp.sqrt(mp.mpf("0.2") ** 2 + 14 ** 2) * mp.power(N, mp.mpf("0.3"))
        rows.append({
            "N": N,
            "plant_gamma_prefix": mp.nstr(gamma_prefix, 30),
            "plant_gamma_prefix_abs_error_bound": mp.nstr(scale * (C_bound + tail_bound), 8),
            "literal_root_abs": mp.nstr(mp.sqrt(N) * abs(gamma_prefix), 30),
            "centered_gamma": mp.nstr(centered, 30),
            "centered_gamma_abs_error_bound": mp.nstr(scale * tail_bound, 8),
            "centered_root_abs": mp.nstr(mp.sqrt(N) * abs(centered), 30),
            "envelope": mp.nstr(envelope, 30),
            "centered_root_signed": mp.nstr(mp.sqrt(N) * centered, 30),
        })
    csv_path = OUT / "part_b_j5_centered.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator="\n")
        w.writeheader()
        w.writerows(rows)
    write_svg(rows, OUT / "part_b_j5_preflight.svg")
    xs = [float(r["N"]) for r in rows]
    literal_slope = linear_slope(xs, [float(r["literal_root_abs"]) for r in rows])
    centered_actual_slope = linear_slope(xs, [float(r["centered_root_abs"]) for r in rows])
    env_slope = linear_slope(xs, [float(r["envelope"]) for r in rows])
    plot_metadata = {
        "artifact": "part_b_j5_preflight.svg",
        "plot_type": "log-log line plot",
        "x_range": [1000000, 100000000],
        "sample_count": len(rows),
        "series": [
            {"name": "literal |sqrt(N) gamma_plant|", "color": "#b43c3c",
             "slope": literal_slope},
            {"name": "centered |sqrt(N)(gamma_plant-C)|", "color": "#246b8e",
             "slope": centered_actual_slope},
            {"name": "centered N^0.3 amplitude envelope", "color": "#568b51",
             "slope": env_slope},
        ],
        "input_data": "part_b_j5_centered.csv",
        "tail_bounds_in_csv": True,
    }
    (OUT / "part_b_j5_plot_metadata.json").write_text(json.dumps(plot_metadata, indent=2) + "\n", encoding="utf-8")
    return {
        "literal_J5": {
            "status": "FAIL" if abs(literal_slope - 0.3) > 0.1 else "PASS",
            "plant_limit_C_before_factor_0.01": mp.nstr(C, 40),
            "plant_limit_after_factor_0.01": mp.nstr(scale * C, 40),
            "series_truncation_terms": 64,
            "unscaled_series_remainder_bound": mp.nstr(C_bound, 12),
            "log_log_regression_slope_1e6_to_1e8": literal_slope,
            "interpretation": "nonzero constant offset makes the literal root statistic grow with exponent 1/2",
        },
        "centered_companion": {
            "status": "DIAGNOSTIC_ONLY_NOT_J5",
            "log_log_slope_of_actual_absolute_samples": centered_actual_slope,
            "log_log_slope_of_N_0_3_amplitude_envelope": env_slope,
            "expected_envelope_slope": 0.3,
            "tail_method": "Euler trapezoid plus geometric integral expansion; explicit pointwise remainder bounds in CSV",
            "point_count": len(rows),
        },
        "source_formula": "literal delta_gamma(N)=0.01 sum_{k<N} k^0.8 cos(14 log k)/[k(k+1)]",
        "score_rule": "A centered companion cannot change literal J5; judge failure means official Part B run is void/inconclusive.",
        "plot_metadata": plot_metadata,
    }


def main() -> None:
    j3 = j3_head_check()
    j4 = j4_small_check()
    b1 = b1_exact_witness()
    j5 = j5_preflight()
    result = {
        "run_status": "PREFLIGHT_ONLY_NO_1E8_SCIENTIFIC_RUN",
        "overall_part_b_status": "INCONCLUSIVE",
        "overall_reason": "The literal J5 plant has a nonzero limiting offset and slope 1/2, not its required approximately 0.3; the scientific run is void under the preregistered judge gate.",
        "J3_head": j3,
        "J4_reference": j4,
        "B1_prediction": b1,
        "B2_prediction": {"score": "NOT_RUN", "reason": "Full E_N^h grid and exact tail were not computed."},
        "B3_prediction": {
            "score": "SPLIT",
            "visible_growth_component": "HIT: literal plant-only root statistic has clear N^0.5 growth",
            "registered_approximately_0_3_slope_component": "MISS: literal measured slope is 0.4997859",
            "registered_J5_validation": "INCONCLUSIVE: scientific run void under failed J5 judge",
            "centered_companion": "diagnostic only; its envelope has slope 0.3 and does not repair the literal control",
        },
        "J5": j5,
    }
    (OUT / "part_b_judge_preflight.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    log = (
        "COMMAND: uv run --with mpmath python docs/routeB_bus/diag/NB_RATE_THERMOMETER_2026-11-06/part_b_judge_preflight.py\n"
        "SCOPE: preflight only; no 1e8 scientific run\n"
        f"OVERALL_PART_B: {result['overall_part_b_status']}\n"
        f"J3_HEAD: {j3['status']} (max checked error {max(x['max_abs_H_minus_1'] for x in j3['rows']):.4g})\n"
        f"J4_SMALL_REFERENCE: {j4['status']} (10, 100, 1000)\n"
        f"B1: {b1['score']} (N=2 value sqrt(2)/2={math.sqrt(2)/2:.12f})\n"
        "B2: NOT_RUN (full E_N^h grid/tail absent)\n"
        f"J5_LITERAL: FAIL (slope {j5['literal_J5']['log_log_regression_slope_1e6_to_1e8']:.12f}, expected about 0.3)\n"
        f"J5_CENTERED_ENVELOPE_SLOPE: {j5['centered_companion']['log_log_slope_of_N_0_3_amplitude_envelope']:.12f}\n"
        "B3: visible-growth HIT; requested 0.3-slope MISS; registered control validation INCONCLUSIVE\n"
    )
    (OUT / "part_b_preflight_run.log").write_text(log, encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
