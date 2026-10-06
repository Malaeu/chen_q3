#!/usr/bin/env python3
"""Finite signed even-tail diagnostic; numerical evidence only, never a proof.

For the original two-column plane span{G,G''}, form the *physical window*
residual r_j = 1_[-L/2,L/2] g_j - sum_{|n|<=m} c_n(g_j)(-1)^n e^(2 pi i n t/L)/sqrt(L).
Compute its full 2x2 L2 Gram E and the complete prime-power correlation matrix
P through q<=m from physical overlap integrals. One mixed entry is checked
against periodic correlation minus the reflected boundary term in equation
(30) of PROSHKA_SIGNED_EVEN_TAIL_INLINE.

The finite theta sum, quadrature, and eigensolve have no interval enclosure.
No numerical outcome here proves an eventual inequality or a tail statement.
"""
import argparse
import hashlib
import json
import math
import sys
import time
from functools import lru_cache
from pathlib import Path

sys.dont_write_bytecode = True

import mpmath as mp

ROOT = Path(__file__).resolve().parents[3]
SOURCE_DIR = ROOT / "docs/routeB_bus/fokas_k_sign_2026-09-25"
sys.path.insert(0, str(SOURCE_DIR))
import full_center_probe as fc  # noqa: E402

HERE = Path(__file__).resolve().parent
DEFAULT_OUT = HERE / "signed_tail_probe.json"


def s(x, digits=48):
    return mp.nstr(x, digits)


def theta_source(m, dps):
    """Reproduce full_center_probe.gaussian_plane's G and cutoff exactly.

    Analytic derivatives are used to avoid differentiating the theta sum at
    every quadrature node. Their formulas are checked against mp.diff below.
    """
    L = mp.log(m)
    b = L / 2
    cutoff = int(mp.ceil(mp.sqrt(m * (dps + 20) * mp.log(10) / mp.pi))) + 3

    def sum_poly(t, which):
        et = mp.exp(t)
        ehalf = mp.exp(t / 2)
        terms = []
        for r in range(1, cutoff + 1):
            x = mp.pi * (r * et) ** 2
            ex = mp.exp(-x)
            if which == 0:
                poly = 24 * x - 16 * x**2
            elif which == 1:
                poly = 60 * x - 120 * x**2 + 32 * x**3
            else:
                poly = 150 * x - 660 * x**2 + 448 * x**3 - 64 * x**4
            terms.append(ehalf * poly * ex)
        return mp.fsum(terms)

    def G(t):
        # full_center_probe uses the exact evenness of G and evaluates the
        # positive theta series on [0,L/2]. Reflect it here so truncation
        # roundoff cannot introduce an artificial odd component.
        return sum_poly(abs(t), 0)

    def Gprime(t):
        return mp.sign(t) * sum_poly(abs(t), 1)

    def Gsecond(t):
        return sum_poly(abs(t), 2)

    return L, b, cutoff, G, Gprime, Gsecond


def sample(m, dps, order):
    mp.mp.dps = dps
    started = time.monotonic()
    L, b, cutoff, G, Gprime, Gsecond = theta_source(m, dps)
    sqrtL = mp.sqrt(L)
    omega = lambda n: 2 * mp.pi * n / L

    # Composite fixed Gauss-Legendre quadrature makes the many related Gram
    # entries share cached physical residual evaluations. Max panel width .12
    # keeps the highest retained Fourier phase below 3 radians per panel.
    nodes0, weights0 = mp.gauss_quadrature(order, "legendre")
    nodes = [nodes0[i] for i in range(order)]
    weights = [weights0[i] for i in range(order)]
    max_width = min(mp.mpf("0.12"), mp.mpf(3) / abs(omega(m)))

    def panel_count(left, right):
        return max(1, int(mp.ceil(abs(right - left) / max_width)))

    def integrate(fun, left, right, panels=None):
        if right <= left:
            return mp.mpf(0)
        count = panels if panels is not None else panel_count(left, right)
        total = mp.mpf(0)
        for k in range(count):
            lo = left + (right - left) * k / count
            hi = left + (right - left) * (k + 1) / count
            mid = (lo + hi) / 2
            half = (hi - lo) / 2
            total += half * mp.fsum(
                weights[i] * fun(mid + half * nodes[i]) for i in range(order)
            )
        return total

    # Exact phase and normalization used by full_center_probe.gaussian_plane.
    positive_nodes = []
    positive_weights = []
    for k in range(panel_count(mp.mpf(0), b)):
        lo = b * k / panel_count(mp.mpf(0), b)
        hi = b * (k + 1) / panel_count(mp.mpf(0), b)
        mid = (lo + hi) / 2
        half = (hi - lo) / 2
        positive_nodes.extend(mid + half * x for x in nodes)
        positive_weights.extend(half * w for w in weights)
    c0 = []
    c2 = []
    endpoint_gp = Gprime(b)
    cosine_rows = [[mp.cos(omega(n) * t) for n in range(m + 1)] for t in positive_nodes]
    g_integrals = [mp.fsum(
        positive_weights[k] * G(positive_nodes[k]) * cosine_rows[k][n]
        for k in range(len(positive_nodes))
    ) for n in range(m + 1)]
    for n in range(m + 1):
        cn = (-1) ** n * 2 / sqrtL * g_integrals[n]
        c0.append(cn)
        c2.append(-omega(n) ** 2 * cn + 2 * endpoint_gp / sqrtL)

    coeffs = [c0, c2]

    def finite_synthesis(j, t):
        return (coeffs[j][0] + 2 * mp.fsum(
            (-1) ** n * coeffs[j][n] * mp.cos(omega(n) * t)
            for n in range(1, m + 1)
        )) / sqrtL

    @lru_cache(maxsize=100000)
    def residual_pair(t):
        g0 = G(t)
        g2 = Gsecond(t)
        return g0 - finite_synthesis(0, t), g2 - finite_synthesis(1, t)

    def residual(j, t):
        return residual_pair(t)[j]

    # Check the derivative recurrence and coefficient vectors against the
    # existing source function, projector, phase, and normalization.
    derivative_points = [b / 3, b]
    derivative_check = max(
        abs(Gprime(t) - mp.diff(G, t)) for t in derivative_points
    )
    derivative_check = max(
        derivative_check,
        *(abs(Gsecond(t) - mp.diff(G, t, 2)) for t in derivative_points),
    )
    plane_from_coefficients = mp.matrix([
        [coeffs[0][abs(n)], coeffs[1][abs(n)]] for n in range(-m, m + 1)
    ])
    gram_coeffs = plane_from_coefficients.T * plane_from_coefficients
    coeff_projector = plane_from_coefficients * mp.inverse(gram_coeffs) * plane_from_coefficients.T
    source_projector, endpoint_parity_error, source_cutoff = fc.gaussian_plane(m)
    projector_residual = mp.norm(coeff_projector - source_projector)

    # E is the Gram matrix of the actual zero-extended window residuals.
    # Exact evenness reduces integration to twice the positive half-window.
    E = mp.matrix(2, 2)
    projection_residuals = {}
    projection_integrals = [[mp.mpf(0) for _ in range(m + 1)] for _ in range(2)]
    for i in range(2):
        for j in range(i, 2):
            val = 2 * integrate(lambda t: residual(i, t) * residual(j, t), 0, b)
            E[i, j] = E[j, i] = mp.re(val)

    for n in (0, 1, m):
        for j in range(2):
            moment = integrate(
                lambda t, jj=j, nn=n: residual(jj, t) * mp.cos(omega(nn) * t),
                0, b,
            )
            projection_integrals[j][n] = (-1) ** n * 2 / sqrtL * moment
            projection_residuals[f"column_{j}_mode_{n}"] = s(projection_integrals[j][n])
    max_projection_residual = max(
        abs(projection_integrals[j][n]) for j in range(2) for n in (0, 1, m)
    )

    def direct_correlation(i, j, shift):
        # Physical overlap of the two zero-extended functions.
        return integrate(
            lambda t: residual(i, t) * residual(j, t + shift), -b, b - shift
        )

    def periodic_correlation(i, j, shift):
        # Integrate over one period with the actual wrap at the right edge.
        inner = integrate(
            lambda t: residual(i, t) * residual(j, t + shift),
            -b, b - shift,
        )
        wrapped = integrate(
            lambda t: residual(i, t) * residual(j, t + shift - L),
            b - shift, b,
        )
        return inner + wrapped

    def reflected_boundary(i, j, shift):
        # H_jk(s) = int_0^s r_j(b-u) r_k(b-(s-u)) du.
        return integrate(
            lambda u: residual(i, b - u) * residual(j, b - (shift - u)),
            mp.mpf(0), shift,
        )

    prime_powers = []
    for q in range(2, m + 1):
        p = next((d for d in range(2, int(math.isqrt(q)) + 1) if q % d == 0), q)
        quotient = q
        while quotient % p == 0:
            quotient //= p
        if quotient == 1:
            prime_powers.append((q, p, mp.log(p) / mp.sqrt(q)))

    Praw = mp.matrix(2, 2)
    correlation_rows = []
    for q, p, weight in prime_powers:
        shift = mp.log(q)
        qrow = {"q": q, "prime_base": p, "von_mangoldt_over_sqrt_q": s(weight)}
        for i in range(2):
            for j in range(2):
                corr = direct_correlation(i, j, shift)
                Praw[i, j] += 2 * weight * corr
                qrow[f"C_{i}{j}"] = s(corr)
        correlation_rows.append(qrow)

    # Verify one cross-correlation by a separately parameterized direct
    # physical overlap, rather than by periodic wrap minus reflection.
    check_q, check_i, check_j = 2, 0, 1
    check_shift = mp.log(check_q)
    check_direct = direct_correlation(check_i, check_j, check_shift)
    check_formula = (
        periodic_correlation(check_i, check_j, check_shift)
        - reflected_boundary(check_i, check_j, check_shift)
    )
    direct_check = {
        "q": check_q,
        "entry": f"{check_i}{check_j}",
        "direct_physical_integral": s(check_direct),
        "periodic_minus_reflected": s(check_formula),
        "absolute_difference": s(abs(check_direct - check_formula)),
        "interpretation": "Separate physical-overlap quadrature compared with the periodized/reflected identity; the periodized integral contains the same overlap region, so this is an algebraic consistency check, not an independent analytic method.",
    }

    # Evenness makes the exact cross entries equal. Retain the raw discrepancy
    # and use the Hermitian part for the generalized comparison.
    antisymmetry = max(abs(Praw[0, 1] - Praw[1, 0]), abs(Praw[1, 0] - Praw[0, 1]))
    P = (Praw + Praw.T) / 2
    evals_E = mp.eigsy(E, eigvals_only=True)
    chol = mp.cholesky(E)
    chol_inv = mp.inverse(chol)
    whitened = chol_inv * P * chol_inv.T
    whitened = (whitened + whitened.T) / 2
    lambdas, vecs = mp.eigsy(whitened)
    generalized = []
    for k in range(2):
        zvec = mp.inverse(chol.T) * vecs[:, k]
        znorm = mp.sqrt(mp.re((zvec.T * E * zvec)[0]))
        zvec /= znorm
        generalized.append({
            "eigenvalue": s(lambdas[k]),
            "E_normalized_direction_z0_z2": [s(zvec[0]), s(zvec[1])],
        })

    Omega = 2 * mp.pi * m / L
    # a(omega) = Re psi(1/4+i*omega/2)-psi(1/4), an exact
    # digamma form of the convergent beta_k series in equation (2).
    a_omega = mp.re(mp.digamma(mp.mpf(1) / 4 + 1j * Omega / 2)
                    - mp.digamma(mp.mpf(1) / 4))
    c_ar = mp.euler + mp.log(8 * mp.pi) + mp.pi / 2
    kappa = a_omega - c_ar
    threshold = kappa - 1
    max_eigenvalue = lambdas[1]
    d_gap = kappa - max_eigenvalue

    result = {
        "m": m,
        "dps": dps,
        "status": "FINITE_NUMERICAL_DIAGNOSTIC_ONLY_NOT_A_PROOF",
        "elapsed_seconds": s(time.monotonic() - started, 12),
        "theta_cutoff": cutoff,
        "full_center_probe_cutoff": source_cutoff,
        "source_G_sha256": hashlib.sha256((SOURCE_DIR / "full_center_probe.py").read_bytes()).hexdigest(),
        "window": {"L_log_m": s(L), "b_L_over_2": s(b), "Omega_2pi_m_over_L": s(Omega)},
        "source_and_convention_checks": {
            "analytic_derivative_vs_mp_diff_max_abs": s(derivative_check),
            "coefficient_plane_projector_vs_full_center_probe_max_norm": s(projector_residual),
            "theta_endpoint_parity_error_from_full_center_probe": s(endpoint_parity_error),
            "coefficient_convention": "psi_n(t)=(-1)^n exp(i omega_n t)/sqrt(L); c_n=<psi_n,g>; synthesis=sum c_n psi_n",
            "direct_projection_residuals_modes_0_1_m": projection_residuals,
            "max_direct_projection_residual_abs": s(max_projection_residual),
            "quadrature_order": order,
        },
        "E_actual_window_residual_gram": [[s(E[i, j]) for j in range(2)] for i in range(2)],
        "E_eigenvalues": [s(x) for x in evals_E],
        "E_determinant": s(mp.det(E)),
        "P_full_prime_power_correlation_gram": [[s(P[i, j]) for j in range(2)] for i in range(2)],
        "P_raw_cross_antisymmetry_abs": s(antisymmetry),
        "prime_power_terms_q_le_m": correlation_rows,
        "q_equals_m_zero_extension_correlation": {
            "q": m,
            "C_00": next((row["C_00"] for row in correlation_rows if row["q"] == m), "0"),
            "reason": "The overlap interval has zero length at shift log(m)=L; when m is a prime power this zero term is retained in the full sum.",
        },
        "independent_direct_correlation_check": direct_check,
        "generalized_eigenvalues_P_vs_E": generalized,
        "criterion_33": {
            "a_Omega": s(a_omega),
            "c_ar": s(c_ar),
            "kappa": s(kappa),
            "threshold_kappa_minus_1": s(threshold),
            "largest_generalized_eigenvalue": s(max_eigenvalue),
            "finite_cell_margin_threshold_minus_largest_eigenvalue": s(threshold - max_eigenvalue),
            "numerical_cell_test": "P <= (kappa-1)E" if max_eigenvalue <= threshold else "P <= (kappa-1)E FAILS AT THIS NUMERICAL CELL",
            "d_kappa_minus_largest_eigenvalue": s(d_gap),
            "weaker_finite_cell_test_P_le_kappa_E": "passes numerically at this cell" if d_gap >= 0 else "fails numerically at this cell",
            "scope": "Only the stronger sufficient criterion (33) at this finite m; says nothing about cofinal validity or the weaker budget-complete comparison (32).",
        },
        "limitations": [
            "Finite theta cutoff is copied from full_center_probe.gaussian_plane and is not accompanied here by a certified tail enclosure.",
            "mpmath quadrature and eigenvalues are floating-point diagnostics, not Arb intervals or a proof.",
            "Only m=8 is the requested initial cell; no asymptotic or cofinal conclusion follows.",
            "The positive reflected-image and pole terms in A_m, and the full budget comparison (32), are not tested by criterion (33).",
        ],
    }
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=8)
    parser.add_argument("--settings", nargs="+", default=["60:24", "60:32", "90:32"],
                        help="precision:Gauss-Legendre-order pairs")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    try:
        settings = [(int(pair.split(":", 1)[0]), int(pair.split(":", 1)[1]))
                    for pair in args.settings]
    except (ValueError, IndexError):
        parser.error("settings must use precision:order, for example 60:24")
    if args.m < 2 or any(dps < 60 or order < 16 for dps, order in settings):
        parser.error("require m >= 2, precision >= 60, and quadrature order >= 16")

    # Register the diagnostic's scope and expected discriminating capability
    # in the output before launching either numerical precision.
    payload = {
        "status": "DIAGNOSTIC_ONLY_NEVER_A_TAIL_PROOF",
        "prediction_before_run": (
            "At m=8 the full generalized spectrum P_m versus E_m can decide only whether the stronger finite-cell criterion (33) holds for every combination in the original span{G,G''}; its largest eigenvalue finds the most adverse mixed direction, which diagonal column checks can miss. The threshold is expected to be small, so the cell comparison is phase-sensitive. Failure at m=8 does not refute eventual (33), and passing m=8 does not establish it on an unbounded family."
        ),
        "definitions": {
            "E_m": "Gram matrix of r_j=1_[-L/2,L/2]g_j-f_j, where f_j is the actual finite Fourier synthesis of window coefficients and g=(G,G'').",
            "P_m": "2 sum_{q<=m} Lambda(q)/sqrt(q) times the Hermitian matrix of C_r(log q), including every prime power and the mixed terms.",
            "correlation_method": "P uses direct physical overlap integrals of the actual zero-extended residual for every q<=m; one mixed entry is checked against equation (30), retaining its reflected boundary Hankel integral.",
            "comparison": "lambda_max(E_m^{-1/2} P_m E_m^{-1/2}) <= kappa_m-1, the stronger sufficient criterion (33).",
        },
        "runs": [],
    }
    for dps, order in settings:
        print(f"signed_tail_probe: m={args.m}, dps={dps}, GL order={order}", flush=True)
        run = sample(args.m, dps, order)
        payload["runs"].append(run)
        print(json.dumps({
            "m": run["m"], "dps": run["dps"], "elapsed_seconds": run["elapsed_seconds"],
            "E": run["E_actual_window_residual_gram"],
            "P": run["P_full_prime_power_correlation_gram"],
            "generalized_eigenvalues": run["generalized_eigenvalues_P_vs_E"],
            "threshold": run["criterion_33"]["threshold_kappa_minus_1"],
            "margin": run["criterion_33"]["finite_cell_margin_threshold_minus_largest_eigenvalue"],
            "direct_check_error": run["independent_direct_correlation_check"]["absolute_difference"],
        }, indent=2), flush=True)

    if len(payload["runs"]) >= 2:
        payload["convergence_comparisons"] = []
        for low, high in zip(payload["runs"], payload["runs"][1:]):
            payload["convergence_comparisons"].append({
                "settings": [[low["dps"], low["source_and_convention_checks"]["quadrature_order"]],
                             [high["dps"], high["source_and_convention_checks"]["quadrature_order"]]],
                "largest_generalized_eigenvalue_matches_to_stored_significant_digits": (
                    low["generalized_eigenvalues_P_vs_E"][1]["eigenvalue"]
                    == high["generalized_eigenvalues_P_vs_E"][1]["eigenvalue"]
                ),
                "threshold_matches_to_stored_significant_digits": (
                    low["criterion_33"]["threshold_kappa_minus_1"]
                    == high["criterion_33"]["threshold_kappa_minus_1"]
                ),
                "E_entries_match_to_stored_significant_digits": (
                    low["E_actual_window_residual_gram"] == high["E_actual_window_residual_gram"]
                ),
                "P_entries_match_to_stored_significant_digits": (
                    low["P_full_prime_power_correlation_gram"]
                    == high["P_full_prime_power_correlation_gram"]
                ),
                "meaning": "Comparisons use exact equality of the stored 48-significant-digit strings. Numerical stability only; neither is a certified quadrature or theta-tail enclosure.",
            })

    args.output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {args.output}", flush=True)


if __name__ == "__main__":
    main()
