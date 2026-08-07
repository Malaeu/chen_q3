#!/usr/bin/env python3
"""Rigorous Phase-1 CCM penalty certificate for the fixed (m, N) = (13, 120) cell.

The matrix is rebuilt with Arb balls from the source-side CCM formulas.  The
probe is the exact rational J-even projection of the pinned prolate packet,
followed by algebraic Euclidean normalization.  Positive semidefiniteness is
certified by interval LDL^T in the exact even/odd parity decomposition.

This script deliberately does not optimize beta or tau:

    beta = 10^-56,  tau = 1.

Both values are precommitted control values, not fitted spectral data.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import acb, arb, arb_mat, ctx


REPO = Path(__file__).resolve().parents[3]
Q_SOURCE = REPO / (
    "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/"
    "out/portable_k_coeffs_lambda_sq_13_N_120.json"
)
EXPECTED_Q_SHA256 = "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88"

M = 13
N = 120
BETA = Fraction(1, 10**56)
TAU = Fraction(1, 1)
PRIME_POWERS = ((2, 2), (3, 3), (4, 2), (5, 5), (7, 7), (8, 2), (9, 3), (11, 11), (13, 13))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_arb(value: Fraction) -> arb:
    return arb(value.numerator) / value.denominator


def bounds(value: arb) -> dict[str, str]:
    return {"ball": str(value), "lower": str(value.lower()), "upper": str(value.upper())}


def q_source_exact_even() -> tuple[list[Fraction], dict[str, Any]]:
    actual_sha = sha256(Q_SOURCE)
    if actual_sha != EXPECTED_Q_SHA256:
        raise SystemExit(f"q source SHA mismatch: {actual_sha}")
    payload = json.loads(Q_SOURCE.read_text(encoding="utf-8"))
    if payload.get("lambda_sq") != M or payload.get("N") != N or payload.get("logical_vector") != "k1":
        raise SystemExit("q source object mismatch")
    rows = payload["coefficients"]
    if [row["n"] for row in rows] != list(range(-N, N + 1)):
        raise SystemExit("q source mode ordering mismatch")

    real = {row["n"]: Fraction(row["re"]) for row in rows}
    imag = {row["n"]: Fraction(row["im"]) for row in rows}
    projected = [(real[n] + real[-n]) / 2 for n in range(-N, N + 1)]
    if any(projected[n + N] != projected[-n + N] for n in range(-N, N + 1)):
        raise SystemExit("exact J-even projection failed")
    norm_sq = sum((x * x for x in projected), Fraction(0))
    if norm_sq <= 0:
        raise SystemExit("projected q is zero")

    max_real_asymmetry = max(abs(real[n] - real[-n]) for n in range(-N, N + 1))
    max_conjugacy_error = max(abs(imag[n] + imag[-n]) for n in range(-N, N + 1))
    discarded_imag_norm_sq = sum((x * x for x in imag.values()), Fraction(0))
    return projected, {
        "source": str(Q_SOURCE.relative_to(REPO)),
        "sha256": actual_sha,
        "construction": "exact_decimal_rationals_then_(q+Jq)/2_then_Euclidean_normalize",
        "J_even_by_construction": True,
        "nonzero": True,
        "projected_norm_sq_exact_numerator_digits": len(str(abs(norm_sq.numerator))),
        "projected_norm_sq_exact_denominator_digits": len(str(norm_sq.denominator)),
        "max_real_J_asymmetry_before_projection": str(exact_arb(max_real_asymmetry)),
        "max_conjugacy_error_before_projection": str(exact_arb(max_conjugacy_error)),
        "discarded_imag_norm_sq": str(exact_arb(discarded_imag_norm_sq)),
    }


class CCMArbBuilder:
    def __init__(self) -> None:
        self.pi = arb.pi()
        self.L = arb(M).log()
        self.z = arb(1) / (M * M)
        self.exp_minus_L_over_2 = arb(1) / arb(M).sqrt()
        self.I = acb(0, 1)
        self.exp_correction = self._exp_correction()
        self.constant = (
            arb.const_euler() + (4 * self.pi * (M - 1) / (M + 1)).log()
        ) / 2
        self.alpha = {n: self._alpha(n) for n in range(N + 1)}
        self.beta = {n: self._beta(n) for n in range(N + 1)}
        self.gamma = {n: self._gamma(n) for n in range(N + 1)}
        self.log_prime = {p: arb(p).log() for _, p in PRIME_POWERS}
        self.log_k = {k: arb(k).log() for k, _ in PRIME_POWERS}

    def _alpha(self, n: int) -> arb:
        if n == 0:
            return arb(0)
        a = acb(arb(1) / 4, self.pi * n / self.L)
        hyp = acb(self.z).hypgeom_2f1(1, a, a + 1)
        term = (2 * self.L / (self.L + 4 * self.pi * self.I * n)) * hyp
        return (self.exp_minus_L_over_2 * term.imag + a.digamma().imag / 2) / self.pi

    def _beta(self, n: int) -> arb:
        if n == 0:
            # x*rho(x) = exp(x/2)/(2*sinc(i*x)); this removes the endpoint singularity.
            integrand = lambda x, _analytic: (x / 2).exp() / (2 * (self.I * x).sinc())
            value = acb.integral(
                integrand,
                0,
                self.L,
                rel_tol=arb(10) ** (-(ctx.dps - 10)),
                abs_tol=arb(10) ** (-(ctx.dps - 10)),
            )
            return value.real / self.L
        a = acb(arb(1) / 4, self.pi * n / self.L)
        hyp = acb(self.z).hypgeom_2f1(1, a, a + 1)
        term1 = -self.L * self.exp_minus_L_over_2 * (
            (2 * self.L / (4 * self.pi * n - self.I * self.L)) * hyp
        ).imag
        term2 = -self.exp_minus_L_over_2 * acb(self.z).lerch_phi(2, a).real / 4
        term3 = a.polygamma(1).real / 4
        return (term1 + term2 + term3) / self.L

    def _cos_minus_one(self, n: int) -> arb:
        if n == 0:
            return arb(0)
        a = acb(arb(1) / 4, self.pi * n / self.L)
        hyp = acb(self.z).hypgeom_2f1(1, a, a + 1)
        h0 = self.z.hypgeom_2f1(arb(1) / 4, 1, arb(5) / 4)
        term1 = -self.exp_minus_L_over_2 * (
            (2 * self.L / (self.L + 4 * self.pi * self.I * n)) * hyp
        ).real
        term2 = 2 * self.exp_minus_L_over_2 * h0
        term3 = -(a.digamma().real - arb(arb(1) / 4).digamma()) / 2
        return term1 + term2 + term3

    def _exp_correction(self) -> arb:
        # (1-exp(-x/2))*rho(x) = exp(x)/((exp(x/2)+1)*(exp(x)+1)).
        integrand = lambda x, _analytic: x.exp() / (((x / 2).exp() + 1) * (x.exp() + 1))
        return acb.integral(
            integrand,
            0,
            self.L,
            rel_tol=arb(10) ** (-(ctx.dps - 10)),
            abs_tol=arb(10) ** (-(ctx.dps - 10)),
        ).real

    def _gamma(self, n: int) -> arb:
        return self._cos_minus_one(n) + self.exp_correction + self.constant

    def q_nm(self, n: int, m: int, y: arb) -> arb:
        if n == m:
            return 2 * (1 - y / self.L) * (2 * self.pi * n * y / self.L).cos()
        return (
            (2 * self.pi * m * y / self.L).sin()
            - (2 * self.pi * n * y / self.L).sin()
        ) / (self.pi * (n - m))

    def w02(self, n: int, m: int) -> arb:
        return (
            32
            * self.L
            * (self.L / 4).sinh() ** 2
            * (self.L**2 - 16 * self.pi**2 * m * n)
            / (
                (self.L**2 + 16 * self.pi**2 * m * m)
                * (self.L**2 + 16 * self.pi**2 * n * n)
            )
        )

    def wr(self, n: int, m: int) -> arb:
        if n == m:
            k = abs(n)
            return 2 * self.gamma[k] - 2 * self.beta[k]
        alpha_n = self.alpha[abs(n)] if n >= 0 else -self.alpha[abs(n)]
        alpha_m = self.alpha[abs(m)] if m >= 0 else -self.alpha[abs(m)]
        return (alpha_m - alpha_n) / (n - m)

    def prime(self, n: int, m: int) -> arb:
        total = arb(0)
        for k, p in PRIME_POWERS:
            total += self.log_prime[p] / arb(k).sqrt() * self.q_nm(n, m, self.log_k[k])
        return total

    def tau_entry(self, n: int, m: int) -> arb:
        return self.w02(n, m) - self.wr(n, m) - self.prime(n, m)

    def parity_blocks(self) -> tuple[arb_mat, arb_mat, dict[str, dict[str, str]]]:
        even = arb_mat(N + 1, N + 1)
        odd = arb_mat(N, N)
        sqrt2 = arb(2).sqrt()
        cache: dict[tuple[int, int], arb] = {}

        def k(i: int, j: int) -> arb:
            key = (i, j) if i <= j else (j, i)
            if key not in cache:
                cache[key] = self.tau_entry(*key)
            return cache[key]

        even[0, 0] = k(0, 0)
        for j in range(1, N + 1):
            value = sqrt2 * k(0, j)
            even[0, j] = value
            even[j, 0] = value
        for i in range(1, N + 1):
            for j in range(i, N + 1):
                even_value = k(i, j) + k(i, -j)
                odd_value = k(i, j) - k(i, -j)
                even[i, j] = even_value
                even[j, i] = even_value
                odd[i - 1, j - 1] = odd_value
                odd[j - 1, i - 1] = odd_value
        samples = {
            "K_0_0": bounds(k(0, 0)),
            "K_1_2": bounds(k(1, 2)),
            "K_2_minus_1": bounds(k(2, -1)),
            "K_3_3": bounds(k(3, 3)),
        }
        return even, odd, samples


def interval_ldlt(matrix: arb_mat) -> dict[str, Any]:
    n = matrix.nrows()
    lower = [[arb(0) for _ in range(n)] for __ in range(n)]
    pivots: list[arb] = []
    for i in range(n):
        for j in range(i):
            previous = sum((lower[i][k] * lower[j][k] * pivots[k] for k in range(j)), arb(0))
            lower[i][j] = (matrix[i, j] - previous) / pivots[j]
        previous = sum((lower[i][k] ** 2 * pivots[k] for k in range(i)), arb(0))
        pivot = matrix[i, i] - previous
        pivots.append(pivot)
        if not pivot.is_finite() or not pivot.lower() > 0:
            sign_status = "INSUFFICIENT_PRECISION" if pivot.upper() > 0 else "NONPOSITIVE_PIVOT"
            return {
                "pass": False,
                "status": sign_status,
                "dimension": n,
                "failed_pivot_index": i,
                "failed_pivot": bounds(pivot),
                "positive_pivots_before_failure": i,
            }
        lower[i][i] = arb(1)
    minimum = min(pivots, key=lambda x: float(x.lower()))
    maximum = max(pivots, key=lambda x: float(x.upper()))
    return {
        "pass": True,
        "status": "INTERVAL_POSITIVE_DEFINITE",
        "dimension": n,
        "positive_pivot_count": n,
        "minimum_pivot": bounds(minimum),
        "maximum_pivot": bounds(maximum),
    }


def run_precision(dps: int, projected: list[Fraction]) -> dict[str, Any]:
    ctx.dps = dps
    ctx.threads = 1
    started = time.time()
    builder = CCMArbBuilder()
    even, odd, samples = builder.parity_blocks()

    norm_sq_exact = sum((x * x for x in projected), Fraction(0))
    norm = exact_arb(norm_sq_exact).sqrt()
    sqrt2 = arb(2).sqrt()
    q_even = [exact_arb(projected[N]) / norm]
    q_even.extend(sqrt2 * exact_arb(projected[N + i]) / norm for i in range(1, N + 1))
    q_norm_sq = sum((x * x for x in q_even), arb(0))

    kq = []
    for i in range(N + 1):
        kq.append(sum((even[i, j] * q_even[j] for j in range(N + 1)), arb(0)))
    a = sum((q_even[i] * kq[i] for i in range(N + 1)), arb(0))

    beta = exact_arb(BETA)
    tau = exact_arb(TAU)
    for i in range(N + 1):
        for j in range(i, N + 1):
            value = even[i, j] + tau * q_even[i] * q_even[j]
            if i == j:
                value -= beta
            even[i, j] = value
            even[j, i] = value
    for i in range(N):
        odd[i, i] -= beta

    even_ldlt = interval_ldlt(even)
    odd_ldlt = interval_ldlt(odd)
    beta_gt_a = beta > a.upper()
    passed = bool(beta_gt_a and even_ldlt["pass"] and odd_ldlt["pass"])
    return {
        "dps": dps,
        "elapsed_seconds": time.time() - started,
        "arb_version": __import__("flint").__version__,
        "L_equals_log_m": bounds(builder.L),
        "q_norm_sq": bounds(q_norm_sq),
        "a_q_star_K_q": bounds(a),
        "beta": str(beta),
        "tau": str(tau),
        "beta_minus_a": bounds(beta - a),
        "beta_strictly_greater_than_a": bool(beta_gt_a),
        "matrix_entry_samples": samples,
        "even_penalty_ldlt": even_ldlt,
        "odd_unpenalized_ldlt": odd_ldlt,
        "interval_psd_pass": passed,
    }


def intervals_overlap(first: dict[str, str], second: dict[str, str]) -> bool:
    # Reparse the reported balls at the current high precision.  Overlap is a
    # consistency check only; each individual LDL result is already rigorous.
    return arb(first["ball"]).overlaps(arb(second["ball"]))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", nargs=2, type=int, default=(120, 240), metavar=("LOW", "HIGH"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    low_dps, high_dps = args.dps
    if low_dps < 90 or high_dps < 2 * low_dps:
        raise SystemExit("precision contract requires LOW >= 90 and HIGH >= 2*LOW")

    projected, q_meta = q_source_exact_even()
    runs = [run_precision(low_dps, projected), run_precision(high_dps, projected)]
    consistency = {
        "a_intervals_overlap": intervals_overlap(runs[0]["a_q_star_K_q"], runs[1]["a_q_star_K_q"]),
        "beta_minus_a_intervals_overlap": intervals_overlap(runs[0]["beta_minus_a"], runs[1]["beta_minus_a"]),
        "sample_intervals_overlap": all(
            intervals_overlap(runs[0]["matrix_entry_samples"][key], runs[1]["matrix_entry_samples"][key])
            for key in runs[0]["matrix_entry_samples"]
        ),
    }
    # The doubled-precision run is the rigorous certificate.  The lower run is
    # a precision-sensitivity witness and is allowed to return an interval
    # containing zero; demanding two successful certificates would defeat the
    # purpose of precision doubling.  Cross-precision source quantities must
    # nevertheless remain consistent.
    interval_pass = runs[-1]["interval_psd_pass"] and all(consistency.values())
    verdict = (
        "CCM_CONTROL_CELL_CERT_INTERVAL_PASS"
        if interval_pass
        else "CCM_CONTROL_CELL_NUMERICALLY_INCONCLUSIVE"
    )
    result = {
        "schema": "CCMControlCellPenaltyIntervalCertificate.v1",
        "verdict": verdict,
        "route": "CHALLENGER_NOT_RH",
        "promotion": "FORBIDDEN",
        "control_cell": {"m": M, "lambda": "sqrt(13)", "N": N, "dimension": 2 * N + 1},
        "matrix_orientation": "K=W_0_2-W_R-W_prime; G=I; J=mode_reversal",
        "q": q_meta,
        "parameters": {
            "beta_exact": f"{BETA.numerator}/{BETA.denominator}",
            "tau_exact": f"{TAU.numerator}/{TAU.denominator}",
            "selection": "precommitted_decade_and_unit_penalty; no_fit; no_optimization",
        },
        "precision_doubling": runs,
        "cross_precision_consistency": consistency,
        "interval_psd_certified": interval_pass,
        "semantic_boundary": "finite_CCM_control_cell_only; not_SlotH2a; not_uniform_gap; not_RH",
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        output = args.output if args.output.is_absolute() else REPO / args.output
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0 if interval_pass else 2


if __name__ == "__main__":
    raise SystemExit(main())
