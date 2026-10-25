"""High-precision noninterval recheck of the two saved Q16 direct sums.

Uses mpmath decimal precision at dps=80 and dps=160.  The direct sum is
computed from the full original Q_n matrix and every nonzero Lambda(n),
including prime powers.  Packet contact moments are evaluated analytically as
piecewise polynomial-exponential integrals; no packet quadrature is used.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import mpmath as mp

ROOT = Path("/Users/emalam/GitHub/rh_lean_01_2026")
INPUT = ROOT / "docs/literature/openai_math_2026-10-07/q16_verdict_checks/diagnostic_results.json"
OUTPUT = Path("/tmp/ccm_q16_precision_recheck.json")
SCRIPT = Path(__file__)


def mpstr(x, dps):
    return mp.nstr(x, n=dps, strip_zeros=False)


def prime_power(n: int):
    """Return (p, exponent) iff n is a positive power of one prime."""
    value = n
    factors = []
    p = 2
    while p * p <= value:
        if value % p == 0:
            exponent = 0
            while value % p == 0:
                value //= p
                exponent += 1
            factors.append((p, exponent))
        p += 1
    if value > 1:
        factors.append((value, 1))
    return factors[0] if len(factors) == 1 else None


def max_abs_matrix(mat):
    return max(abs(mat[i, j]) for i in range(mat.rows) for j in range(mat.cols))


def qn_matrix(omegas, js, s, L):
    """Literal Q_n entry formula from diagnostic_q16.py, with all entries."""
    size = len(js)
    qn = mp.matrix(size, size)
    for i, ji in enumerate(js):
        for k, jk in enumerate(js):
            if ji == jk:
                qn[i, k] = 2 * (1 - s / L) * mp.cos(omegas[i] * s)
            else:
                qn[i, k] = (
                    mp.sin(omegas[k] * s) - mp.sin(omegas[i] * s)
                ) / (mp.pi * (ji - jk))
    return qn


def exp_monomial_integrals(alpha, upper, max_degree):
    """I_k = integral_0^upper x^k exp(alpha*x) dx via exact recurrence."""
    result = []
    eupper = mp.exp(alpha * upper)
    ezero = mp.mpf(1)
    result.append((eupper - ezero) / alpha)
    for k in range(1, max_degree + 1):
        result.append((upper**k * eupper) / alpha - (k / alpha) * result[k - 1])
    return result


def poly_exp_integral(coeffs, alpha, upper):
    integrals = exp_monomial_integrals(alpha, upper, len(coeffs) - 1)
    return sum(coeffs[k] * integrals[k] for k in range(len(coeffs)))


def add_scaled_poly(target, poly, scale):
    for k, value in enumerate(poly):
        target[k] += scale * value


def packet_contacts(c, dh, omegas, L, ell, J, dps):
    """Compute max_j |int_0^L exp(+-t/2) packet_j(t) dt| analytically."""
    count = J + 1
    sqrtL = mp.sqrt(L)
    r = [mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(10), mp.mpf(-15), mp.mpf(6)]
    rp = [mp.mpf(0), mp.mpf(0), 30 / ell, -60 / ell, 30 / ell]
    rpp = [mp.mpf(0), 60 / ell**2, -180 / ell**2, 120 / ell**2]
    one_minus_r = [-value for value in r]
    one_minus_r[0] += 1
    results = {}

    for sign in (-1, 1):
        moments = [mp.mpc(0) for _ in range(count)]
        sigma = mp.mpf(sign) / 2
        for segment in range(J):
            t0 = segment * ell
            t1 = min((segment + 1) * ell, L)
            if t1 <= t0:
                continue
            upper_x = (t1 - t0) / ell
            for freq_index, omega in enumerate(omegas):
                exponent = mp.mpc(sigma, omega)
                alpha = ell * exponent
                base = mp.exp(exponent * t0) / sqrtL
                c_j = c[freq_index]
                dh_j = dh[freq_index]
                hp_j = mp.j * omega * dh_j

                left = [mp.mpc(0) for _ in range(6)]
                right = [mp.mpc(0) for _ in range(6)]
                add_scaled_poly(left, one_minus_r, c_j)
                add_scaled_poly(left, rp, -2 * hp_j)
                add_scaled_poly(left, rpp, -dh_j)
                add_scaled_poly(right, r, c_j)
                add_scaled_poly(right, rp, 2 * hp_j)
                add_scaled_poly(right, rpp, dh_j)

                prefactor = ell * base
                moments[segment] += prefactor * poly_exp_integral(left, alpha, upper_x)
                moments[segment + 1] += prefactor * poly_exp_integral(right, alpha, upper_x)
        results[str(sign)] = {
            "max_abs_contact": mpstr(max(abs(value) for value in moments), dps),
            "per_packet_abs_contacts": [mpstr(abs(value), dps) for value in moments],
        }
    return results


def packet_value(t, c, dh, omegas, L, ell, J):
    count = J + 1
    result = [mp.mpc(0) for _ in range(count)]
    if t < 0 or t > L:
        return result
    segment = min(int(mp.floor(t / ell)), J)
    x = t / ell - segment
    r = 10 * x**3 - 15 * x**4 + 6 * x**5
    rp = 30 * x**2 * (1 - x) ** 2 / ell
    rpp = 60 * x * (1 - x) * (1 - 2 * x) / ell**2
    f = mp.mpc(0)
    h = mp.mpc(0)
    hp = mp.mpc(0)
    for coeff, dcoeff, omega in zip(c, dh, omegas):
        phase = mp.exp(mp.j * omega * t) / mp.sqrt(L)
        f += coeff * phase
        h += dcoeff * phase
        hp += mp.j * omega * dcoeff * phase
    result[segment] = (1 - r) * f - 2 * rp * hp - rpp * h
    if segment + 1 < count:
        result[segment + 1] = r * f + 2 * rp * hp + rpp * h
    return result


def one_case(m, M, dps, include_qn_matrices=False):
    mp.mp.dps = dps
    L = mp.log(m)
    ell = mp.mpf(2) / 9
    J = int(mp.ceil(L / ell))
    count = J + 1
    js = list(range(-M, M + 1))
    omegas = [2 * mp.pi * j / L for j in js]
    row_count = len(js)

    # Original three constraint columns and P = I - C(C* C)^(-1)C*.
    C = mp.matrix(row_count, 3)
    for i, omega in enumerate(omegas):
        C[i, 0] = 1
        C[i, 1] = 1 / (mp.mpf("0.5") - mp.j * omega)
        C[i, 2] = 1 / (mp.mpf("0.5") + mp.j * omega)
    Cstar = C.H
    P = mp.eye(row_count) - C * (Cstar * C) ** -1 * Cstar

    seed = mp.matrix(row_count, 1)
    for i, j in enumerate(js):
        phase = 1 if j % 2 == 0 else -1
        seed[i] = (j + M + 1) ** 2 + mp.j * phase * (j + M + 2)
    projected = P * seed
    projected_norm = mp.sqrt((projected.H * projected)[0])
    cmat = projected / projected_norm
    c = [cmat[i] for i in range(row_count)]
    norm_sq = (cmat.H * cmat)[0]
    constraint_residual = max(abs(value) for value in Cstar * cmat)
    projector_idempotence = max_abs_matrix(P * P - P)
    projector_hermitian = max_abs_matrix(P - P.H)
    projected_sum_norm = mp.sqrt(sum(abs(value) ** 2 for value in projected))

    dh = [-c[i] / (omegas[i] ** 2 + mp.mpf("0.25")) for i in range(row_count)]

    # Sample the same 51-point reconstruction check used by the float64 source.
    reconstruction = mp.mpf(0)
    for sample in range(51):
        t = L * sample / 50
        packets = packet_value(t, c, dh, omegas, L, ell, J)
        field = sum(
            c[i] * mp.exp(mp.j * omegas[i] * t) / mp.sqrt(L)
            for i in range(row_count)
        )
        reconstruction = max(reconstruction, abs(sum(packets) - field))

    contacts = packet_contacts(c, dh, omegas, L, ell, J, dps)
    contact_max = max(mp.mpf(contacts[str(sign)]["max_abs_contact"]) for sign in (-1, 1))

    direct = mp.mpf(0)
    term_rows = []
    all_nonzero_n = []
    for n in range(2, m + 1):
        pp = prime_power(n)
        if pp is None:
            continue
        p, exponent = pp
        all_nonzero_n.append(n)
        lam = mp.log(p)
        s = mp.log(n)
        qn = qn_matrix(omegas, js, s, L)
        qform = (cmat.H * qn * cmat)[0]
        weighted_term = lam / mp.sqrt(n) * mp.re(qform)
        direct += weighted_term
        term = {
            "n": n,
            "prime": p,
            "prime_exponent": exponent,
            "Lambda_n": mpstr(lam, dps),
            "qform_real": mpstr(mp.re(qform), dps),
            "qform_imaginary_residual": mpstr(mp.im(qform), dps),
            "weighted_direct_term": mpstr(weighted_term, dps),
        }
        if include_qn_matrices:
            term["full_Q_n_matrix"] = [
                [mpstr(qn[i, k], dps) for k in range(row_count)]
                for i in range(row_count)
            ]
        term_rows.append(term)

    saved = json.loads(INPUT.read_text())
    saved_row = next(row for row in saved["rows"] if row["m"] == m and row["M"] == M)
    saved_direct = saved_row["original_prime_quadratic_form"]
    saved_contact = saved_row["packet_contact_max"]
    # Directly evaluate formula (3.9) as implemented: sum_n Lambda(n)/sqrt(n) Re(c* Q_n c).
    # Both real and imaginary parts of each complex c*Q_n*c are retained above.
    return {
        "m": m,
        "M": M,
        "mpmath_decimal_digits": dps,
        "projector": "I - C(C* C)^(-1)C* with the original three C columns",
        "seed": "(j+M+1)^2 + i*(-1)^j*(j+M+2)",
        "projected_seed_norm_before_normalization": mpstr(projected_norm, dps),
        "normalized_projected_seed_norm": mpstr(mp.sqrt(abs(norm_sq)), dps),
        "normalized_projected_seed_norm_squared": mpstr(norm_sq, dps),
        "max_constraint_residual_abs_Cstar_c": mpstr(constraint_residual, dps),
        "projector_idempotence_max_entry_residual": mpstr(projector_idempotence, dps),
        "projector_hermitian_max_entry_residual": mpstr(projector_hermitian, dps),
        "packet_count": count,
        "packet_width_exact": "2/9",
        "packet_reconstruction_51_point_max": mpstr(reconstruction, dps),
        "packet_contacts_by_temporal_sign": contacts,
        "packet_contact_max_both_signs": mpstr(contact_max, dps),
        "saved_float64_packet_contact_max": saved_contact,
        "direct_sum_value": mpstr(direct, dps),
        "saved_float64_direct_value": saved_direct,
        "difference_from_saved_float64_decimal": mpstr(direct - mp.mpf(str(saved_direct)), dps),
        "all_nonzero_Lambda_n": all_nonzero_n,
        "n_range_scanned_inclusive": {"first": 2, "last": m, "count": m - 1},
        "prime_power_terms": term_rows,
        "full_Q_n_matrices_included": include_qn_matrices,
        "note": "Q_n uses the complete supplied row/column formula; c*Q_n*c is kept complex and its imaginary residual recorded.",
    }


def main():
    saved = json.loads(INPUT.read_text())
    cases = [(16, 2), (64, 3)]
    rows = {}
    for m, M in cases:
        low = one_case(m, M, 80, include_qn_matrices=False)
        high = one_case(m, M, 160, include_qn_matrices=True)
        drift = mp.mpf(high["direct_sum_value"]) - mp.mpf(low["direct_sum_value"])
        high["dps80_direct_sum_value"] = low["direct_sum_value"]
        high["dps80_packet_contact_max_both_signs"] = low["packet_contact_max_both_signs"]
        high["dps80_normalized_projected_seed_norm"] = low["normalized_projected_seed_norm"]
        high["dps80_normalized_projected_seed_norm_squared"] = low["normalized_projected_seed_norm_squared"]
        high["precision_drift_dps160_minus_dps80"] = mpstr(drift, 160)
        high["dps80_prime_power_terms"] = low["prime_power_terms"]
        rows[f"m{m}_M{M}"] = high

    result = {
        "status": "COMPLETED_NONINTERVAL_HIGH_PRECISION_RECHECK",
        "mpmath_version": mp.__version__,
        "precision_unit": "decimal digits (mpmath mp.dps)",
        "precisions": [80, 160],
        "input_results_sha256": hashlib.sha256(INPUT.read_bytes()).hexdigest(),
        "source_script_sha256": hashlib.sha256((ROOT / "docs/literature/openai_math_2026-10-07/q16_verdict_checks/diagnostic_q16.py").read_bytes()).hexdigest(),
        "cases": rows,
        "scope": "Finite numerical check only; no interval enclosure, asymptotic sign certificate, or production CCM claim.",
    }
    OUTPUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "status": result["status"],
        "output": str(OUTPUT),
        "cases": {
            key: {
                "dps80_direct": value["dps80_direct_sum_value"],
                "dps160_direct": value["direct_sum_value"],
                "saved_float64": value["saved_float64_direct_value"],
                "difference_from_saved": value["difference_from_saved_float64_decimal"],
                "precision_drift": value["precision_drift_dps160_minus_dps80"],
                "contact_dps80": value["dps80_packet_contact_max_both_signs"],
                "contact_dps160": value["packet_contact_max_both_signs"],
                "norm_dps80": value["dps80_normalized_projected_seed_norm"],
                "norm_dps160": value["normalized_projected_seed_norm"],
                "norm_sq_dps80": value["dps80_normalized_projected_seed_norm_squared"],
                "norm_sq_dps160": value["normalized_projected_seed_norm_squared"],
                "terms": len(value["prime_power_terms"]),
            }
            for key, value in rows.items()
        },
    }, indent=2))


if __name__ == "__main__":
    main()
