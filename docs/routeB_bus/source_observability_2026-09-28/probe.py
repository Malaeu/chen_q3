#!/usr/bin/env python3
"""High-precision diagnostic for the literal even-sector CCM matrix.

This is an observed-grid numerical calculation, not a certificate.  It imports
full_center_probe.matrix_K unchanged and computes finite Fourier projections
of the same truncated theta-G function used by full_center_probe.gaussian_plane.
The optional reference-row pass computes finite-center Z and alpha diagnostics.
No multirow S_m, gamma, or selected full-row E is constructed.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

import mpmath as mp

REPO = Path(__file__).resolve().parents[3]
SOURCE_DIR = REPO / "docs/routeB_bus/fokas_k_sign_2026-09-25"
sys.dont_write_bytecode = True
sys.path.insert(0, str(SOURCE_DIR))
import full_center_probe as fc  # noqa: E402
import rectangle_probe as rp  # noqa: E402

NEXT = REPO / "docs/Codex/NEXT.md"
TRANSFER = SOURCE_DIR / "SOURCE_TRANSFER.md"
MATRIX_SOURCE = SOURCE_DIR / "full_center_probe.py"
REFERENCE_SOURCE = SOURCE_DIR / "rectangle_probe.py"
M8_CROSSCHECK = SOURCE_DIR / "schur_probe_m8_dps140.json"
OUTPUT = Path(__file__).with_name("results.json")
EXPECTED_SHA256 = {
    "docs/Codex/NEXT.md": "eb67d6db8be5380b824f5ff3b82127d6f0b125170db2f789333bbeb280db7b0b",
    "docs/routeB_bus/fokas_k_sign_2026-09-25/SOURCE_TRANSFER.md": "b01d145b3ad3e83caf4d097da50150ec824f0876c731dde7bb0c74bb616acaa0",
    "docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py": "ead3b1e533a0d30164200602107dd70ac8ffcccadb43f42c963fe5d6f5a612c9",
    "docs/routeB_bus/fokas_k_sign_2026-09-25/rectangle_probe.py": "0e23ecd7252c0a52175c642ecc95a7527becf1ac7933f2f7ef939571ec4b0987",
    "docs/routeB_bus/fokas_k_sign_2026-09-25/schur_probe_m8_dps140.json": "86175f06cbc05861bef45818fc17861d5e7077d192155cdf05d2498c7d99cc03",
}
BASELINE_HEAD = "cbfa5254f03dd3f68f6091d3eebec49b96236c54"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_provenance() -> dict[str, object]:
    paths = {
        "docs/Codex/NEXT.md": NEXT,
        "docs/routeB_bus/fokas_k_sign_2026-09-25/SOURCE_TRANSFER.md": TRANSFER,
        "docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py": MATRIX_SOURCE,
        "docs/routeB_bus/fokas_k_sign_2026-09-25/rectangle_probe.py": REFERENCE_SOURCE,
        "docs/routeB_bus/fokas_k_sign_2026-09-25/schur_probe_m8_dps140.json": M8_CROSSCHECK,
    }
    hashes = {name: sha256(path) for name, path in paths.items()}
    for name, expected in EXPECTED_SHA256.items():
        if hashes[name] != expected:
            raise RuntimeError(f"source hash mismatch for {name}: {hashes[name]} != {expected}")
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=REPO, check=True, text=True, capture_output=True
    ).stdout.strip()
    return {
        "baseline_head_expected": BASELINE_HEAD,
        "head_observed": head,
        "source_sha256": hashes,
        "matrix_callable": "full_center_probe.matrix_K",
        "theta_G_source": "full_center_probe.gaussian_plane.G_cached formula and m,dps cutoff",
        "historical_m8_crosscheck": {
            "path": "docs/routeB_bus/fokas_k_sign_2026-09-25/schur_probe_m8_dps140.json",
            "sha256": hashes[
                "docs/routeB_bus/fokas_k_sign_2026-09-25/schur_probe_m8_dps140.json"
            ],
            "json_locators": [
                "actual_lowest_full_K_eigenpair.lambda0",
                "actual_lowest_full_K_eigenpair.full_K_eigenvalues_below_a[2]",
            ],
            "scope": "separate numerical diagnostic; not an Arb certificate",
        },
    }


def not_computed_fields(has_reference_rows: bool = False) -> dict[str, dict[str, str]]:
    return {
        "S_m": {
            "status": "NOT_COMPUTED",
            "reason": (
                "SOURCE_TRANSFER.md does not define the multirow S_m operator on the "
                "lower even eigenspace; no row operator was constructed."
            ),
        },
        "gamma_mr": {
            "status": "NOT_COMPUTED",
            "reason": (
                "The singular-value diagnostic needs the restriction of a specified "
                "multirow S_m to the lower eigenspace; SOURCE_TRANSFER.md does not define it."
            ),
        },
        "Z_m": {
            "status": "REFERENCE_CENTER_DIAGNOSTIC_ONLY" if has_reference_rows else "NOT_COMPUTED",
            "reason": (
                "The optional reference_rows section measures Z=||zhat|| for finite "
                "Robin midpoint rows; this is not a cofinal selected-family result."
            ),
        },
        "E_m": {
            "status": "NOT_COMPUTED",
            "reason": (
                "SOURCE_TRANSFER.md defines E through the selected full-row error budget "
                "(T4); this probe does not compute that row, its interval/sup energy error, "
                "or its tail bound."
            ),
        },
        "E_m_over_Z_m": {
            "status": "NOT_COMPUTED",
            "reason": (
                "Finite midpoint Z values are available after augmentation, but the "
                "matching selected full-row E bound is not evaluated on these cells."
            ),
        },
        "alpha_m": {
            "status": "REFERENCE_CENTER_DIAGNOSTIC_ONLY" if has_reference_rows else "NOT_COMPUTED",
            "reason": (
                "The optional reference_rows section measures the finite same-K ground "
                "angle for Robin midpoint rows; no eventual rate is established."
            ),
        },
    }


def poly_derivative(coeffs: list[mp.mpf]) -> list[mp.mpf]:
    return [mp.mpf(i) * coeffs[i] for i in range(1, len(coeffs))]


def poly_add(left: list[mp.mpf], right: list[mp.mpf]) -> list[mp.mpf]:
    out = [mp.mpf("0")] * max(len(left), len(right))
    for i, value in enumerate(left):
        out[i] += value
    for i, value in enumerate(right):
        out[i] += value
    return out


def theta_derivative_polynomials(max_order: int) -> list[list[mp.mpf]]:
    # G(t) = exp(t/2) * sum_r P_0(z_r) exp(-z_r),
    # z_r = pi (r exp(t))^2, P_0(z)=24z-16z^2.
    polys = [[mp.mpf("0"), mp.mpf("24"), mp.mpf("-16")]]
    for _ in range(max_order):
        p = polys[-1]
        dp = poly_derivative(p)
        # d/dt [exp(t/2) P(z) exp(-z)] corresponds to
        # P_next = P/2 + 2 z P' - 2 z P, since z'=2z.
        out = [mp.mpf("0")] * (len(p) + 1)
        for i, value in enumerate(p):
            out[i] += value / 2 + 2 * i * value
            out[i + 1] -= 2 * value
        # dp is computed as an independent shape check for the recurrence.
        if len(dp) > len(out):
            raise RuntimeError("unexpected derivative polynomial degree")
        polys.append(out)
    return polys


def theta_G_derivative(t: mp.mpf, order: int, cutoff: int,
                       polys: list[list[mp.mpf]]) -> mp.mpf:
    u = mp.exp(t)
    p = polys[order]
    values = []
    for r in range(1, cutoff + 1):
        z = mp.pi * (r * u) ** 2
        pz = mp.polyval(list(reversed(p)), z)
        values.append(pz * mp.exp(-z))
    return mp.exp(t / 2) * mp.fsum(values)


def theta_endpoint_evenness(m: int, dps: int) -> dict[str, str | int]:
    """Directly compare the same finite theta series at +/- b, for G and G''."""
    mp.mp.dps = dps
    b = mp.log(m) / 2
    cutoff = int(mp.ceil(mp.sqrt(m * (mp.mp.dps + 20) * mp.log(10) / mp.pi))) + 3
    polys = theta_derivative_polynomials(2)
    g_left = theta_G_derivative(-b, 0, cutoff, polys)
    g_right = theta_G_derivative(b, 0, cutoff, polys)
    g2_left = theta_G_derivative(-b, 2, cutoff, polys)
    g2_right = theta_G_derivative(b, 2, cutoff, polys)
    return {
        "dps": dps,
        "cutoff": cutoff,
        "G_minus_b_minus_G_b_abs": mp_string(abs(g_left - g_right), dps),
        "G2_minus_b_minus_G2_b_abs": mp_string(abs(g2_left - g2_right), dps),
        "max_abs_endpoint_evenness_residual": mp_string(
            max(abs(g_left - g_right), abs(g2_left - g2_right)), dps
        ),
    }


def even_basis(m: int) -> mp.matrix:
    """Columns are the orthonormal reflection-even vectors in modes -m..m."""
    q = mp.zeros(2 * m + 1, m + 1)
    q[m, 0] = 1
    inv_sqrt_two = 1 / mp.sqrt(2)
    for n in range(1, m + 1):
        q[m - n, n] = inv_sqrt_two
        q[m + n, n] = inv_sqrt_two
    return q


def max_abs_matrix(a: mp.matrix) -> mp.mpf:
    return max((abs(a[i, j]) for i in range(a.rows) for j in range(a.cols)),
               default=mp.mpf("0"))


def max_abs_vector(a: mp.matrix) -> mp.mpf:
    return max((abs(a[i]) for i in range(a.rows)), default=mp.mpf("0"))


def matrix_norm_inf(a: mp.matrix) -> mp.mpf:
    return max((mp.fsum(abs(a[i, j]) for j in range(a.cols))
                for i in range(a.rows)), default=mp.mpf("0"))


def mp_string(value: mp.mpf, digits: int) -> str:
    return mp.nstr(value, n=digits, strip_zeros=False)


def orthogonal_complement_basis(q: mp.matrix) -> mp.matrix:
    """Build an orthonormal basis of the complex complement of unit q."""
    n = q.rows
    e0 = mp.zeros(n, 1)
    e0[0] = 1
    phase = q[0] / abs(q[0]) if q[0] != 0 else mp.mpf(1)
    householder_vector = q + phase * e0
    denominator = mp.re((householder_vector.H * householder_vector)[0])
    if denominator <= 0:
        raise ArithmeticError("cannot form Householder complement basis")

    # H maps e0 to -conj(phase)*q, so its remaining columns form an
    # orthonormal basis perpendicular to the complex vector q.
    basis = mp.zeros(n, n - 1)
    for j in range(1, n):
        column = mp.zeros(n, 1)
        column[j] = 1
        column -= 2 * householder_vector * mp.conj(householder_vector[j]) / denominator
        for i in range(n):
            basis[i, j - 1] = column[i]
    return basis


def run_one(m: int, dps: int) -> dict[str, object]:
    mp.mp.dps = dps
    t0 = time.monotonic()
    L = mp.log(m)
    b = L / 2
    cutoff = int(mp.ceil(mp.sqrt(m * (mp.mp.dps + 20) * mp.log(10) / mp.pi))) + 3

    print(f"m={m}: evaluating literal full_center_probe.matrix_K at dps={dps}", flush=True)
    t_matrix = time.monotonic()
    K = fc.matrix_K(m)
    matrix_seconds = time.monotonic() - t_matrix
    print(f"m={m}: K ready ({matrix_seconds:.2f}s); restricting even sector", flush=True)

    Q = even_basis(m)
    B = Q.T * K * Q
    eigvals, eigvecs = mp.eigsy(B)
    order = min(5, len(eigvals))
    low = [eigvals[i] for i in range(order)]
    gaps = {
        "lambda2_minus_lambda1": eigvals[1] - eigvals[0] if order >= 2 else None,
        "lambda3_minus_lambda1": eigvals[2] - eigvals[0] if order >= 3 else None,
    }

    b_sym = max(abs(B[i, j] - B[j, i])
                for i in range(B.rows) for j in range(B.cols))
    ident = eigvecs.T * eigvecs
    orth_residual = max(abs(ident[i, j] - (1 if i == j else 0))
                        for i in range(ident.rows) for j in range(ident.cols))
    k_inf = matrix_norm_inf(B)
    eig_residuals = []
    for j in range(order):
        v = mp.matrix([eigvecs[i, j] for i in range(eigvecs.rows)])
        residual = B * v - eigvals[j] * v
        abs_resid = max_abs_vector(residual)
        denom = max(mp.mpf("1"), (k_inf + abs(eigvals[j])) * max_abs_vector(v))
        eig_residuals.append({
            "eigenvalue_index": j + 1,
            "absolute_inf_residual": mp_string(abs_resid, dps),
            "scaled_inf_residual": mp_string(abs_resid / denom, dps),
        })

    polys = theta_derivative_polynomials(8)
    rayleighs: list[dict[str, object]] = []
    for k in range(5):
        derivative_order = 2 * k
        positive_coeffs = []
        for n in range(m + 1):
            coeff = ((-1) ** n) * (2 / mp.sqrt(L)) * mp.quad(
                lambda x, n=n, order=derivative_order:
                    theta_G_derivative(x, order, cutoff, polys)
                    * mp.cos(2 * mp.pi * n * x / L),
                [0, b / 2, b],
            )
            positive_coeffs.append(coeff)
        full_coeffs = mp.matrix([positive_coeffs[abs(n)] for n in range(-m, m + 1)])
        even_coeffs = Q.T * full_coeffs
        norm_sq = (even_coeffs.T * even_coeffs)[0]
        if norm_sq == 0:
            rq = None
        else:
            rq = (even_coeffs.T * B * even_coeffs)[0] / norm_sq
        projected = Q * even_coeffs
        projection_residual = max_abs_vector(full_coeffs - projected)
        rayleighs.append({
            "k": k,
            "derivative_order": derivative_order,
            "rayleigh_quotient_observed": None if rq is None else mp_string(rq, dps),
            "projected_even_vector_norm": mp_string(mp.sqrt(norm_sq), dps),
            "even_projection_inf_residual": mp_string(projection_residual, dps),
        })
        print(f"m={m}: D^{derivative_order}G projection done", flush=True)

    reflection_residual = max(
        abs(K[i, j] - K[2 * m - i, 2 * m - j])
        for i in range(2 * m + 1)
        for j in range(2 * m + 1)
    )
    result = {
        "m": m,
        "dps": dps,
        "theta_truncation_cutoff": cutoff,
        "dimensions": {
            "full_matrix": 2 * m + 1,
            "even_reflection_sector": m + 1,
        },
        "lowest_even_sector_eigenvalues": [
            {"index": i + 1, "value": mp_string(low[i], dps)} for i in range(order)
        ],
        "splittings": {
            key: None if value is None else mp_string(value, dps)
            for key, value in gaps.items()
        },
        "projected_theta_derivative_rayleigh_quotients": rayleighs,
        "validation": {
            "even_sector_matrix_symmetry_inf": mp_string(b_sym, dps),
            "even_sector_reflection_commutator_inf": mp_string(reflection_residual, dps),
            "eigenvector_orthogonality_inf": mp_string(orth_residual, dps),
            "lowest_eigenpair_residuals": eig_residuals,
            "projection_residuals_are_observed_not_interval_bounds": True,
        },
        "timing_seconds": {
            "literal_matrix_K": matrix_seconds,
            "complete_sample": time.monotonic() - t0,
        },
        "status": "NUMERICAL_DIAGNOSTIC_ONLY_NOT_A_PROOF",
    }
    return result


def run_reference_row(m: int, dps: int) -> dict[str, object]:
    """Numerical center row z(c0,c4) and same-K ground angle from T4.

    The Robin intervals and finite Mellin map are exactly the ones used by
    schur_probe.run.  This does not construct the selected full row b or E.
    """
    mp.mp.dps = dps
    if not hasattr(rp._mp_kernel, "cache_info"):
        rp._mp_kernel = lru_cache(maxsize=None)(rp._mp_kernel)
    t0 = time.monotonic()
    print(f"m={m}: building reference Robin row at dps={dps}", flush=True)
    intervals = rp.bracket(m)
    c0 = mp.fsum(intervals[0]) / 2
    c4 = mp.fsum(intervals[4]) / 2
    p0 = rp.recurrence(m, c0)[0]
    p4 = rp.recurrence(m, c4)[0]
    F = rp.F_matrix(m)
    coeff = mp.matrix([(-1)**k * (p0[k] - p4[k]) for k in range(1, 6*m)])
    z = F * coeff
    norm_sq = mp.re((z.H * z)[0])
    if norm_sq <= 0:
        raise ArithmeticError("reference row has nonpositive squared norm")
    Z = mp.sqrt(norm_sq)
    q = z / Z

    print(f"m={m}: reference row ready; computing same literal K ground vector", flush=True)
    K = fc.matrix_K(m)
    eigvals, eigvecs = mp.eigsy(K)
    u = mp.matrix([eigvecs[i, 0] for i in range(eigvecs.rows)])
    overlap = (u.H * q)[0]
    projection = u * overlap
    alpha_sq = mp.re(((q - projection).H * (q - projection))[0])
    alpha = mp.sqrt(alpha_sq)
    all_excited_weights = []
    for j in range(1, eigvals.rows):
        uj = mp.matrix([eigvecs[i, j] for i in range(eigvecs.rows)])
        weight = abs((uj.H * q)[0]) ** 2
        all_excited_weights.append({
            "full_K_index": j + 1,
            "eigenvalue": mp_string(eigvals[j], dps),
            "weight": mp_string(weight, dps),
            "fraction_of_alpha_squared": (
                None if alpha_sq == 0 else mp_string(weight / alpha_sq, dps)
            ),
        })
    spectral_alpha_sq = mp.fsum(
        mp.mpf(mode["weight"]) for mode in all_excited_weights
    )
    spectral_alpha = mp.sqrt(spectral_alpha_sq)
    dominant_mode = max(
        zip((mp.mpf(mode["weight"]) for mode in all_excited_weights), all_excited_weights),
        key=lambda item: item[0],
    )[1]
    three_largest_excited_weights = sorted(
        all_excited_weights,
        key=lambda mode: mp.mpf(mode["weight"]),
        reverse=True,
    )[:3]

    # Test the proposed cut mu=a directly on q^perp.  This compression is built
    # from q itself and does not rely on an exact parity assertion.
    a = mp.re((q.H * K * q)[0])
    q_perp = orthogonal_complement_basis(q)
    compressed_K = q_perp.H * K * q_perp
    q_perp_eigvals, q_perp_eigvecs = mp.eighe(compressed_K)
    q_perp_minimum = q_perp_eigvals[0]
    q_perp_minimizer = q_perp * mp.matrix(
        [q_perp_eigvecs[i, 0] for i in range(q_perp_eigvecs.rows)]
    )
    cut_margin = q_perp_minimum - a
    projected_cut_residual = q_perp.H * (
        (K - a * mp.eye(K.rows)) * q_perp_minimizer
        - cut_margin * q_perp_minimizer
    )
    q_perp_gram = q_perp.H * q_perp
    q_perp_basis_orthogonality = max(
        abs(q_perp_gram[i, j] - (1 if i == j else 0))
        for i in range(q_perp_gram.rows)
        for j in range(q_perp_gram.cols)
    )
    residual = K*u - eigvals[0]*u
    reflection_z = mp.matrix([z[2*m-i] for i in range(2*m+1)])
    reflection_u = mp.matrix([u[2*m-i] for i in range(2*m+1)])
    even_u_mass = mp.re((((u+reflection_u)/2).H * ((u+reflection_u)/2))[0])
    return {
        "m": m,
        "dps": dps,
        "definition": "zhat=F_m*((-1)^k(P_k(c0)-P_k(c4)))_{k=1}^{6m-1}; Z=||zhat||; alpha=||(I-uu*)zhat/Z||, u=lowest full-K eigenvector",
        "center_energies": {"c0": mp_string(c0, dps), "c4": mp_string(c4, dps)},
        "Z_m_reference": mp_string(Z, dps),
        "alpha_m_reference": mp_string(alpha, dps),
        "reference_rayleigh_a_full_K": mp_string(a, dps),
        "three_largest_excited_spectral_weights": three_largest_excited_weights,
        "alpha_squared_from_all_excited_spectral_weights": mp_string(
            spectral_alpha_sq, dps
        ),
        "alpha_from_all_excited_spectral_weights": mp_string(spectral_alpha, dps),
        "alpha_squared_reconstruction_abs_error": mp_string(
            abs(spectral_alpha_sq - alpha_sq), dps
        ),
        "dominant_excited_mode_fraction_of_alpha_squared": (
            None if alpha_sq == 0 else mp_string(mp.mpf(dominant_mode["weight"]) / alpha_sq, dps)
        ),
        "cut_mu_equals_a_q_perp_test": {
            "definition": "min_{v perpendicular to q, ||v||=1} <v,(K-aI)v>, a=<q,Kq>",
            "a_full_K": mp_string(a, dps),
            "q_perp_minimum_eigenvalue_of_K": mp_string(q_perp_minimum, dps),
            "minimum_q_perp_value_of_K_minus_aI": mp_string(cut_margin, dps),
            "minimizer_q_orthogonality_residual": mp_string(
                abs((q.H * q_perp_minimizer)[0]), dps
            ),
            "q_perp_basis_q_orthogonality_inf": mp_string(
                max(abs((q.H * q_perp)[j]) for j in range(q_perp.cols)), dps
            ),
            "compressed_eigenpair_projected_residual_inf": mp_string(
                max_abs_vector(projected_cut_residual), dps
            ),
            "q_perp_basis_orthogonality_inf": mp_string(q_perp_basis_orthogonality, dps),
            "status": "FINITE_DIMENSIONAL_NUMERICAL_DIAGNOSTIC_ONLY",
        },
        "ground_eigenvalue_full_K": mp_string(eigvals[0], dps),
        "ground_eigenvalue_gap_full_K": mp_string(eigvals[1]-eigvals[0], dps),
        "source_even_reflection_difference_norm": mp_string(
            mp.sqrt(mp.re(((z-reflection_z).H*(z-reflection_z))[0])), dps
        ),
        "ground_even_mass": mp_string(even_u_mass, dps),
        "ground_eigenpair_residual_inf": mp_string(max_abs_vector(residual), dps),
        "elapsed_seconds": time.monotonic()-t0,
        "status": "REFERENCE_CENTER_NUMERICAL_DIAGNOSTIC_ONLY_NOT_SELECTED_FULL_ROW",
    }


def slope(xs: list[int], ys: list[mp.mpf], dps: int) -> dict[str, object]:
    if len(xs) < 3:
        return {"status": "NOT_MEANINGFUL", "reason": "fewer than three samples"}
    if any(y == 0 for y in ys):
        return {"status": "NOT_MEANINGFUL", "reason": "zero value"}
    signs = {mp.sign(y) for y in ys}
    if len(signs) != 1:
        return {"status": "NOT_MEANINGFUL", "reason": "sign changes"}
    xx = [mp.log(x) for x in xs]
    yy = [mp.log(abs(y)) for y in ys]
    xbar = mp.fsum(xx) / len(xx)
    ybar = mp.fsum(yy) / len(yy)
    estimate = mp.fsum((x - xbar) * (y - ybar) for x, y in zip(xx, yy)) / mp.fsum(
        (x - xbar) ** 2 for x in xx
    )
    return {
        "status": "EXPLORATORY_FIT",
        "slope": mp_string(estimate, dps),
        "basis": "least-squares slope of log(abs(value)) against log(m)",
        "sample_count": len(xs),
    }


def make_slope_table(samples: list[dict[str, object]], dps: int) -> dict[str, object]:
    xs = [int(s["m"]) for s in samples]
    table: dict[str, object] = {}
    for key in ("lambda2_minus_lambda1", "lambda3_minus_lambda1"):
        ys = [mp.mpf(s["splittings"][key]) for s in samples]
        table[key] = slope(xs, ys, dps)
    for k in range(5):
        ys = [
            mp.mpf(s["projected_theta_derivative_rayleigh_quotients"][k]
                   ["rayleigh_quotient_observed"])
            for s in samples
        ]
        table[f"rayleigh_D{2*k}_G"] = slope(xs, ys, dps)
    return table


def save_partial(record: dict[str, object]) -> None:
    OUTPUT.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def refresh_saved_metadata() -> None:
    record = json.loads(OUTPUT.read_text(encoding="utf-8"))
    record["provenance"] = source_provenance()
    record["observed_head"] = record["provenance"]["head_observed"]
    record["not_computed"] = not_computed_fields(bool(record.get("reference_rows")))
    record["method"]["completed_m_values"] = [int(s["m"]) for s in record["samples"]]
    record["method"]["sample_dps_by_m"] = {
        str(s["m"]): int(s["dps"]) for s in record["samples"]
    }
    record["limitations"] = [
        item.replace("Three-cell log-log fits", "Four-cell log-log fits")
        for item in record["limitations"]
    ]
    for sample in record["samples"]:
        sample.setdefault("validation", {})["theta_endpoint_evenness"] = theta_endpoint_evenness(
            int(sample["m"]), int(sample["dps"])
        )
    record["log_log_slopes"] = make_slope_table(
        record["samples"], int(record["method"]["precision_dps"])
    )
    record["metadata_refresh_command"] = (
        ".venv/bin/python docs/routeB_bus/source_observability_2026-09-28/"
        "probe.py --refresh-metadata"
    )
    save_partial(record)
    print(f"refreshed metadata and endpoint checks in {OUTPUT}", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m-list", nargs="+", type=int, default=[8, 12, 16])
    parser.add_argument("--dps", type=int, default=70)
    parser.add_argument("--refresh-metadata", action="store_true")
    parser.add_argument("--augment-reference-rows", action="store_true")
    parser.add_argument("--append-samples", action="store_true")
    args = parser.parse_args()
    if args.refresh_metadata:
        refresh_saved_metadata()
        return
    if args.augment_reference_rows:
        if args.dps < 60:
            raise SystemExit("--dps must be at least 60")
        record = json.loads(OUTPUT.read_text(encoding="utf-8"))
        source_provenance()
        reference_rows = record.setdefault("reference_rows", {})
        for m in args.m_list:
            reference_rows[str(m)] = run_reference_row(m, args.dps)
            record["not_computed"] = not_computed_fields(True)
            save_partial(record)
            print(f"m={m}: reference row saved", flush=True)
        return
    if args.append_samples:
        if args.dps < 60:
            raise SystemExit("--dps must be at least 60")
        if any(m < 1 for m in args.m_list):
            raise SystemExit("all m must be positive")
        record = json.loads(OUTPUT.read_text(encoding="utf-8"))
        source_provenance()
        existing = {int(sample["m"]) for sample in record["samples"]}
        for m in args.m_list:
            if m in existing:
                raise SystemExit(f"m={m} already saved; refusing to overwrite")
            record["samples"].append(run_one(m, args.dps))
            existing.add(m)
            record["samples"].sort(key=lambda sample: int(sample["m"]))
            record["log_log_slopes"] = make_slope_table(record["samples"], args.dps)
            save_partial(record)
            print(f"m={m}: full even-sector sample appended", flush=True)
        return
    if args.dps < 60:
        raise SystemExit("--dps must be at least 60")
    if any(m < 1 for m in args.m_list):
        raise SystemExit("all m must be positive")
    provenance = source_provenance()
    record: dict[str, object] = {
        "title": "Literal full K even-sector source observability diagnostics",
        "classification": "DIAGNOSTIC_ONLY_NOT_A_PROOF",
        "baseline_head": BASELINE_HEAD,
        "observed_head": provenance["head_observed"],
        "provenance": provenance,
        "method": {
            "K": "direct call to unchanged full_center_probe.matrix_K(m)",
            "even_sector": "orthonormal basis e_0, (e_n+e_-n)/sqrt(2), n=1..m",
            "theta_G": (
                "same finite theta-G sum and m,dps cutoff as full_center_probe.gaussian_plane; "
                "D^(2k) derivatives evaluated by the exact polynomial recurrence"
            ),
            "Fourier_projection": (
                "c_n=(-1)^n*2/sqrt(log m)*integral_0^(log m/2) "
                "G^(2k)(t) cos(2*pi*n*t/log m) dt, n=-m..m; "
                "then orthogonal projection to reflection-even sector"
            ),
            "rayleigh": "v^T (Q^T K Q) v / (v^T v) for projected even-sector coordinates v",
            "precision_dps": args.dps,
            "requested_m_values": args.m_list,
            "reproduction_command": (
                ".venv/bin/python docs/routeB_bus/source_observability_2026-09-28/"
                "probe.py --m-list " + " ".join(map(str, args.m_list))
                + f" --dps {args.dps}"
            ),
        },
        "not_computed": not_computed_fields(),
        "samples": [],
        "log_log_slopes": {"status": "NOT_COMPUTED_YET"},
        "limitations": [
            "mpmath quadrature and eigensolver outputs are not interval enclosures.",
            "The theta-G series uses the finite cutoff copied from full_center_probe.gaussian_plane.",
            "Eigenpair residuals validate the numerical eigensolver result, not matrix quadrature error.",
            "Three-cell log-log fits are exploratory and establish no asymptotic rate.",
            "No selected-source S_m-based observability or source-transfer conclusion is made.",
        ],
    }
    save_partial(record)
    for m in args.m_list:
        sample = run_one(m, args.dps)
        record["samples"].append(sample)
        record["log_log_slopes"] = make_slope_table(record["samples"], args.dps)
        save_partial(record)
        print(f"m={m}: sample saved; total={sample['timing_seconds']['complete_sample']:.2f}s",
              flush=True)
    print(f"wrote {OUTPUT}", flush=True)


if __name__ == "__main__":
    main()
