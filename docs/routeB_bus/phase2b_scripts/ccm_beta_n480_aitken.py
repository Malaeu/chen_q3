#!/usr/bin/env python3
"""Phase 2B RUN_DELTA_N480_AITKEN: rigorous fixed-q beta*_480, Aitken Delta^2,
parity ledger, for Goal 057 cell m=13.

Frozen spec (batch rank 1, 2026-08-09): N=480, dim 961, SAME fixed q in E_120
as Phase 2, literal zero-padding, no profile re-optimization, no schedule
changes after seeing results.  python-flint/Arb interval arithmetic, interval
LDLT, two independent eigensolvers (vdhoeven_mourrain production, rump
independent full repeat), precision doubling 180 -> 360 dps, every output an
enclosure.  Aitken Delta^2 over (beta*_120, beta*_240, beta*_480) with the
stored Phase-2 360-dps enclosures as x0, x1.  Pre-registered decision rule on
r3 = beta*_480/beta*_240 (verbatim, frozen):

    r3 <= 0.84         => POWER_LAW_WITNESS_DECAY
    0.86 <= r3 <= 0.90 => CONV_Q1      (beta_inf ~ 1.900e-55)
    r3 >= 0.92         => CONV_Q2PLUS  (beta_inf ~ 2.285e-55)
    otherwise          => TRANSIENT    -> schedule N=960, same spec

Search failure at any stage = CERT_NOT_FOUND, its own verdict class.

All matrix construction, q embedding, Householder, floor, Schur and LDLT
logic is imported from the SHA-pinned Phase-2 script (which itself pins the
Phase-1 builder and the exact rational q source).  This file adds only:
algorithm parameterization, bottom-k spectra, eigenvector parity ledger,
interlacing versus N=240, Aitken/r3 enclosures, and the frozen decision rule.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import acb, arb, arb_mat, acb_mat, ctx


REPO = Path(__file__).resolve().parents[3]
PHASE2_SCRIPT = REPO / "docs/routeB_bus/phase2_scripts/ccm_beta_n_profile.py"
EXPECTED_PHASE2_SHA256 = "851db5963b4ad012cc3746b2827931b1beedad0b931676d2b40f4cb9ca774f72"
PHASE2_RESULTS = REPO / "docs/routeB_bus/phase2_results/ccm_fixed_q_beta_n_profile.json"
EXPECTED_PHASE2_RESULTS_SHA256 = "204e441ee807938335a3826257e1b77cb186fb9aa5416eec66b46cd54b69ff4b"

N_2B = 480
PRECISIONS = (180, 360)
PRODUCTION_ALGORITHM = "vdhoeven_mourrain"
INDEPENDENT_ALGORITHM = "rump"
BOTTOM_K = 5
FINALIZE_DPS = 400

DECISION_RULE_VERBATIM = [
    "r3 <= 0.84         => POWER_LAW_WITNESS_DECAY  (fixed-q witness decays; NOT the true gap, NOT Route B)",
    "0.86 <= r3 <= 0.90 => CONV_Q1      (beta_inf ~ 1.900e-55)",
    "r3 >= 0.92         => CONV_Q2PLUS  (beta_inf ~ 2.285e-55)",
    "otherwise          => TRANSIENT    -> schedule N=960, same spec",
    "Search failure at any stage = CERT_NOT_FOUND, its own verdict class",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_phase2_module():
    actual = sha256(PHASE2_SCRIPT)
    if actual != EXPECTED_PHASE2_SHA256:
        raise SystemExit(f"Phase-2 implementation pin mismatch: {actual}")
    name = "ccm_phase2_pinned"
    spec = importlib.util.spec_from_file_location(name, PHASE2_SCRIPT)
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load pinned Phase-2 implementation")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


P2 = load_phase2_module()
P1 = P2.P1


def environment_record() -> dict[str, Any]:
    return {
        "os": platform.system(),
        "platform": platform.platform(),
        "python_version": sys.version.split()[0],
        "python_flint_version": __import__("flint").__version__,
        "phase2_python_flint_version": "0.8.0",
        "arb_threads": 1,
    }


def rigorous_floor_k(
    matrix: arb_mat, algorithm: str, bottom_k: int
) -> tuple[arb, list[arb], dict[str, Any]]:
    """Phase-2 rigorous_floor with algorithm parameter and bottom-k spectrum."""
    started = time.time()
    eigenvalues = matrix.eig(algorithm=algorithm)
    if len(eigenvalues) != matrix.nrows():
        raise RuntimeError("Arb did not isolate the complete spectrum")
    ordered = sorted(eigenvalues, key=lambda z: float(z.real.mid()))
    first = ordered[0]
    if 0 not in first.imag:
        raise RuntimeError(f"Hermitian eigenvalue enclosure missed the real axis: {first}")
    floor = first.real
    if not floor.lower() > 0:
        raise RuntimeError(f"spectral floor is not certified positive: {first}")
    bottom = []
    for z in ordered[:bottom_k]:
        if 0 not in z.imag:
            raise RuntimeError(f"bottom-{bottom_k} enclosure missed the real axis: {z}")
        bottom.append(z.real)
    return floor, bottom, {
        "floor": P1.bounds(floor),
        "imaginary_radius": str(first.imag),
        "eigenvalue_count": len(ordered),
        "bottom_k": [P1.bounds(x) for x in bottom],
        "elapsed_seconds": time.time() - started,
        "algorithm": algorithm,
    }


def build_even_side(projected: list[Fraction], n_cutoff: int):
    """Shared even-sector pipeline: blocks, q, Householder, compression."""
    builder = P2.CCMArbBuilderN(n_cutoff)
    k_even, k_odd, samples = builder.parity_blocks()
    q = P2.fixed_q_even_coords(projected, n_cutoff)
    h = P2.householder_q_first(q)
    transformed = h.transpose() * k_even * h
    a = transformed[0, 0]
    compression = P2.submatrix(transformed, 1, 1, n_cutoff, n_cutoff)
    coupling = P2.submatrix(transformed, 1, 0, n_cutoff, 1)
    return k_even, k_odd, samples, q, h, transformed, a, compression, coupling


def run_profile_cell(
    projected: list[Fraction], n_cutoff: int, dps: int, algorithm: str
) -> dict[str, Any]:
    """Phase-2 run_cell, algorithm-parameterized, plus bottom-k spectra and
    the literal zero-padding witness.  Gates verbatim from Phase 2."""
    ctx.dps = dps
    ctx.threads = 1
    started = time.time()
    k_even, k_odd, samples, q, h, transformed, a, compression, coupling = build_even_side(
        projected, n_cutoff
    )
    q_norm_sq = sum((x * x for x in q), arb(0))
    zero_padding_literal = all(q[n].is_zero() for n in range(P2.N0 + 1, n_cutoff + 1))

    compression_floor, compression_bottom, compression_meta = rigorous_floor_k(
        compression, algorithm, BOTTOM_K
    )
    odd_floor, odd_bottom, odd_meta = rigorous_floor_k(k_odd, algorithm, BOTTOM_K)
    beta_star, controlling_sector = P2.choose_beta_star(compression_floor, odd_floor)
    if not beta_star.lower() > 0 or not beta_star.upper() < P2.INITIAL_BETA_UPPER:
        raise RuntimeError(f"beta-star escaped the precommitted bracket: {beta_star}")
    tolerance = max(P2.ABSOLUTE_TOL, beta_star.upper() / P2.RELATIVE_TOL_DENOMINATOR)
    width = beta_star.upper() - beta_star.lower()
    if not width < tolerance:
        raise RuntimeError(
            f"beta-star enclosure wider than precommit tolerance: {width} >= {tolerance}"
        )

    beta_cert = beta_star.lower() * (1 - arb(1) / P2.RELATIVE_TOL_DENOMINATOR)
    if not beta_cert.upper() < beta_star.lower():
        raise RuntimeError("safe beta endpoint did not separate from beta-star")
    c_beta = arb_mat(compression)
    for i in range(n_cutoff):
        c_beta[i, i] -= beta_cert
    solved = c_beta.solve(coupling, algorithm="precond")
    schur_term = (coupling.transpose() * solved)[0, 0]
    tau_required = beta_cert - a + schur_term
    tau_cert = arb(1)
    if not tau_required.upper() < tau_cert:
        raise RuntimeError(
            f"precommitted tau=1 is not certified above tau_required: {tau_required}"
        )

    full = P2.full_penalty_check(k_even, k_odd, q, beta_cert, tau_cert)
    interval_pass = bool(
        beta_cert > a.upper() and full["even"]["pass"] and full["odd"]["pass"]
    )
    return {
        "cell": "profile",
        "N": n_cutoff,
        "dimension": 2 * n_cutoff + 1,
        "dps": dps,
        "eigen_algorithm": algorithm,
        "elapsed_seconds": time.time() - started,
        "q_embedding": "exact_zero_padding_from_E_120",
        "q_zero_padding_literal_beyond_N0": zero_padding_literal,
        "q_norm_sq": P1.bounds(q_norm_sq),
        "a": P1.bounds(a),
        "compression_floor": compression_meta,
        "odd_floor": odd_meta,
        "beta_N_star": P1.bounds(beta_star),
        "controlling_sector": controlling_sector,
        "beta_N_star_minus_a": P1.bounds(beta_star - a),
        "beta_search_tolerance": str(tolerance),
        "beta_enclosure_width": str(width),
        "safe_beta": P1.bounds(beta_cert),
        "tau_required": P1.bounds(tau_required),
        "tau_certificate": "1",
        "full_interval_ldlt": full,
        "interval_certificate_pass": interval_pass,
        "matrix_entry_samples": samples,
        "environment": environment_record(),
    }


def bottom_eigenvector(matrix: arb_mat, algorithm: str) -> tuple[list[arb], arb, dict[str, Any]]:
    """Certified bottom eigenvector via acb_mat.eig(right=True).

    Returns real coefficient enclosures (sign-normalized so the largest-|mid|
    component is positive), the eigenvalue enclosure, and a meta record."""
    started = time.time()
    attempts = []
    ev = vectors = None
    used = None
    for alg in (algorithm, INDEPENDENT_ALGORITHM):
        try:
            ev, vectors = acb_mat(matrix).eig(right=True, algorithm=alg)
            used = alg
            break
        except Exception as exc:  # noqa: BLE001 - recorded, then fallback
            attempts.append({"algorithm": alg, "error": repr(exc)})
    if ev is None:
        raise RuntimeError(f"eigenvector enclosure unavailable: {attempts}")
    index = min(range(len(ev)), key=lambda i: float(ev[i].real.mid()))
    value = ev[index]
    if 0 not in value.imag:
        raise RuntimeError(f"bottom eigenvalue enclosure missed the real axis: {value}")
    n = matrix.nrows()
    column = [vectors[i, index] for i in range(n)]
    imag_ok = all(0 in z.imag for z in column)
    if not imag_ok:
        raise RuntimeError("bottom eigenvector enclosure is not certified real")
    real = [z.real for z in column]
    norm_sq = sum((x * x for x in real), arb(0))
    if not norm_sq.lower() > 0:
        raise RuntimeError("bottom eigenvector norm is not certified positive")
    norm = norm_sq.sqrt()
    real = [x / norm for x in real]
    anchor = max(range(n), key=lambda i: abs(float(real[i].mid())))
    if float(real[anchor].mid()) < 0:
        real = [-x for x in real]
    meta = {
        "eigenvalue": P1.bounds(value.real),
        "eigenvalue_imaginary_radius": str(value.imag),
        "algorithm_used": used,
        "failed_attempts": attempts,
        "vector_certified_real": imag_ok,
        "elapsed_seconds": time.time() - started,
    }
    return real, value.real, meta


def parity_split(coeffs: list[arb], mode_of_index) -> dict[str, Any]:
    """Mass on even/odd MODE indices, certified sign changes, dominant modes."""
    even_mass = arb(0)
    odd_mass = arb(0)
    signs = []
    for i, x in enumerate(coeffs):
        m = mode_of_index(i)
        sq = x * x
        if m % 2 == 0:
            even_mass += sq
        else:
            odd_mass += sq
        if x.lower() > 0:
            signs.append(1)
        elif x.upper() < 0:
            signs.append(-1)
        else:
            signs.append(0)
    certified = [s for s in signs if s != 0]
    sign_changes = sum(1 for p, q in zip(certified, certified[1:]) if p != q)
    unresolved = sum(1 for s in signs if s == 0)
    dominant = sorted(range(len(coeffs)), key=lambda i: -abs(float(coeffs[i].mid())))[:8]
    return {
        "mass_on_even_modes": P1.bounds(even_mass),
        "mass_on_odd_modes": P1.bounds(odd_mass),
        "certified_sign_changes": sign_changes,
        "entries_with_unresolved_sign": unresolved,
        "dominant_modes": [
            {"mode_n": mode_of_index(i), "coefficient": P1.bounds(coeffs[i])}
            for i in dominant
        ],
    }


def run_vectors_cell(
    projected: list[Fraction], sector: str, dps: int, algorithm: str
) -> dict[str, Any]:
    ctx.dps = dps
    ctx.threads = 1
    started = time.time()
    if sector == "odd":
        builder = P2.CCMArbBuilderN(N_2B)
        _, k_odd, _ = builder.parity_blocks()
        coeffs, eigenvalue, meta = bottom_eigenvector(k_odd, algorithm)
        ledger = parity_split(coeffs, lambda i: i + 1)
        q_overlap = None
    elif sector == "even_qperp":
        k_even, _, _, q, h, transformed, a, compression, coupling = build_even_side(
            projected, N_2B
        )
        coeffs, eigenvalue, meta = bottom_eigenvector(compression, algorithm)
        # Map q-perp coordinates back to even-mode coordinates through H.
        t = arb_mat(N_2B + 1, 1)
        t[0, 0] = arb(0)
        for i in range(N_2B):
            t[i + 1, 0] = coeffs[i]
        mode_vec = h * t
        mode_coeffs = [mode_vec[i, 0] for i in range(N_2B + 1)]
        q_dot = sum((q[i] * mode_coeffs[i] for i in range(N_2B + 1)), arb(0))
        ledger = parity_split(mode_coeffs, lambda i: i)
        q_overlap = {"q_dot_vector": P1.bounds(q_dot), "contains_zero": bool(0 in q_dot)}
    else:
        raise SystemExit(f"unknown sector: {sector}")
    return {
        "cell": "vectors",
        "sector": sector,
        "N": N_2B,
        "dps": dps,
        "requested_algorithm": algorithm,
        "elapsed_seconds": time.time() - started,
        "bottom_eigenvalue_meta": meta,
        "parity_ledger": ledger,
        "q_overlap_check": q_overlap,
        "environment": environment_record(),
    }


def cell_error_record(kind: str, exc: Exception, **context: Any) -> dict[str, Any]:
    return {
        "cell": kind,
        "status": "CERT_NOT_FOUND",
        "error": repr(exc),
        **context,
        "environment": environment_record(),
    }


def load_cells(cells_dir: Path) -> dict[str, Any]:
    cells = {}
    for path in sorted(cells_dir.glob("*.json")):
        cells[path.stem] = json.loads(path.read_text(encoding="utf-8"))
    return cells


def stored_phase2_profile() -> dict[str, Any]:
    actual = sha256(PHASE2_RESULTS)
    if actual != EXPECTED_PHASE2_RESULTS_SHA256:
        raise SystemExit(f"Phase-2 results pin mismatch: {actual}")
    payload = json.loads(PHASE2_RESULTS.read_text(encoding="utf-8"))
    retained = {row["N"]: row["retained"] for row in payload["fixed_q_profile"]}
    return retained


def ball(record: dict[str, str]) -> arb:
    """Reparse a stored {ball, lower, upper} record as a containing enclosure."""
    return arb(record["ball"])


def classify_r3(r3: arb) -> tuple[str, str]:
    """Frozen decision rule applied to the r3 enclosure.

    A band verdict requires the WHOLE enclosure certified inside the band.
    Integer scaling by 100 is exact on dyadic endpoints, so the boundary
    comparisons are exact rational comparisons (0.84 = 84/100 etc.)."""
    scaled = r3 * 100
    lo = arb(scaled.lower())
    hi = arb(scaled.upper())
    if hi <= 84:
        return "POWER_LAW_WITNESS_DECAY", "r3 <= 0.84 certified"
    if lo >= 86 and hi <= 90:
        return "CONV_Q1", "0.86 <= r3 <= 0.90 certified"
    if lo >= 92:
        return "CONV_Q2PLUS", "r3 >= 0.92 certified"
    if lo > 84 and hi < 86:
        return "TRANSIENT", "r3 certified inside gap (0.84, 0.86); schedule N=960, same spec"
    if lo > 90 and hi < 92:
        return "TRANSIENT", "r3 certified inside gap (0.90, 0.92); schedule N=960, same spec"
    return (
        "TRANSIENT",
        "enclosure not certified inside any registered band (straddles a boundary); "
        "schedule N=960, same spec",
    )


def finalize(cells_dir: Path, output: Path) -> int:
    ctx.dps = FINALIZE_DPS
    ctx.threads = 1
    cells = load_cells(cells_dir)
    stored = stored_phase2_profile()

    failures = {
        name: cell for name, cell in cells.items() if cell.get("status") == "CERT_NOT_FOUND"
    }
    retained_name = "p480_d360_vdh"
    retained = cells.get(retained_name)
    verdict_class = None
    if retained is None:
        verdict_class = "CERT_NOT_FOUND"
        reason = f"retained production cell {retained_name} missing"
    elif retained.get("status") == "CERT_NOT_FOUND":
        verdict_class = "CERT_NOT_FOUND"
        reason = f"retained production cell failed: {retained['error']}"

    analysis: dict[str, Any] = {}
    if verdict_class is None:
        x0 = ball(stored[120]["beta_N_star"])
        x1 = ball(stored[240]["beta_N_star"])
        x2 = ball(retained["beta_N_star"])
        r2 = x1 / x0
        r3 = x2 / x1
        delta1 = x1 - x0
        delta2 = x2 - x1
        denom = delta2 - delta1  # x2 - 2*x1 + x0
        if 0 in denom:
            aitken = None
            aitken_status = "DENOMINATOR_CONTAINS_ZERO"
        else:
            aitken = x2 - delta2 * delta2 / denom
            aitken_status = "ENCLOSURE"
        band, band_reason = classify_r3(r3)
        verdict_class = band
        reason = band_reason
        analysis = {
            "x0_beta_star_120_stored": P1.bounds(x0),
            "x1_beta_star_240_stored": P1.bounds(x1),
            "x2_beta_star_480_retained": P1.bounds(x2),
            "r2_240_over_120": P1.bounds(r2),
            "r2_matches_registered_0_81085": bool(
                arb((r2 * 100000 - 81085).upper()) < 1
                and arb((r2 * 100000 - 81085).lower()) > -1
            ),
            "r3_480_over_240": P1.bounds(r3),
            "aitken_delta_sq_status": aitken_status,
            "aitken_beta_inf_estimate": None if aitken is None else P1.bounds(aitken),
            "aitken_denominator_x2_minus_2x1_plus_x0": P1.bounds(denom),
            "registered_reference_points": {
                "power_law_r3": "0.811 +/- 0.03",
                "q1_r3": "~0.883",
                "q1_beta_inf": "~1.900e-55",
                "q2plus_r3": "~0.942",
                "q2plus_beta_inf": "~2.285e-55",
            },
        }

    # a-invariance: N=480 production cells versus stored N=120/240 enclosures.
    a_invariance = {}
    if retained is not None and retained.get("status") != "CERT_NOT_FOUND":
        a480 = ball(retained["a"])
        for n in (120, 240):
            a_stored = ball(stored[n]["a"])
            a_invariance[f"a_480_overlaps_stored_a_{n}"] = bool(a480.overlaps(a_stored))
        a_invariance["a_480"] = P1.bounds(a480)

    # Cross-precision (180 vs 360) and cross-algorithm (vdh vs rump) consistency.
    def overlap_fields(first: dict[str, Any], second: dict[str, Any]) -> dict[str, bool]:
        out = {}
        for field in ("a", "beta_N_star", "beta_N_star_minus_a", "tau_required"):
            out[field] = P1.intervals_overlap(first[field], second[field])
        out["compression_floor"] = P1.intervals_overlap(
            first["compression_floor"]["floor"], second["compression_floor"]["floor"]
        )
        out["odd_floor"] = P1.intervals_overlap(
            first["odd_floor"]["floor"], second["odd_floor"]["floor"]
        )
        return out

    consistency: dict[str, Any] = {}
    pairs = [
        ("cross_precision_production", "p480_d180_vdh", "p480_d360_vdh"),
        ("cross_precision_independent", "p480_d180_rump", "p480_d360_rump"),
        ("cross_algorithm_dps180", "p480_d180_vdh", "p480_d180_rump"),
        ("cross_algorithm_dps360", "p480_d360_vdh", "p480_d360_rump"),
    ]
    for label, first, second in pairs:
        a_cell, b_cell = cells.get(first), cells.get(second)
        if (
            a_cell is None
            or b_cell is None
            or a_cell.get("status") == "CERT_NOT_FOUND"
            or b_cell.get("status") == "CERT_NOT_FOUND"
        ):
            consistency[label] = "UNAVAILABLE"
        else:
            consistency[label] = overlap_fields(a_cell, b_cell)

    # Reproduction cells versus stored Phase-2 enclosures (flint 0.9 vs 0.8).
    reproduction = {}
    for name, n, dps in (("p120_d180_vdh", 120, 180), ("p240_d360_vdh", 240, 360)):
        cell = cells.get(name)
        if cell is None or cell.get("status") == "CERT_NOT_FOUND":
            reproduction[name] = "UNAVAILABLE"
            continue
        stored_row = stored[n]
        if dps == 360:
            comparisons = {
                field: bool(ball(cell[field]).overlaps(ball(stored_row[field])))
                for field in ("a", "beta_N_star", "beta_N_star_minus_a", "tau_required")
            }
        else:
            # stored retained rows are 360 dps; compare source quantities only
            comparisons = {
                field: bool(ball(cell[field]).overlaps(ball(stored_row[field])))
                for field in ("a", "beta_N_star")
            }
        reproduction[name] = {
            "against_stored_retained_360dps": comparisons,
            "interval_certificate_pass": cell["interval_certificate_pass"],
        }

    # Interlacing ledger: odd_240 is the leading principal 240x240 submatrix of
    # odd_480 (entries are N-independent), so Cauchy gives
    # lambda_k(odd_480) <= lambda_k(odd_240).
    interlacing = {}
    p240 = cells.get("p240_d360_vdh")
    if (
        retained is not None
        and retained.get("status") != "CERT_NOT_FOUND"
        and p240 is not None
        and p240.get("status") != "CERT_NOT_FOUND"
    ):
        rows = []
        for k in range(BOTTOM_K):
            l480 = ball(retained["odd_floor"]["bottom_k"][k])
            l240 = ball(p240["odd_floor"]["bottom_k"][k])
            rows.append({
                "k": k + 1,
                "lambda_k_odd_480": P1.bounds(l480),
                "lambda_k_odd_240": P1.bounds(l240),
                "certified_strict_lambda_k_480_lt_lambda_k_240": bool(
                    l480.upper() < l240.lower()
                ),
                "cauchy_consistent_lambda_k_480_le_lambda_k_240": bool(
                    l480.lower() <= l240.upper()
                ),
            })
        compr480 = ball(retained["compression_floor"]["floor"])
        compr240_stored = ball(stored[240]["compression_floor"]["floor"])
        interlacing = {
            "odd_sector_bottom_k": rows,
            "even_qperp_floor_480": P1.bounds(compr480),
            "even_qperp_floor_240_stored": P1.bounds(compr240_stored),
            "certified_strict_even_qperp_floor_480_lt_240": bool(
                compr480.upper() < compr240_stored.lower()
            ),
        }

    # Parity ledger assembly.
    parity = {}
    if retained is not None and retained.get("status") != "CERT_NOT_FOUND":
        parity["binding_sector_480"] = retained["controlling_sector"]
        parity["binding_sector_expected"] = "ODD_SECTOR"
    for name, label in (
        ("vec_odd", "bottom_odd_sector_vector"),
        ("vec_even_qperp", "bottom_even_qperp_vector"),
    ):
        cell = cells.get(name)
        if cell is None:
            parity[label] = "UNAVAILABLE"
        elif cell.get("status") == "CERT_NOT_FOUND":
            parity[label] = {"status": "ENCLOSURE_UNAVAILABLE", "error": cell["error"]}
        else:
            parity[label] = {
                "bottom_eigenvalue": cell["bottom_eigenvalue_meta"]["eigenvalue"],
                "algorithm_used": cell["bottom_eigenvalue_meta"]["algorithm_used"],
                **cell["parity_ledger"],
                **({"q_overlap_check": cell["q_overlap_check"]} if cell["q_overlap_check"] else {}),
            }

    result = {
        "schema": "CCMFixedQBetaN480Aitken.v1",
        "task": "RUN_DELTA_N480_AITKEN (batch rank 1, Phase 2B, cell m=13)",
        "verdict_class": verdict_class,
        "verdict_reason": reason,
        "route": "CHALLENGER_NOT_RH",
        "promotion": "FORBIDDEN",
        "bus_010": "VOID",
        "goal_055": "HOLD",
        "px_rh_claim": "NOT_MADE",
        "precommit": {
            "lambda": "sqrt(13)",
            "m": 13,
            "N0": P2.N0,
            "N": N_2B,
            "dimension": 2 * N_2B + 1,
            "q": "SAME fixed q in E_120 as Phase 2 (SHA-pinned through Phase-1 loader)",
            "embedding": "literal zero-padding only; no profile re-optimization",
            "precision_dps": list(PRECISIONS),
            "beta_initial_bracket": ["0", "1e-48"],
            "beta_search_tolerance": "max(1e-100, 2^-40 * current_upper_bracket)",
            "production_eigen_algorithm": PRODUCTION_ALGORITHM,
            "independent_eigen_algorithm": INDEPENDENT_ALGORITHM,
            "aitken_inputs": "stored Phase-2 360-dps enclosures for beta*_120, beta*_240",
            "decision_rule_verbatim": DECISION_RULE_VERBATIM,
            "no_schedule_changes_after_results": "K6/C09",
        },
        "implementation": {
            "phase2_script": str(PHASE2_SCRIPT.relative_to(REPO)),
            "phase2_script_sha256": EXPECTED_PHASE2_SHA256,
            "phase2_results_sha256": EXPECTED_PHASE2_RESULTS_SHA256,
            "phase1_script_sha256": P2.EXPECTED_PHASE1_SHA256,
            "q_source_sha256": P1.EXPECTED_Q_SHA256,
            "this_script": "docs/routeB_bus/phase2b_scripts/ccm_beta_n480_aitken.py",
        },
        "environment": environment_record(),
        "analysis": analysis,
        "a_invariance_zero_padding_control": a_invariance,
        "consistency": consistency,
        "reproduction_control_cells": reproduction,
        "interlacing_vs_240": interlacing,
        "parity_ledger": parity,
        "cert_not_found_cells": {k: v.get("error") for k, v in failures.items()},
        "cells": cells,
        "semantic_boundary": (
            "finite_fixed_q_profile_only; no_continuum_transfer; not_SlotH2a; not_RH; "
            "no_Lean_edits; no_goal_closure_claims"
        ),
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text, encoding="utf-8")
    print(f"verdict_class={verdict_class} reason={reason}", file=sys.stderr)
    return 0 if verdict_class not in ("CERT_NOT_FOUND",) else 2


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cell", required=True,
                        choices=["profile", "vectors", "finalize"])
    parser.add_argument("--N", type=int, default=N_2B)
    parser.add_argument("--dps", type=int, default=360)
    parser.add_argument("--algorithm", default=PRODUCTION_ALGORITHM)
    parser.add_argument("--sector", choices=["odd", "even_qperp"])
    parser.add_argument("--cells-dir", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    if args.cell == "finalize":
        if args.cells_dir is None:
            raise SystemExit("finalize requires --cells-dir")
        return finalize(args.cells_dir, args.output)

    ctx.dps = 80
    projected, _q_meta = P1.q_source_exact_even()
    try:
        if args.cell == "profile":
            record = run_profile_cell(projected, args.N, args.dps, args.algorithm)
        else:
            if args.sector is None:
                raise SystemExit("vectors cell requires --sector")
            record = run_vectors_cell(projected, args.sector, args.dps, args.algorithm)
    except (RuntimeError, ValueError, ZeroDivisionError) as exc:
        record = cell_error_record(
            args.cell, exc, N=args.N, dps=args.dps,
            algorithm=args.algorithm, sector=args.sector,
        )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    status = record.get("status", "OK")
    print(f"[phase2b] cell={args.cell} N={args.N} dps={args.dps} "
          f"alg={args.algorithm} sector={args.sector} status={status}",
          file=sys.stderr, flush=True)
    return 0 if status == "OK" else 2


if __name__ == "__main__":
    raise SystemExit(main())
