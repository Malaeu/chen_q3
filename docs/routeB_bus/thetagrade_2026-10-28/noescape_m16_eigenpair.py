#!/usr/bin/env python3
"""Cache the literal m=N=16 even-sector ground and second eigenpairs.

This is finite numerical input only: DIAGNOSTIC_NEVER_A_PROOF and
CHALLENGER_NOT_RH.  The Arb matrix/eigenpair follows the existing
CCMArbBuilder + resolve_eigenpair path.  A separate high-precision mpmath
comparison checks every even-block entry against the original full K matrix;
that comparison is diagnostic and is not used to certify the Arb result.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
import time
from pathlib import Path
from typing import Any

sys.dont_write_bytecode = True

from flint import acb_mat, arb, ctx  # noqa: E402
import mpmath as mp  # noqa: E402

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PHASE5 = ROOT / "docs/routeB_bus/phase5_scripts"
FOKAS = ROOT / "docs/routeB_bus/fokas_k_sign_2026-09-25"
sys.path.insert(0, str(PHASE5))
sys.path.insert(0, str(FOKAS))

import edge_ledger_build as edge  # noqa: E402
import full_center_probe as full_probe  # noqa: E402
from parity_gap_table import parity_bases  # noqa: E402

M = 16
N = 16
BASE_DPS = 120
MPCHECK_DPS = 160
ENTRYWISE_TOLERANCE = mp.mpf("1e-50")
OUTPUT = HERE / "noescape_m16_eigenpair.json"


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def arb_ball(value: arb) -> dict[str, str]:
    return {
        "ball": str(value),
        "lower": str(value.lower()),
        "upper": str(value.upper()),
    }


def arb_mid_as_mp(value: arb, digits: int) -> mp.mpf:
    return mp.mpf(value.mid().str(digits, radius=False))


def entrywise_source_crosscheck(matrix: Any, actual_dps: int) -> dict[str, Any]:
    """Compare Arb-builder midpoints with E.T * full-center K * E (diagnostic)."""
    mp.mp.dps = MPCHECK_DPS
    full_k = full_probe.matrix_K(M)
    even_basis, _odd_basis = parity_bases(M)
    compressed = even_basis.T * full_k * even_basis
    differences: list[mp.mpf] = []
    scales: list[mp.mpf] = []
    for i in range(N + 1):
        for j in range(N + 1):
            builder_mid = arb_mid_as_mp(matrix[i, j], MPCHECK_DPS)
            reference = compressed[i, j]
            differences.append(abs(builder_mid - reference))
            scales.append(abs(reference))
    max_abs = max(differences)
    max_scale = max(scales)
    max_rel = max_abs / max_scale if max_scale else mp.mpf(0)
    entry_count = (N + 1) ** 2
    within_tolerance = sum(diff <= ENTRYWISE_TOLERANCE for diff in differences)
    return {
        "status": "DIAGNOSTIC_ONLY_NOT_CERTIFICATION",
        "reference": "full_center_probe.matrix_K(16), compressed by parity_gap_table.parity_bases(16).E",
        "builder_midpoint_precision_dps": actual_dps,
        "mpmath_precision_dps": MPCHECK_DPS,
        "mpmath_quadrature_is_not_rigorous": True,
        "entries_compared": entry_count,
        "entries_with_abs_difference_at_most_1e-50": within_tolerance,
        "entrywise_tolerance": mp.nstr(ENTRYWISE_TOLERANCE, 8),
        "max_abs_midpoint_difference": mp.nstr(max_abs, 30),
        "max_relative_midpoint_difference_using_max_reference_entry": mp.nstr(max_rel, 30),
        "max_reference_entry_abs": mp.nstr(max_scale, 30),
        "all_entries_within_tolerance": within_tolerance == entry_count,
    }


def vector_records(values: list[arb]) -> list[dict[str, str]]:
    return [arb_ball(value) for value in values]


def main(output: Path = OUTPUT) -> int:
    started = time.perf_counter()
    ctx.dps = BASE_DPS
    ctx.threads = 1
    captured: dict[str, Any] = {}

    def build_matrix() -> Any:
        captured["matrix"] = edge.CCMArbBuilder(M, N).even_block()
        return captured["matrix"]

    print(f"building and isolating m=N={M}, even dimension {N + 1} at dps={BASE_DPS}", flush=True)
    result = edge.resolve_eigenpair(build_matrix, N + 1, BASE_DPS, want_vectors=True)
    matrix = captured["matrix"]
    actual_dps = BASE_DPS + int(result["bump"])
    ctx.dps = actual_dps
    ctx.threads = 1

    lam0: arb = result["lambda1"]
    lam1: arb = result["lambda2"]
    vec0: list[arb] = result["vec1"]
    vec1: list[arb] = result["vec2"]
    if vec0 is None or vec1 is None or len(vec1) != N + 1:
        raise RuntimeError("resolve_eigenpair did not return the requested full-spectrum eigenvectors")

    # Keep a full-spectrum readback so the zero-based second index is checked
    # against the third as well as the ground eigenvalue. This is the same
    # validated python-flint eig API and algorithm selected by resolve_eigenpair.
    spectrum_c, _right_c = acb_mat(matrix).eig(right=True, algorithm=result["method"])
    if len(spectrum_c) != N + 1:
        raise RuntimeError(f"full spectrum has {len(spectrum_c)} values, expected {N + 1}")
    ordered = sorted(spectrum_c, key=lambda value: float(value.real.mid()))
    if any(0 not in value.imag for value in ordered):
        raise RuntimeError("full-spectrum readback contains an eigenvalue not enclosing the real axis")
    ordered_real = [value.real for value in ordered]
    if not (ordered_real[0].upper() < ordered_real[1].lower()):
        raise RuntimeError("ground and second eigenvalue balls are not strictly separated")
    if not (ordered_real[1].upper() < ordered_real[2].lower()):
        raise RuntimeError("second and third eigenvalue balls are not strictly separated")
    if not (lam0.overlaps(ordered_real[0]) and lam1.overlaps(ordered_real[1])):
        raise RuntimeError("resolve_eigenpair outputs do not overlap the sorted full-spectrum readback")

    def residual(vec: list[arb], lam: arb) -> list[arb]:
        return [
            sum((matrix[i, j] * vec[j] for j in range(N + 1)), arb(0)) - lam * vec[i]
            for i in range(N + 1)
        ]

    residual0 = residual(vec0, lam0)
    residual1 = residual(vec1, lam1)
    norm2_0 = sum((entry * entry for entry in vec0), arb(0))
    norm2_1 = sum((entry * entry for entry in vec1), arb(0))
    ground_residuals_contain_zero = all(0 in item for item in residual0)
    ground_norm2_strictly_positive = norm2_0.lower() > 0
    ground_norm2_encloses_one = 1 in norm2_0
    residuals_contain_zero = all(0 in item for item in residual1)
    normalization_encloses_one = 1 in norm2_1
    if not ground_residuals_contain_zero:
        raise RuntimeError("ground eigenpair residual interval failed to contain zero componentwise")
    if not ground_norm2_strictly_positive:
        raise RuntimeError("ground eigenvector norm-squared interval is not strictly positive")
    if not ground_norm2_encloses_one:
        raise RuntimeError("ground eigenvector norm-squared interval failed to enclose 1")
    if not residuals_contain_zero:
        raise RuntimeError("second eigenpair residual interval failed to contain zero componentwise")
    if not normalization_encloses_one:
        raise RuntimeError("second eigenvector norm-squared interval failed to enclose 1")

    ground_norm = norm2_0.sqrt()
    normalized_ground_vec = [entry / ground_norm for entry in vec0]
    normalized_ground_norm2 = sum(
        (entry * entry for entry in normalized_ground_vec), arb(0)
    )
    normalized_ground_norm2_encloses_one = 1 in normalized_ground_norm2
    if not normalized_ground_norm2_encloses_one:
        raise RuntimeError("interval-normalized ground vector norm-squared failed to enclose 1")

    print("running entrywise diagnostic comparison against full_center_probe.matrix_K(16)", flush=True)
    crosscheck = entrywise_source_crosscheck(matrix, actual_dps)
    if not crosscheck["all_entries_within_tolerance"]:
        raise RuntimeError(
            "builder/full-K diagnostic mismatch: only "
            f"{crosscheck['entries_with_abs_difference_at_most_1e-50']}/"
            f"{crosscheck['entries_compared']} entries met the diagnostic tolerance"
        )

    even_vector = vector_records(vec1)
    full_vector = vector_records(edge.even_to_pm_row(vec1, N))
    ground_even_vector = vector_records(vec0)
    ground_full_vector = vector_records(edge.even_to_pm_row(vec0, N))
    normalized_ground_even_vector = vector_records(normalized_ground_vec)
    normalized_ground_full_vector = vector_records(
        edge.even_to_pm_row(normalized_ground_vec, N)
    )
    source_paths = {
        "this_script": Path(__file__).resolve(),
        "edge_ledger_build.py": PHASE5 / "edge_ledger_build.py",
        "phase1_ccm_control_cell_penalty.py": ROOT / "docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py",
        "full_center_probe.py": FOKAS / "full_center_probe.py",
        "parity_gap_table.py": HERE / "parity_gap_table.py",
    }
    elapsed = time.perf_counter() - started
    payload = {
        "status": "FINITE_EIGENPAIR_INPUT_DIAGNOSTIC_NEVER_A_PROOF",
        "route_status": "CHALLENGER_NOT_RH",
        "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
        "scope": "literal CCM even block m=N=16 only; no F/X or RH certificate",
        "operator": {
            "name": "CCMArbBuilder(16,16).even_block()",
            "dimension": N + 1,
            "parity_basis": "e_0, (e_i + e_-i)/sqrt(2), i=1..16",
            "source_crosscheck": crosscheck,
        },
        "eigensolver": {
            "path": "edge_ledger_build.resolve_eigenpair -> robust_eig -> acb_mat.eig(right=True)",
            "method": result["method"],
            "base_dps": BASE_DPS,
            "precision_bump": result["bump"],
            "actual_dps": actual_dps,
            "threads": 1,
            "spectrum_size": len(spectrum_c),
            "ordering": "ascending by real midpoint; returned index i=1 is zero-based second eigenpair",
            "first_three_real_eigenvalue_balls": [arb_ball(value) for value in ordered_real[:3]],
            "first_second_strictly_separated": True,
            "second_third_strictly_separated": True,
            "ground_eigenvalue": arb_ball(lam0),
            "ground_residual_componentwise_contains_zero": ground_residuals_contain_zero,
            "ground_residual_components": vector_records(residual0),
            "selected_eigenvalue_i1": arb_ball(lam1),
            "selected_index_zero_based": 1,
            "residual_enclosure_componentwise_contains_zero": residuals_contain_zero,
            "selected_residual_components": vector_records(residual1),
            "ground_norm_squared_ball": arb_ball(norm2_0),
            "ground_norm_squared_strictly_positive": ground_norm2_strictly_positive,
            "ground_norm_squared_encloses_one": ground_norm2_encloses_one,
            "selected_norm_squared_ball": arb_ball(norm2_1),
            "selected_norm_squared_encloses_one": normalization_encloses_one,
            "normalization_note": "No post-hoc rescaling; stores the eigensolver vector and its Arb norm-squared enclosure.",
        },
        "selected_eigenvector": {
            "even_basis_coordinates": even_vector,
            "fourier_modes_minus16_to_plus16": full_vector,
            "mode_order": list(range(-N, N + 1)),
            "map": "c_0=xi_0 and c_{+/-j}=xi_j/sqrt(2)",
        },
        "ground_eigenvector": {
            "selected_index_zero_based": 0,
            "eigenvalue": arb_ball(lam0),
            "raw": {
                "even_basis_coordinates": ground_even_vector,
                "fourier_modes_minus16_to_plus16": ground_full_vector,
                "mode_order": list(range(-N, N + 1)),
                "map": "c_0=xi_0 and c_{+/-j}=xi_j/sqrt(2)",
            },
            "normalization": {
                "method": "divide each coordinate by the square root of its Arb norm-squared enclosure",
                "raw_norm_squared": arb_ball(norm2_0),
                "raw_norm_squared_strictly_positive": ground_norm2_strictly_positive,
                "factor": arb_ball(ground_norm),
            },
            "interval_normalized": {
                "even_basis_coordinates": normalized_ground_even_vector,
                "fourier_modes_minus16_to_plus16": normalized_ground_full_vector,
                "mode_order": list(range(-N, N + 1)),
                "map": "c_0=xi_0 and c_{+/-j}=xi_j/sqrt(2)",
                "norm_squared": arb_ball(normalized_ground_norm2),
                "norm_squared_encloses_one": normalized_ground_norm2_encloses_one,
            },
            "validation": {
                "raw_residual_componentwise_contains_zero": ground_residuals_contain_zero,
                "raw_residual_components": vector_records(residual0),
                "raw_norm_squared_encloses_one": ground_norm2_encloses_one,
                "normalized_norm_squared_encloses_one": normalized_ground_norm2_encloses_one,
                "residual_note": "Componentwise interval containment of zero is a residual enclosure check only; by itself it does not prove a common exact eigenpair.",
            },
        },
        "runtime": {
            "python": platform.python_version(),
            "python_flint": getattr(__import__("flint"), "__version__", "unknown"),
            "mpmath": mp.__version__,
            "seconds_total_including_crosscheck": round(elapsed, 3),
        },
        "source_sha256": {name: file_sha256(path) for name, path in source_paths.items()},
        "limitations": [
            "This is one finite even-sector eigenpair and supplies no uniform-in-m input.",
            "The mpmath matrix comparison is floating-point diagnostics, not a rigorous source identity proof.",
            "A finite numerical eigenpair supplies no F/X consumer bound and proves no statement about RH.",
            "The selected vector is an Arb enclosure returned by python-flint; its norm-squared ball is recorded without rescaling.",
        ],
    }
    output.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, ensure_ascii=False), flush=True)
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=OUTPUT,
        help=f"write the JSON payload here (default: {OUTPUT})",
    )
    raise SystemExit(main(parser.parse_args().output))
