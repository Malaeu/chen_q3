#!/usr/bin/env python3
"""Finite effective-resistance diagnostic for literal even CCM eigenvectors.

Builds the full source matrix with full_center_probe.matrix_K, compresses it
with parity_gap_table.parity_bases(m).E, then forms the signed graph
w_ij=-A_ij*c_i*c_j for the bottom and first excited real eigenvectors.
All graph decisions use mpmath values and omit exactly zero weights only.
This is numerical evidence for finite m, not a source certificate or proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import signal
import sys
import time
from collections import deque
from pathlib import Path
from typing import Any

import mpmath as mp

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
FOKAS = HERE.parents[0] / "fokas_k_sign_2026-09-25"
sys.path.insert(0, str(FOKAS))
sys.path.insert(0, str(HERE))

import full_center_probe as full_probe  # noqa: E402
from parity_gap_table import parity_bases  # noqa: E402

OUTPUT = HERE / "noescape_resistance_probe.json"
CELL_TIME_CAP_SECONDS = 180
DEFAULT_DPS = 70
ADAPTIVE_DPS = 90
PRINT_DIGITS = 45


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def number(value: mp.mpf, digits: int = PRINT_DIGITS) -> str:
    if value == mp.inf:
        return "Infinity"
    if value == -mp.inf:
        return "-Infinity"
    if mp.isnan(value):
        return "NaN"
    return mp.nstr(value, digits)


def vector_norm(values: list[mp.mpf]) -> mp.mpf:
    return mp.sqrt(mp.fsum(value * value for value in values))


def matrix_residual(A: mp.matrix, c: list[mp.mpf], eigenvalue: mp.mpf) -> mp.mpf:
    residual = [
        mp.fsum(A[i, j] * c[j] for j in range(A.cols)) - eigenvalue * c[i]
        for i in range(A.rows)
    ]
    return vector_norm(residual)


def displacement_record(
    A: mp.matrix, c: list[mp.mpf], eigenvalue: mp.mpf, m: int, residual_norm: mp.mpf
) -> dict[str, Any]:
    """Cross-check the i^2 multiplier against the source commutator formula."""
    indices_squared = [mp.mpf(i * i) for i in range(m + 1)]
    y = [indices_squared[i] * c[i] for i in range(m + 1)]
    y_norm_squared = mp.fsum(value * value for value in y)
    residual = [
        mp.fsum(A[i, j] * c[j] for j in range(m + 1)) - eigenvalue * c[i]
        for i in range(m + 1)
    ]
    qx = mp.fsum(
        y[i]
        * (mp.fsum(A[i, j] * y[j] for j in range(m + 1)) - eigenvalue * y[i])
        for i in range(m + 1)
    )

    d = [mp.mpf(1)] + [mp.sqrt(2) for _ in range(m)]
    F = [mp.mpf(0)] + [mp.mpf(i * i) * A[0, i] / mp.sqrt(2) for i in range(1, m + 1)]
    delta = (
        mp.fsum(d[i] * indices_squared[i] * c[i] for i in range(m + 1))
        * mp.fsum(d[i] * F[i] * c[i] for i in range(m + 1))
        - mp.fsum(d[i] * c[i] for i in range(m + 1))
        * mp.fsum(d[i] * F[i] * indices_squared[i] * c[i] for i in range(m + 1))
    )
    graph_sum = mp.fsum(
        (-A[i, j] * c[i] * c[j]) * (indices_squared[i] - indices_squared[j]) ** 2
        for i in range(m + 1)
        for j in range(i + 1, m + 1)
    )
    residual_correction = mp.fsum(
        indices_squared[i] ** 2 * c[i] * residual[i] for i in range(m + 1)
    )
    residual_bound = mp.mpf(m) ** 4 * residual_norm
    return {
        "direction": "X=diag(i^2), y=Xc, i=0..m",
        "direct_Qx": number(qx),
        "direction_norm_squared": number(y_norm_squared),
        "normalized_energy_shift_Qx_over_norm_squared": number(qx / y_norm_squared) if y_norm_squared else None,
        "commutator_delta_from_F_i_i_beta_i": number(delta),
        "signed_graph_weighted_square_sum": number(graph_sum),
        "Qx_minus_delta": number(qx - delta),
        "residual_correction_sum_i4_c_i_r_i": number(residual_correction),
        "Qx_minus_delta_minus_residual_correction": number(qx - delta - residual_correction),
        "delta_minus_graph_weighted_square_sum": number(delta - graph_sum),
        "eigenpair_residual_l2": number(residual_norm),
        "m4_times_residual_l2_bound": number(residual_bound),
        "abs_Qx_minus_delta_within_m4_residual_bound_numerically": bool(abs(qx - delta) <= residual_bound),
        "source_formula": (
            "F_0=0; F_i=i^2*A_0i/sqrt(2) for i>0, from A_0i=sqrt(2)*beta_i/i; "
            "d_0=1 and d_i=sqrt(2) for i>0; Delta=(sum d_i*i^2*c_i)(sum d_i*F_i*c_i)"
            "-(sum d_i*c_i)(sum d_i*F_i*i^2*c_i)."
        ),
        "status": "finite algebraic consistency check; no new source identity or proof claim",
    }


def positive_components(
    n: int, positive_edges: list[tuple[int, int, mp.mpf]]
) -> tuple[list[list[int]], list[int]]:
    adjacency: list[list[int]] = [[] for _ in range(n)]
    for p, q, _conductance in positive_edges:
        adjacency[p].append(q)
        adjacency[q].append(p)

    components: list[list[int]] = []
    component_of = [-1] * n
    for start in range(n):
        if component_of[start] >= 0:
            continue
        component_id = len(components)
        component_of[start] = component_id
        queue = deque([start])
        component: list[int] = []
        while queue:
            vertex = queue.popleft()
            component.append(vertex)
            for neighbor in adjacency[vertex]:
                if component_of[neighbor] < 0:
                    component_of[neighbor] = component_id
                    queue.append(neighbor)
        components.append(sorted(component))
    return components, component_of


def grounded_resistance(
    component: list[int],
    positive_edges: list[tuple[int, int, mp.mpf]],
    p: int,
    q: int,
) -> tuple[mp.mpf, mp.mpf]:
    """Solve a grounded mpmath Laplacian system; no pseudoinverse is used."""
    ground = component[-1]
    free = [vertex for vertex in component if vertex != ground]
    local = {vertex: index for index, vertex in enumerate(free)}
    grounded = mp.zeros(len(free))
    for u, v, conductance in positive_edges:
        if u not in local and u != ground:
            continue
        if v not in local and v != ground:
            continue
        if u in local:
            grounded[local[u], local[u]] += conductance
        if v in local:
            grounded[local[v], local[v]] += conductance
        if u in local and v in local:
            grounded[local[u], local[v]] -= conductance
            grounded[local[v], local[u]] -= conductance

    rhs = mp.matrix(len(free), 1)
    if p != ground:
        rhs[local[p]] += 1
    if q != ground:
        rhs[local[q]] -= 1
    solution = mp.lu_solve(grounded, rhs)
    resistance = mp.fsum(rhs[i] * solution[i] for i in range(len(free)))
    residual = mp.sqrt(
        mp.fsum(
            (mp.fsum(grounded[i, j] * solution[j] for j in range(len(free))) - rhs[i]) ** 2
            for i in range(len(free))
        )
    )
    if not resistance > 0:
        raise ArithmeticError(f"grounded solve returned nonpositive resistance for edge {(p, q)}")
    return resistance, residual


def graph_record(
    A: mp.matrix, c: list[mp.mpf], residual_norm: mp.mpf
) -> dict[str, Any]:
    n = len(c)
    positive_edges: list[tuple[int, int, mp.mpf]] = []
    negative_edges: list[tuple[int, int, mp.mpf]] = []
    zero_edge_count = 0
    nonzero_edge_weights: list[mp.mpf] = []
    for p in range(n):
        for q in range(p + 1, n):
            w = -A[p, q] * c[p] * c[q]
            if w == 0:
                zero_edge_count += 1
                continue
            nonzero_edge_weights.append(abs(w))
            if w > 0:
                positive_edges.append((p, q, w))
            else:
                negative_edges.append((p, q, -w))

    degrees = [mp.mpf(0) for _ in range(n)]
    for p, q, conductance in positive_edges:
        degrees[p] += conductance
        degrees[q] += conductance

    components, component_of = positive_components(n, positive_edges)
    edges: list[dict[str, Any]] = []
    max_solve_residual = mp.mpf(0)
    for p, q, alpha in negative_edges:
        endpoint_score = (
            mp.inf
            if degrees[p] == 0 or degrees[q] == 0
            else alpha * (1 / degrees[p] + 1 / degrees[q])
        )
        if component_of[p] != component_of[q]:
            resistance = mp.inf
            inverse_resistance = mp.mpf(0)
            solve_residual = mp.mpf(0)
            component_status = "endpoints_in_distinct_positive_components"
        else:
            resistance, solve_residual = grounded_resistance(
                components[component_of[p]], positive_edges, p, q
            )
            inverse_resistance = 1 / resistance
            component_status = "same_positive_component_grounded_solve"
            max_solve_residual = max(max_solve_residual, solve_residual)
        ratio = alpha * resistance
        margin = alpha - inverse_resistance
        edges.append(
            {
                "edge": [p, q],
                "negative_weight": number(-alpha),
                "alpha": number(alpha),
                "positive_component_status": component_status,
                "positive_component_id_p": component_of[p],
                "positive_component_id_q": component_of[q],
                "effective_resistance": number(resistance),
                "alpha_times_resistance": number(ratio),
                "inverse_resistance": number(inverse_resistance),
                "alpha_minus_inverse_resistance": number(margin),
                "positive_degree_p": number(degrees[p]),
                "positive_degree_q": number(degrees[q]),
                "endpoint_score_alpha_times_reciprocal_degree_sum": number(endpoint_score),
                "grounded_solve_residual_l2": number(solve_residual),
                "single_edge_overload_numerically": bool(ratio > 1),
                "overload_margin_exceeds_eigenpair_residual": bool(margin > residual_norm),
                "margin_minus_eigenpair_residual": number(margin - residual_norm),
            }
        )

    # Keep the calculation itself in mp arithmetic when selecting the edge.
    ratios = [mp.mpf(row["alpha_times_resistance"]) if row["alpha_times_resistance"] not in ("Infinity", "-Infinity", "NaN") else mp.inf for row in edges]
    margins = [mp.mpf(row["alpha_minus_inverse_resistance"]) for row in edges]
    endpoint_scores = [
        mp.mpf(row["endpoint_score_alpha_times_reciprocal_degree_sum"])
        if row["endpoint_score_alpha_times_reciprocal_degree_sum"] not in ("Infinity", "-Infinity", "NaN")
        else mp.inf
        for row in edges
    ]
    ratio_index = max(range(len(ratios)), key=ratios.__getitem__) if ratios else None
    margin_index = max(range(len(margins)), key=margins.__getitem__) if margins else None
    endpoint_index = max(range(len(endpoint_scores)), key=endpoint_scores.__getitem__) if endpoint_scores else None
    selected_by_ratio = edges[ratio_index] if ratio_index is not None else None
    selected_by_margin = edges[margin_index] if margin_index is not None else None
    selected_by_endpoint = edges[endpoint_index] if endpoint_index is not None else None

    coordinates = [abs(value) for value in c if value != 0]
    return {
        "positive_edge_count": len(positive_edges),
        "negative_edge_count": len(negative_edges),
        "exactly_zero_edge_count": zero_edge_count,
        "positive_component_count": len(components),
        "positive_component_sizes": [len(component) for component in components],
        "positive_weighted_degrees": [number(value) for value in degrees],
        "minimum_nonzero_abs_coordinate": number(min(coordinates)) if coordinates else None,
        "minimum_nonzero_abs_edge_weight": number(min(nonzero_edge_weights)) if nonzero_edge_weights else None,
        "maximum_nonzero_abs_edge_weight": number(max(nonzero_edge_weights)) if nonzero_edge_weights else None,
        "maximum_alpha_times_resistance": number(max(ratios)) if ratios else None,
        "edge_maximizing_alpha_times_resistance": selected_by_ratio["edge"] if selected_by_ratio else None,
        "alpha_minus_inverse_resistance_at_ratio_maximum": selected_by_ratio["alpha_minus_inverse_resistance"] if selected_by_ratio else None,
        "maximum_alpha_minus_inverse_resistance": number(max(margins)) if margins else None,
        "edge_maximizing_alpha_minus_inverse_resistance": selected_by_margin["edge"] if selected_by_margin else None,
        "maximum_endpoint_score_alpha_times_reciprocal_degree_sum": number(max(endpoint_scores)) if endpoint_scores else None,
        "edge_maximizing_endpoint_score": selected_by_endpoint["edge"] if selected_by_endpoint else None,
        "any_single_edge_overload_numerically": any(value > 1 for value in ratios),
        "any_overload_margin_exceeds_eigenpair_residual": any(margin > residual_norm for margin in margins),
        "maximum_grounded_solve_residual_l2": number(max_solve_residual),
        "negative_edges": edges,
        "endpoint_score_note": (
            "Computed as alpha*(1/Dp+1/Dq), Dp=sum of incident positive conductances. "
            "For an exact bottom the two-coordinate principal minor makes this score <= 1; "
            "the full positive-network resistance is computed independently above."
        ),
    }


def compute_cell(m: int, dps: int) -> dict[str, Any]:
    started = time.perf_counter()
    with mp.workdps(dps):
        full_k = full_probe.matrix_K(m)
        even_basis, _odd_basis = parity_bases(m)
        A = even_basis.T * full_k * even_basis
        eigenvalues, eigenvectors = mp.eigsy(A)
        if len(eigenvalues) < 2:
            raise ArithmeticError("even block has no first excited eigenpair")

        eigenpair_records: list[dict[str, Any]] = []
        graph_records: dict[str, Any] = {}
        residuals: list[mp.mpf] = []
        for index, label in ((0, "bottom"), (1, "first_excited")):
            raw = [eigenvectors[i, index] for i in range(A.rows)]
            raw_norm = vector_norm(raw)
            if raw_norm == 0:
                raise ArithmeticError(f"mpmath eigsy returned zero vector for {label}")
            c = [value / raw_norm for value in raw]
            norm = vector_norm(c)
            residual = matrix_residual(A, c, eigenvalues[index])
            residuals.append(residual)
            eigenpair_records.append(
                {
                    "label": label,
                    "eigenvalue_index_zero_based": index,
                    "eigenvalue": number(eigenvalues[index]),
                    "norm_l2": number(norm),
                    "residual_l2": number(residual),
                    "coordinates": [number(value) for value in c],
                    "i_squared_direction": displacement_record(A, c, eigenvalues[index], m, residual),
                }
            )
            graph_records[label] = graph_record(A, c, residual)

        gap = eigenvalues[1] - eigenvalues[0]
        if gap <= 0:
            raise ArithmeticError("eigensolver did not return a strictly ordered bottom and first excited value")
        coordinate_scale = [
            abs(mp.mpf(value))
            for item in eigenpair_records
            for value in item["coordinates"]
            if mp.mpf(value) != 0
        ]
        tolerance = mp.power(10, -mp.mpf(dps) / 2)
        concerns: list[str] = []
        if max(residuals) / gap > tolerance:
            concerns.append("eigenpair residual is not small relative to the even-sector spectral gap")
        if coordinate_scale and min(coordinate_scale) / max(coordinate_scale) < tolerance:
            concerns.append("nonzero eigenvector coordinates span more than half the working digits")
        edge_scales = [
            (mp.mpf(graph_records[label]["minimum_nonzero_abs_edge_weight"]),
             mp.mpf(graph_records[label]["maximum_nonzero_abs_edge_weight"]))
            for label in ("bottom", "first_excited")
            if graph_records[label]["minimum_nonzero_abs_edge_weight"] is not None
        ]
        if edge_scales and min(lo / hi for lo, hi in edge_scales) < tolerance:
            concerns.append("nonzero graph weights/degrees span more than half the working digits")
        for label in ("bottom", "first_excited"):
            ratio = graph_records[label]["maximum_alpha_times_resistance"]
            if ratio not in (None, "Infinity", "-Infinity", "NaN") and abs(mp.mpf(ratio) - 1) < tolerance:
                concerns.append(f"{label} maximum alpha*R is too close to the strict threshold 1")
            endpoint = graph_records[label]["maximum_endpoint_score_alpha_times_reciprocal_degree_sum"]
            if endpoint not in (None, "Infinity", "-Infinity", "NaN") and abs(mp.mpf(endpoint) - 1) < tolerance:
                concerns.append(f"{label} endpoint score is too close to the strict threshold 1")

        return {
            "status": "FINITE_NUMERICAL_DIAGNOSTIC_NOT_A_PROOF",
            "m": m,
            "mpmath_dps": dps,
            "full_matrix_dimension": 2 * m + 1,
            "even_matrix_dimension": m + 1,
            "matrix_source": "full_center_probe.matrix_K(m)",
            "even_basis_source": "parity_gap_table.parity_bases(m).E",
            "eigenvalues_and_residuals": eigenpair_records,
            "even_spectral_gap_lambda1_minus_lambda0": number(gap),
            "bottom_graph": graph_records["bottom"],
            "first_excited_graph": graph_records["first_excited"],
            "precision_diagnostics": {
                "half_digit_relative_tolerance": number(tolerance),
                "adaptive_90_dps_recommended": bool(concerns),
                "reasons": concerns,
            },
            "seconds": round(time.perf_counter() - started, 3),
            "numerical_limitations": [
                "The source matrix uses mpmath quadrature and is not a rigorous enclosure.",
                "Finite m values do not imply a cofinal source estimate, NOESCAPE, or RH.",
                "A strict overload is only a finite numerical trigger; compare its margin with the recorded eigenpair residual.",
                "Positive components are classified by strict mpmath sign with exactly zero weights omitted; no sign threshold is applied.",
                "Effective resistance uses a grounded mpmath linear solve, never a floating-point pseudoinverse.",
            ],
        }


def run_capped_cell(m: int, dps: int) -> dict[str, Any]:
    old_handler = signal.getsignal(signal.SIGALRM)

    def timeout_handler(_signum: int, _frame: Any) -> None:
        raise TimeoutError(f"cell m={m} exceeded {CELL_TIME_CAP_SECONDS}s")

    signal.signal(signal.SIGALRM, timeout_handler)
    signal.setitimer(signal.ITIMER_REAL, CELL_TIME_CAP_SECONDS)
    started = time.perf_counter()
    try:
        first = compute_cell(m, dps)
        if first["precision_diagnostics"]["adaptive_90_dps_recommended"] and dps < ADAPTIVE_DPS:
            reasons = first["precision_diagnostics"]["reasons"]
            result = compute_cell(m, ADAPTIVE_DPS)
            result["adaptive_precision"] = {
                "rerun": True,
                "initial_dps": dps,
                "final_dps": ADAPTIVE_DPS,
                "initial_reasons": reasons,
                "initial_summary": {
                    "gap": first["even_spectral_gap_lambda1_minus_lambda0"],
                    "bottom_max_alpha_R": first["bottom_graph"]["maximum_alpha_times_resistance"],
                    "excited_max_alpha_R": first["first_excited_graph"]["maximum_alpha_times_resistance"],
                    "bottom_endpoint_max": first["bottom_graph"]["maximum_endpoint_score_alpha_times_reciprocal_degree_sum"],
                    "excited_endpoint_max": first["first_excited_graph"]["maximum_endpoint_score_alpha_times_reciprocal_degree_sum"],
                },
            }
            result["seconds_including_adaptive_run"] = round(time.perf_counter() - started, 3)
            return result
        first["adaptive_precision"] = {"rerun": False, "reason": "no stability trigger"}
        return first
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)


def save(path: Path, payload: dict[str, Any]) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m", type=int, nargs="+", default=[4, 8, 16], help="cells to compute; default: 4 8 16")
    parser.add_argument("--dps", type=int, default=DEFAULT_DPS, help=f"working mpmath precision (minimum 60; default {DEFAULT_DPS})")
    args = parser.parse_args()
    if args.dps < 60:
        parser.error("--dps must be at least 60")
    if any(m < 2 for m in args.m):
        parser.error("each m must be at least 2")

    try:
        payload = json.loads(OUTPUT.read_text(encoding="utf-8"))
        if not isinstance(payload.get("results"), dict):
            raise ValueError("existing JSON has no results mapping")
    except FileNotFoundError:
        payload = {"results": {}}
    except (json.JSONDecodeError, ValueError):
        payload = {"results": {}}

    payload.update(
        {
            "schema": "noescape_resistance_probe.v1",
            "status": "RUNNING_FINITE_DIAGNOSTIC_NOT_A_PROOF",
            "route_status": "CHALLENGER_NOT_RH",
            "claim_boundary": "PX_RH_CLAIM: NOT_MADE",
            "requested_m": args.m,
            "base_mpmath_dps": args.dps,
            "adaptive_mpmath_dps": ADAPTIVE_DPS,
            "per_cell_runtime_cap_seconds": CELL_TIME_CAP_SECONDS,
            "exact_zero_policy": "classify strict mpmath signs; exclude exactly zero only",
            "resistance_solver": "grounded mpmath linear solve per positive component; no pseudoinverse",
            "source_sha256": {
                "full_center_probe.py": sha256(FOKAS / "full_center_probe.py"),
                "parity_gap_table.py": sha256(HERE / "parity_gap_table.py"),
                "this_script": sha256(Path(__file__).resolve()),
            },
        }
    )
    save(OUTPUT, payload)

    failed = False
    for m in args.m:
        print(f"building literal even CCM matrix and signed graphs for m={m} at dps={args.dps}", flush=True)
        try:
            result = run_capped_cell(m, args.dps)
        except TimeoutError as exc:
            result = {
                "status": "INCOMPLETE_CELL_TIME_CAP",
                "m": m,
                "base_mpmath_dps": args.dps,
                "runtime_cap_seconds": CELL_TIME_CAP_SECONDS,
                "detail": str(exc),
            }
            failed = True
        except Exception as exc:  # keep an honest partial result for later targeted reruns
            result = {
                "status": "INCOMPLETE_CELL_ERROR",
                "m": m,
                "base_mpmath_dps": args.dps,
                "error_type": type(exc).__name__,
                "detail": str(exc),
            }
            failed = True
        payload["results"][str(m)] = result
        payload["status"] = "PARTIAL_OR_INCOMPLETE" if failed else "RUNNING_FINITE_DIAGNOSTIC_NOT_A_PROOF"
        save(OUTPUT, payload)
        print(json.dumps({"m": m, "status": result["status"], "seconds": result.get("seconds_including_adaptive_run", result.get("seconds")), "output": str(OUTPUT)}, ensure_ascii=False), flush=True)
        if failed:
            break

    payload["status"] = "PARTIAL_OR_INCOMPLETE" if failed else "REQUESTED_CELLS_COMPLETE_FINITE_DIAGNOSTIC_NOT_A_PROOF"
    save(OUTPUT, payload)
    print(f"saved {OUTPUT}", flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
