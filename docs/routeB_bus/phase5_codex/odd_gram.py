#!/usr/bin/env python3
"""Probe 8: reciprocal-mode odd-Gram defect and the odd-sector floor.

Frozen precommit: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md
ADDENDUM 9. Mathematical source: verdict 3dc82357's C5
(docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL_2026-09-03.md
Section 6).

This probe lives on the FULL noncentral block in +-N row indexing (modes
n = -N..-1, 1..N, both parities), NOT on the folded even basis used by the
rest of the edge-ledger family. The full (2N+1)x(2N+1) matrix K is assembled
here, entry by entry, from the frozen builder's own ``tau_entry(n, m)``
(imported, never re-derived): K[0,0] = a0, the first row/column off the
center is b, and the remaining 2N x 2N block is D. Symmetric pairs
(n, m)/(m, n) give the identical value of tau_entry (verified: w02, wr and
prime are each symmetric under argument swap) and are cached once, exactly
as CCMArbBuilder.even_block()'s own ``k(i, j)`` cache does -- this is a
caching choice about our own driver loop, not a change to what tau_entry
computes.

Definitions (verdict Section 6 Step 1-3, precommit ADDENDUM 9):
  X = diag(n), R = X^-1, eta = all-ones, r = R eta (r_n = 1/n, odd),
  A = (D - lambda1 I)^-1 applied only via arb_mat.solve(algorithm="precond")
  (never formed as a matrix), lambda1 the even bottom eigenvalue of K.
  T1 = (1/2)||r||^2, T2 = <r, A(Rb)>, T3 = (a0-lambda1)<r, Ar>,
  T4 = sum_{n>N} 1/n^2 = pi^2/6 - sum_{n=1}^N 1/n^2 (closed form -- the
  infinite tail is a finite subtraction from zeta(2), never a literal
  infinite/very-long summation), E = T1 - T2 + T3 + T4.
Checks: <r, Ab> == 0 (parity), <b, Ab> - (a0-lambda1) == 0 (Schur root),
commutator residual D R - R D - (b r^T - r b^T) == 0 (source identity,
verdict Step 1; only the i<j upper triangle is checked -- both sides are
antisymmetric matrices since D is symmetric and R is diagonal).
Sanity: kappa_probe4 = (L^2/(4 pi^2)) E must agree with Probe 4's own kappa
(docs/routeB_bus/phase5_scripts/out/edge_ledger_ratio.json) to >= 8 digits
at the same cell -- kappa is basis-independent (this probe works in the raw
+-N basis; Probe 4 works in the folded even basis with sqrt(2) on n=0), so
only the identity itself is being re-derived through a different route.
Mismatch stops with ODD_GRAM_SANITY_MISMATCH.

Odd sector: K has no central coupling to odd vectors (b is even under
n -> -n by the same reversal symmetry that makes tau_entry(n, m) symmetric
under (n, m) -> (-n, -m), verified numerically below), so the odd block of D
and the odd block of K restricted to odd modes are literally the same N x N
matrix O[i, j] = tau_entry(i, j) - tau_entry(i, -j) for i, j = 1..N (an odd
vector v with v_{-n} = -v_n is carried by its N free coordinates w_i = v_i).
mu_odd_min is O's smallest eigenvalue, compared with lambda2 (the even
second eigenvalue, computed here from the same even block the rest of the
edge-ledger family uses).

DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE. No Lean, no route
promotion.
"""

from __future__ import annotations

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from flint import arb, arb_mat, ctx

REPO = Path(__file__).resolve().parents[3]
PHASE5_SCRIPTS = REPO / "docs" / "routeB_bus" / "phase5_scripts"
sys.path.insert(0, str(PHASE5_SCRIPTS))

from edge_ledger_build import (  # noqa: E402
    CCMArbBuilder,
    bounds,
    compute_eig_data,
    decimal_str,
    sig_agree,
)

OUT_DIR = Path(__file__).resolve().parent / "out"
RATIO_JSON = PHASE5_SCRIPTS / "out" / "edge_ledger_ratio.json"
PRECOMMIT = PHASE5_SCRIPTS / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"
VERDICT_SOURCE = (
    REPO / "docs" / "routeB_bus" / "proshka"
    / "PROSHKA_VERDICT_GOAL058_NEW_MECHANISM_FOR_CURVATURE_WALL_2026-09-03.md"
)
SCHEDULE = ((13, 240), (23, 240), (43, 240), (83, 360))
PROGRESS_INTERVAL_SECONDS = 60.0

_last_progress = 0.0


def progress(message: str, force: bool = False) -> None:
    global _last_progress
    now = time.monotonic()
    if not force and (now - _last_progress) < PROGRESS_INTERVAL_SECONDS:
        return
    _last_progress = now
    print(f"[odd-gram] {message}", file=sys.stderr, flush=True)


def dot(left: list[arb], right: list[arb]) -> arb:
    return sum((x * y for x, y in zip(left, right, strict=True)), arb(0))


def solve_vector(matrix: arb_mat, rhs: list[arb]) -> list[arb]:
    column = arb_mat(len(rhs), 1)
    for i, value in enumerate(rhs):
        column[i, 0] = value
    solution = matrix.solve(column, algorithm="precond")
    return [solution[i, 0] for i in range(len(rhs))]


def load_kappa_references() -> dict[int, float]:
    payload = json.loads(RATIO_JSON.read_text(encoding="utf-8"))
    refs: dict[int, float] = {}
    for record in payload["probe4_records"]:
        m = int(record["m"])
        if int(record["N"]) != m:
            continue
        if m in refs and record["dps"] != 240:
            continue
        if record["dps"] not in (120, 240):
            continue
        refs[m] = float(record["kappa"])
    expected = {m for m, _ in SCHEDULE}
    missing = expected - set(refs)
    if missing:
        raise RuntimeError(f"edge_ledger_ratio.json Probe-4 kappa missing cells: {sorted(missing)}")
    return refs


def build_cell(m: int, dps: int, kappa_ref: float) -> dict[str, Any]:
    started = time.monotonic()
    ctx.dps = dps
    ctx.threads = 1
    N = m
    builder = CCMArbBuilder(m, N)
    pi = builder.pi

    progress(f"m=N={m} dps={dps}: even block + lambda1/lambda2")
    even = builder.even_block()
    lambda1, lambda2, _v1, _v2, algorithm = compute_eig_data(even, want_vectors=False)

    modes = list(range(1, N + 1)) + list(range(-1, -N - 1, -1))
    dim = 2 * N
    cache: dict[tuple[int, int], arb] = {}

    def tau(n: int, mm: int) -> arb:
        key = (n, mm) if n <= mm else (mm, n)
        if key not in cache:
            cache[key] = builder.tau_entry(*key)
        return cache[key]

    progress(f"m=N={m} dps={dps}: assembling {dim}x{dim} noncentral block D")
    a0 = builder.tau_entry(0, 0)
    b = [builder.tau_entry(modes[i], 0) for i in range(dim)]
    D = arb_mat(dim, dim)
    for i in range(dim):
        D[i, i] = tau(modes[i], modes[i])
        for j in range(i + 1, dim):
            value = tau(modes[i], modes[j])
            D[i, j] = value
            D[j, i] = value

    # Reversal-symmetry sanity: b must be even (b_{-n} = b_n) -- this is what
    # makes K's center have zero coupling to any odd vector (verdict Step 2).
    b_even_defect = max(
        float(abs(b[i] - b[N + i]).mid()) for i in range(N)
    )

    r = [arb(1) / modes[i] for i in range(dim)]
    Rb = [b[i] / modes[i] for i in range(dim)]

    shifted_D = arb_mat(D)
    for i in range(dim):
        shifted_D[i, i] = shifted_D[i, i] - lambda1

    progress(f"m=N={m} dps={dps}: three precond solves against (D-lambda1 I)")
    Ab = solve_vector(shifted_D, b)
    A_Rb = solve_vector(shifted_D, Rb)
    Ar = solve_vector(shifted_D, r)

    T1 = dot(r, r) / 2
    T2 = dot(r, A_Rb)
    a0_minus_lambda1 = a0 - lambda1
    T3 = a0_minus_lambda1 * dot(r, Ar)
    tail_closed_form = (pi * pi) / 6 - sum((arb(1) / (n * n) for n in range(1, N + 1)), arb(0))
    T4 = tail_closed_form
    E = T1 - T2 + T3 + T4

    r_Ab = dot(r, Ab)
    b_Ab_minus_schur = dot(b, Ab) - a0_minus_lambda1

    progress(f"m=N={m} dps={dps}: commutator residual (upper triangle)")
    commutator_max_abs = 0.0
    commutator_all_zero = True
    for i in range(dim):
        inv_i = arb(1) / modes[i]
        for j in range(i + 1, dim):
            inv_j = arb(1) / modes[j]
            residual = D[i, j] * (inv_j - inv_i) - (b[i] * inv_j - b[j] * inv_i)
            commutator_max_abs = max(commutator_max_abs, float(abs(residual).mid()))
            if 0 not in residual:
                commutator_all_zero = False

    kappa_computed = (builder.L ** 2 / (4 * pi * pi)) * E
    kappa_ref_arb = arb(str(kappa_ref))
    sanity_ok = sig_agree(kappa_computed, kappa_ref_arb, 8)
    if not sanity_ok:
        raise RuntimeError(
            "ODD_GRAM_SANITY_MISMATCH "
            f"m={m}: kappa_computed={decimal_str(kappa_computed)} "
            f"kappa_probe4_ref={kappa_ref}"
        )

    progress(f"m=N={m} dps={dps}: odd block O ({N}x{N}) and its ground eigenvalue")
    O = arb_mat(N, N)
    for i in range(N):
        for j in range(N):
            # v_{-n} = -v_n odd vectors: (D v)_i = sum_j [tau(i,j) - tau(i,-j)] w_j
            O[i, j] = D[i, j] - D[i, N + j]
    mu_odd_min, _mu_odd_second, _ov1, _ov2, odd_algorithm = compute_eig_data(O, want_vectors=False)

    ratio_mu_lambda2 = mu_odd_min / lambda2

    T2_L2 = abs(T2) * builder.L ** 2
    T3_L2 = abs(T3) * builder.L ** 2
    p_e_terms_metric = max(T2_L2, T3_L2)
    p_e_terms_confirmed_cell = bool(p_e_terms_metric <= 10)
    p_e_terms_refuted_cell = not p_e_terms_confirmed_cell

    return {
        "m": m,
        "N": N,
        "dps": dps,
        "L": bounds(builder.L),
        "eigen_algorithm_even": algorithm,
        "eigen_algorithm_odd": odd_algorithm,
        "a0": bounds(a0),
        "lambda1": bounds(lambda1),
        "lambda2": bounds(lambda2),
        "a0_minus_lambda1": bounds(a0_minus_lambda1),
        "b_even_defect_max_abs": b_even_defect,
        "T1_half_r_sq": bounds(T1),
        "T2_r_A_Rb": bounds(T2),
        "T3_gap_r_Ar": bounds(T3),
        "T4_tail_closed_form": bounds(T4),
        "E": bounds(E),
        "check_r_Ab": bounds(r_Ab),
        "check_r_Ab_zero": bool(0 in r_Ab),
        "check_b_Ab_minus_schur": bounds(b_Ab_minus_schur),
        "check_b_Ab_minus_schur_zero": bool(0 in b_Ab_minus_schur),
        "commutator_residual_max_abs": commutator_max_abs,
        "commutator_residual_all_zero": commutator_all_zero,
        "kappa_computed": bounds(kappa_computed),
        "kappa_probe4_reference": kappa_ref,
        "kappa_sanity_agree_8sig": sanity_ok,
        "mu_odd_min": bounds(mu_odd_min),
        "ratio_mu_odd_min_over_lambda2": bounds(ratio_mu_lambda2),
        "T2_times_L_sq": bounds(T2_L2),
        "T3_times_L_sq": bounds(T3_L2),
        "p_e_terms_metric_max": float(p_e_terms_metric.mid()),
        "p_e_terms_confirmed_cell": p_e_terms_confirmed_cell,
        "p_e_terms_refuted_cell": p_e_terms_refuted_cell,
        "elapsed_seconds": time.monotonic() - started,
    }


def verdict_p_e_terms(cells: list[dict[str, Any]]) -> str:
    if all(cell["p_e_terms_confirmed_cell"] for cell in cells):
        return "CONFIRMED"
    if all(cell["p_e_terms_refuted_cell"] for cell in cells):
        return "REFUTED"
    return "UNRESOLVED"


def verdict_p_odd_floor(cells: list[dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    by_m = {cell["m"]: cell for cell in cells}
    if 13 not in by_m or 83 not in by_m:
        return "UNRESOLVED", {}
    mu13 = arb(by_m[13]["mu_odd_min"]["ball"])
    mu83 = arb(by_m[83]["mu_odd_min"]["ball"])
    ratio = mu83 / mu13
    threshold = arb("1e-6")
    detail = {
        "mu_odd_min_13": by_m[13]["mu_odd_min"],
        "mu_odd_min_83": by_m[83]["mu_odd_min"],
        "ratio_83_over_13": bounds(ratio),
        "ratio_83_over_13_float": float(ratio.mid()),
        "threshold": "1e-6",
    }
    if ratio >= threshold:
        return "CONFIRMED", detail
    if ratio < threshold:
        return "REFUTED", detail
    return "UNRESOLVED", detail


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# Goal 058 Probe 8 — reciprocal-mode odd-Gram defect and the odd-sector floor",
        "",
        "Finite-cell diagnostic only. `DIAGNOSTIC_NEVER_A_PROOF`. `PX_RH_CLAIM: NOT_MADE`.",
        "",
        "Full noncentral block in +-N row indexing (both parities), not the folded even basis.",
        "",
        "| m=N | dps | T1 | T2 | T3 | T4 | E | kappa check | mu_odd_min | lambda2 | ratio mu/lambda2 |",
        "|---:|---:|---:|---:|---:|---:|---:|:---:|---:|---:|---:|",
    ]
    for cell in payload["cells"]:
        lines.append(
            "| {m} | {dps} | {t1} | {t2} | {t3} | {t4} | {e} | {ksan} | {mu} | {lam2} | {ratio} |".format(
                m=cell["m"],
                dps=cell["dps"],
                t1=cell["T1_half_r_sq"]["ball"],
                t2=cell["T2_r_A_Rb"]["ball"],
                t3=cell["T3_gap_r_Ar"]["ball"],
                t4=cell["T4_tail_closed_form"]["ball"],
                e=cell["E"]["ball"],
                ksan="PASS" if cell["kappa_sanity_agree_8sig"] else "FAIL",
                mu=cell["mu_odd_min"]["ball"],
                lam2=cell["lambda2"]["ball"],
                ratio=cell["ratio_mu_odd_min_over_lambda2"]["ball"],
            )
        )
    lines.extend(
        [
            "",
            "## Checks (per cell)",
            "",
            "| m=N | <r,Ab>=0 | <b,Ab>-(a0-lambda1)=0 | commutator residual=0 | b even defect |",
            "|---:|:---:|:---:|:---:|---:|",
        ]
    )
    for cell in payload["cells"]:
        lines.append(
            "| {m} | {c1} | {c2} | {c3} | {bev} |".format(
                m=cell["m"],
                c1="PASS" if cell["check_r_Ab_zero"] else "FAIL",
                c2="PASS" if cell["check_b_Ab_minus_schur_zero"] else "FAIL",
                c3="PASS" if cell["commutator_residual_all_zero"] else "FAIL",
                bev=cell["b_even_defect_max_abs"],
            )
        )
    lines.extend(
        [
            "",
            payload["verdict_line_p_odd_floor"],
            "",
            payload["verdict_line_p_e_terms"],
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    kappa_refs = load_kappa_references()
    cells: list[dict[str, Any]] = []
    for index, (m, dps) in enumerate(SCHEDULE, start=1):
        progress(f"cell {index}/{len(SCHEDULE)} m=N={m} dps={dps} starting", force=True)
        cell = build_cell(m, dps, kappa_refs[m])
        cells.append(cell)
        progress(
            f"cell {index}/{len(SCHEDULE)} m=N={m} done in {cell['elapsed_seconds']:.1f}s",
            force=True,
        )

    p_odd_floor_verdict, p_odd_floor_detail = verdict_p_odd_floor(cells)
    p_e_terms_verdict = verdict_p_e_terms(cells)
    verdict_line_p_odd_floor = f"P_ODD_SECTOR_FLOOR_NONCOLLAPSING: {p_odd_floor_verdict}"
    verdict_line_p_e_terms = f"P_E_TERMS_NOT_GAP_INFLATED: {p_e_terms_verdict}"

    payload = {
        "schema": "EdgeLedgerOddGram.v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "route": "GOAL058_CURVATURE_RECIPROCAL_MODE_ODD_GRAM",
        "precommit": str(PRECOMMIT.relative_to(REPO)),
        "verdict_source": str(VERDICT_SOURCE.relative_to(REPO)),
        "addendum": 9,
        "probe": 8,
        "semantic_boundary": "FINITE_CELL_DIAGNOSTIC_NEVER_A_PROOF",
        "predictions": [
            {
                "id": "P_ODD_SECTOR_FLOOR_NONCOLLAPSING",
                "p": 0.55,
                "rule": "mu_odd_min(83)/mu_odd_min(13) >= 1e-6",
                "verdict": p_odd_floor_verdict,
                "detail": p_odd_floor_detail,
            },
            {
                "id": "P_E_TERMS_NOT_GAP_INFLATED",
                "p": 0.50,
                "rule": "max(|T2|,|T3|)*L^2 <= 10 at every cell",
                "verdict": p_e_terms_verdict,
            },
        ],
        "schedule_m": [m for m, _ in SCHEDULE],
        "cells": cells,
        "verdict_line_p_odd_floor": verdict_line_p_odd_floor,
        "verdict_line_p_e_terms": verdict_line_p_e_terms,
        "promotion": False,
        "px_rh_claim": "NOT_MADE",
    }
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    json_path = OUT_DIR / "odd_gram.json"
    md_path = OUT_DIR / "odd_gram.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload, md_path)
    print(f"[odd-gram] wrote {json_path}", file=sys.stderr)
    print(f"[odd-gram] wrote {md_path}", file=sys.stderr)
    print(f"[odd-gram] {verdict_line_p_odd_floor}", file=sys.stderr)
    print(f"[odd-gram] {verdict_line_p_e_terms}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
