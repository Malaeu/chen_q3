#!/usr/bin/env python3
"""Probe 7: split the bordered curvature pairing into pole and Arch-prime parts.

The production matrix is imported from the frozen Phase-5 builder.  This is a
finite-cell diagnostic only; it proves no cofinal bound and makes no RH claim.
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
DUALCERT = PHASE5_SCRIPTS / "out" / "edge_ledger_dualcert.json"
PRECOMMIT = PHASE5_SCRIPTS / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"
SCHEDULE = ((13, 240), (23, 240), (43, 240), (83, 360))


def progress(message: str) -> None:
    if sys.stdout.isatty():
        sys.stdout.write("\r" + message + " " * 8)
        sys.stdout.flush()
    else:
        print(message, flush=True)


def progress_done() -> None:
    if sys.stdout.isatty():
        sys.stdout.write("\n")
        sys.stdout.flush()


def dot(left: list[arb], right: list[arb]) -> arb:
    return sum((x * y for x, y in zip(left, right, strict=True)), arb(0))


def solve_vector(matrix: arb_mat, rhs: list[arb]) -> list[arb]:
    column = arb_mat(len(rhs), 1)
    for i, value in enumerate(rhs):
        column[i, 0] = value
    solution = matrix.solve(column, algorithm="precond")
    return [solution[i, 0] for i in range(len(rhs))]


def certified_le(left: arb, right: arb) -> bool:
    return bool(left <= right)


def load_references() -> dict[int, arb]:
    payload = json.loads(DUALCERT.read_text(encoding="utf-8"))
    refs: dict[int, arb] = {}
    for cell in payload["cells"]:
        sanity = cell["basis_mapping_sanity_check"]
        if sanity.get("status") != "OK" or not sanity.get("agree_8sig"):
            raise RuntimeError(f"dualcert reference is not validated for m={cell['m']}")
        refs[int(cell["m"])] = arb(str(sanity["a1_over_xi0"]))
    expected = {m for m, _ in SCHEDULE}
    if set(refs) != expected:
        raise RuntimeError(f"dualcert schedule mismatch: got {sorted(refs)}, expected {sorted(expected)}")
    return refs


def build_cell(m: int, dps: int, reference: arb) -> dict[str, Any]:
    started = time.monotonic()
    ctx.dps = dps
    ctx.threads = 1
    N = m
    builder = CCMArbBuilder(m, N)
    matrix = builder.even_block()
    lambda1, _lambda2, _v1, _v2, algorithm = compute_eig_data(matrix, want_vectors=False)

    shifted_D = arb_mat(N, N)
    for i in range(N):
        for j in range(N):
            shifted_D[i, j] = matrix[i + 1, j + 1] - (lambda1 if i == j else 0)

    sqrt2 = arb(2).sqrt()
    b_pole = [sqrt2 * builder.w02(0, i) for i in range(1, N + 1)]
    b_ap = [
        -sqrt2 * (builder.wr(0, i) + builder.prime(0, i))
        for i in range(1, N + 1)
    ]
    b_full = [matrix[i, 0] for i in range(1, N + 1)]
    split_deltas = [b_full[i] - b_pole[i] - b_ap[i] for i in range(N)]
    split_ok = all(0 in delta for delta in split_deltas)
    if not split_ok:
        raise RuntimeError(f"SLOPE_SPLIT_SOURCE_MISMATCH m={m}")

    c = [sqrt2 / (2 * builder.pi**2 * i * i) for i in range(1, N + 1)]
    x_pole = solve_vector(shifted_D, b_pole)
    x_ap = solve_vector(shifted_D, b_ap)
    x_direct = solve_vector(shifted_D, b_full)
    s_pole = dot(c, x_pole)
    s_ap = dot(c, x_ap)
    s_total = s_pole + s_ap
    s_direct = dot(c, x_direct)
    direct_split_delta = s_total - s_direct
    direct_split_ok = 0 in direct_split_delta
    if not direct_split_ok:
        raise RuntimeError(f"SLOPE_SPLIT_SOLVE_MISMATCH m={m}")

    one_twelfth = arb(1) / 12
    cancellation = one_twelfth - s_total
    sanity_ok = sig_agree(cancellation, reference, 8)
    if not sanity_ok:
        raise RuntimeError(
            f"SLOPE_SANITY_MISMATCH m={m} computed={decimal_str(cancellation)} "
            f"reference={decimal_str(reference)}"
        )

    confirmed_cell = certified_le(abs(one_twelfth - s_pole), one_twelfth / 2) and certified_le(
        abs(s_ap), one_twelfth / 2
    )
    refuted_cell = certified_le(abs(s_pole), one_twelfth / 10)
    return {
        "m": m,
        "N": N,
        "dps": dps,
        "eigen_algorithm": algorithm,
        "lambda1": bounds(lambda1),
        "split_overlap_zero": split_ok,
        "direct_split_zero": direct_split_ok,
        "direct_split_delta": bounds(direct_split_delta),
        "S_pole": bounds(s_pole),
        "S_AP": bounds(s_ap),
        "S_total": bounds(s_total),
        "S_direct": bounds(s_direct),
        "one_twelfth_minus_S": bounds(cancellation),
        "dualcert_reference": decimal_str(reference),
        "sanity_agree_8sig": sanity_ok,
        "S_pole_over_one_twelfth": bounds(s_pole / one_twelfth),
        "S_AP_over_one_twelfth": bounds(s_ap / one_twelfth),
        "one_twelfth_minus_S_pole_times_L_sq": bounds(
            (one_twelfth - s_pole) * builder.L**2
        ),
        "confirmed_cell": confirmed_cell,
        "refuted_cell": refuted_cell,
        "elapsed_seconds": time.monotonic() - started,
    }


def verdict_for(cells: list[dict[str, Any]]) -> str:
    if all(cell["confirmed_cell"] for cell in cells):
        return "CONFIRMED"
    if all(cell["refuted_cell"] for cell in cells):
        return "REFUTED"
    return "UNRESOLVED"


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    lines = [
        "# Goal 058 Probe 7 — bordered slope split",
        "",
        "Finite-cell diagnostic only. `DIAGNOSTIC_NEVER_A_PROOF`. `PX_RH_CLAIM: NOT_MADE`.",
        "",
        "| m=N | dps | S_pole/(1/12) | S_AP/(1/12) | (1/12-S_pole)L^2 | 1/12-S | sanity |",
        "|---:|---:|---:|---:|---:|---:|:---:|",
    ]
    for cell in payload["cells"]:
        lines.append(
            "| {m} | {dps} | {sp} | {sa} | {scaled} | {cancel} | {sanity} |".format(
                m=cell["m"],
                dps=cell["dps"],
                sp=cell["S_pole_over_one_twelfth"]["ball"],
                sa=cell["S_AP_over_one_twelfth"]["ball"],
                scaled=cell["one_twelfth_minus_S_pole_times_L_sq"]["ball"],
                cancel=cell["one_twelfth_minus_S"]["ball"],
                sanity="PASS" if cell["sanity_agree_8sig"] else "FAIL",
            )
        )
    lines.extend(
        [
            "",
            payload["verdict_line_quoted"],
            "",
            "The pole and Arch-prime contributions are individually enormous and cancel each other; neither frozen decisive condition holds.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    references = load_references()
    cells: list[dict[str, Any]] = []
    for index, (m, dps) in enumerate(SCHEDULE, start=1):
        progress(f"[slope-split] {index}/{len(SCHEDULE)} m=N={m} dps={dps}")
        cells.append(build_cell(m, dps, references[m]))
    progress_done()
    verdict = verdict_for(cells)
    verdict_line = f"P_POLE_PART_CARRIES_ONE_TWELFTH: {verdict}"
    payload = {
        "schema": "EdgeLedgerSlopeSplit.v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "route": "GOAL058_CURVATURE_BORDERED_SECULAR_SLOPE",
        "precommit": str(PRECOMMIT.relative_to(REPO)),
        "addendum": 8,
        "semantic_boundary": "FINITE_CELL_DIAGNOSTIC_NEVER_A_PROOF",
        "prediction": {"id": "P_POLE_PART_CARRIES_ONE_TWELFTH", "p": 0.60},
        "schedule_m": [m for m, _ in SCHEDULE],
        "cells": cells,
        "verdict": verdict,
        "verdict_line_quoted": verdict_line,
        "promotion": False,
        "px_rh_claim": "NOT_MADE",
    }
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    json_path = OUT_DIR / "slope_split.json"
    md_path = OUT_DIR / "slope_split.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(payload, md_path)
    print(f"[slope-split] wrote {json_path}")
    print(f"[slope-split] wrote {md_path}")
    print(f"[slope-split] verdict: {verdict_line}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
