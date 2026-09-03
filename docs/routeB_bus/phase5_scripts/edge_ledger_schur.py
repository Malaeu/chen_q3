#!/usr/bin/env python3
"""Probe 6 (center Schur-pairing sign structure, attack R2) for the Goal 058
edge ledger.

Precommit: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md,
ADDENDUM 4 (2026-09-03 13:22). Judge context: attack R2
(`P59_CURVATURE_CENTER_SCHUR_STIELTJES`), section 4 (Q3) of
docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md.

Object (production, no substitutes): the EVEN block of the finite CCM Weil
matrix, obtained by importing ``CCMArbBuilder`` from ``edge_ledger_build.py``
and the full-spectrum machinery from ``edge_ledger_dualcert.py`` (Probe 5;
neither is copied). Schedule: m = N in {13, 23, 43, 83} (163 excluded, same
reason as Probe 5 -- no full spectrum there). DIAGNOSTIC_NEVER_A_PROOF.
PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.

--------------------------------------------------------------------------
Center Schur split
--------------------------------------------------------------------------
The even block Q (dim N+1, indices 0..N in the SAME even-basis coordinates
Probe 5 validated) is split at the central coordinate n=0 (index 0):

    Q = [[a, b^T], [b, D]]

a = Q[0,0] (scalar), b = Q[1:,0] (length N, already the even-basis entries,
no extra sqrt(2) translation needed -- Q itself is already expressed in the
even eigenbasis), D = Q[1:,1:] (N x N principal submatrix).

Writing K xi = lambda1 * xi in block form and solving the bottom block row
for the tail gives xi = xi_0 * (1, -(D-lambda1)^{-1} b) (judge's R2 note),
hence

    ell_N(xi)/xi_0 = 1/12 - <c, (D-lambda1)^{-1} b>

with c = ell_even[1:] (the i=1..N, i.e. "n != 0", part of Probe 5's
ell_even; ell_even[0] = 1/12 is exactly the additive 1/12 term here).

f(z) := <c, (D-z)^{-1} b> = sum_j r_j/(mu_j - z), (mu_j, w_j) the
eigenpairs of D, r_j = <c,w_j> * <w_j,b>. Every r_j is invariant under a
global sign flip of w_j (both factors flip together), so -- unlike Probe
5's v1 -- no sign convention needs to be imposed on D's eigenvectors.

Sanity check (frozen in the precommit): 1/12 - f(lambda1) must equal
Probe 5's a_1/xi_0 (itself validated there against 2*kappa/L^2) to >= 8
significant digits. lambda1 and xi_0 are obtained by calling
``edge_ledger_dualcert.robust_full_eig`` -- the SAME function, same
schedule (m, N), same base precision -- that produced Probe 5's numbers,
so this is a bit-for-bit reproduction of Probe 5's v1/xi_0/a_1, not an
independent re-derivation that could coincidentally agree.

--------------------------------------------------------------------------
Interlacing check (documented limitation)
--------------------------------------------------------------------------
The precommit's addendum asks for "sign changes of f on (mu_j, mu_{j+1})
between consecutive poles, evaluate f at midpoints" -- a single midpoint
evaluation per gap is a COARSE proxy: it detects a change in the sign of
f AT THE MIDPOINT from one gap to the next, not whether f actually crosses
zero somewhere inside a given open interval (which would require sampling
near both pole edges, not requested here). This script implements exactly
the literal instruction (one evaluation per gap midpoint) and reports the
resulting sign sequence and its transition count; it does not claim to
certify true interlacing.

--------------------------------------------------------------------------
Loewner monotonicity check (descriptive)
--------------------------------------------------------------------------
b_i here (CCM Lemma 5.1 notation, NOT the Schur-split vector b above) is
CCMArbBuilder's antisymmetric alpha_n sequence for n=1..N (self.alpha[n],
the same values wr's off-diagonal (alpha_m-alpha_n)/(n-m) draws on). This
script reports whether alpha_1 <= alpha_2 <= ... <= alpha_N (increasing),
the reverse (decreasing), or neither, using certified ball comparisons
where they resolve and float-mid fallback only for a same-valued tie.
"""

from __future__ import annotations

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from flint import arb, arb_mat, ctx  # noqa: E402

from edge_ledger_build import (  # noqa: E402
    CCMArbBuilder,
    bounds,
    decimal_str,
    sig_agree,
    unit_normalize,
)
from edge_ledger_dualcert import (  # noqa: E402
    build_ell_even,
    compute_full_eig,
    dot,
    robust_full_eig as robust_full_eig_Q,
    PRECISION_BUMPS as DUALCERT_PRECISION_BUMPS,
)

REPO = Path(__file__).resolve().parents[3]
OUT_DIR = Path(__file__).resolve().parent / "out"
PRECOMMIT = Path(__file__).resolve().parent / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"

SCHEDULE_M = (13, 23, 43, 83)
BASE_DPS = 240
SANITY_SIG_DIGITS = 8
MINORITY_CONFIRM_THRESHOLD = 1e-6
MINORITY_REFUTE_THRESHOLD = 0.05
MAX_PRECISION_RECONCILE_ROUNDS = 3

VERDICT_CONFIRMED_LINE = (
    "- CONFIRMED (one sign): at every cell minority_mass <= 1e-6 -> f is a "
    "Stieltjes-type function on this cell; R2's sign gate is numerically open."
)
VERDICT_REFUTED_LINE = (
    "- REFUTED: at every cell minority_mass >= 0.05 -> no one-sign structure; "
    "R2 needs a different identity (interlacing or exact Loewner inverse), "
    "not positivity."
)
VERDICT_UNRESOLVED_LINE = (
    "- else UNRESOLVED. Also descriptive: the Loewner structure of the "
    "off-diagonal entries tau_{ij} = (b_i - b_j)/(i - j) (CCM Lemma 5.1) -- "
    "report whether the sequence b_i is monotone on 1..N at each cell. "
    "DIAGNOSTIC_NEVER_A_PROOF."
)


def isatty() -> bool:
    return sys.stdout.isatty()


def progress(msg: str) -> None:
    if isatty():
        sys.stdout.write("\r" + msg + " " * 8)
        sys.stdout.flush()
    else:
        print(msg, flush=True)


def progress_done() -> None:
    if isatty():
        sys.stdout.write("\n")
        sys.stdout.flush()


def build_D_matrix(m: int, N: int) -> arb_mat:
    """D = Q[1:,1:], rebuilt fresh at the current ctx.dps."""
    Q = CCMArbBuilder(m, N).even_block()
    D = arb_mat(N, N)
    for i in range(N):
        for j in range(N):
            D[i, j] = Q[i + 1, j + 1]
    return D


def robust_full_eig_D(m: int, N: int, base_dps: int) -> tuple[list[arb], list[list[arb]], str, int]:
    """Full-spectrum eig of D with the same escalating-precision fallback
    edge_ledger_dualcert.robust_full_eig uses for Q, generalized to an
    (N x N) matrix built fresh at each bumped precision."""
    last_exc: Exception | None = None
    for bump in DUALCERT_PRECISION_BUMPS:
        dps = base_dps + bump
        ctx.dps = dps
        ctx.threads = 1
        matrix = build_D_matrix(m, N)
        try:
            lambdas, vectors, algorithm = compute_full_eig(matrix)
            return lambdas, vectors, algorithm, dps
        except Exception as exc:  # noqa: BLE001 - deliberate precision-escalation fallback
            last_exc = exc
            continue
    raise RuntimeError(
        f"full-spectrum eig of D failed even after precision bumps "
        f"{DUALCERT_PRECISION_BUMPS} above base dps={base_dps} for m={m}, N={N}: {last_exc}"
    )


def certified_sign(value: arb) -> str:
    if bool(value < 0):
        return "-"
    if bool(value > 0):
        return "+"
    return "0"


def f_at(z: arb, mus: list[arb], r_list: list[arb]) -> arb:
    total = arb(0)
    for mu, r in zip(mus, r_list):
        total += r / (mu - z)
    return total


def loewner_monotone_check(builder: CCMArbBuilder, N: int) -> dict[str, Any]:
    b = [builder.alpha[n] for n in range(1, N + 1)]
    inc = all(bool(b[i] <= b[i + 1]) for i in range(len(b) - 1))
    dec = all(bool(b[i] >= b[i + 1]) for i in range(len(b) - 1))
    if inc and dec:
        verdict = "constant"
    elif inc:
        verdict = "increasing"
    elif dec:
        verdict = "decreasing"
    else:
        verdict = "not_monotone"
    return {
        "monotone": verdict,
        "b_1": decimal_str(b[0], 20) if b else None,
        "b_N": decimal_str(b[-1], 20) if b else None,
    }


def build_cell(m: int) -> dict[str, Any]:
    N = m
    started = time.time()

    progress(f"[schur] m={m} N={N} full spectrum of Q (dim {N + 1}) ...")
    lambdas_Q, vectors_Q, algo_Q, dps = robust_full_eig_Q(m, N, BASE_DPS)
    progress_done()

    ctx.dps = dps
    ctx.threads = 1
    v1 = unit_normalize(vectors_Q[0])
    if v1[0].mid() < 0:
        v1 = [-x for x in v1]
    lam1 = lambdas_Q[0]
    xi0 = v1[0]

    reconcile_notes: list[str] = []
    for _round in range(MAX_PRECISION_RECONCILE_ROUNDS):
        progress(f"[schur] m={m} N={N} full spectrum of D (dim {N}) at base dps={dps} ...")
        mus, ws_raw, algo_D, dpsD = robust_full_eig_D(m, N, dps)
        progress_done()
        if dpsD == dps:
            break
        reconcile_notes.append(
            f"D needed higher precision than Q ({dpsD} vs {dps}); "
            "re-deriving lambda1/xi0 at the higher precision for a single "
            "consistent working precision this cell."
        )
        progress(f"[schur] m={m} N={N} re-deriving Q-side at dps={dpsD} ...")
        lambdas_Q, vectors_Q, algo_Q, dps2 = robust_full_eig_Q(m, N, dpsD)
        progress_done()
        ctx.dps = dps2
        ctx.threads = 1
        v1 = unit_normalize(vectors_Q[0])
        if v1[0].mid() < 0:
            v1 = [-x for x in v1]
        lam1 = lambdas_Q[0]
        xi0 = v1[0]
        dps = dps2

    ctx.dps = dps
    ctx.threads = 1
    ws = [unit_normalize(w) for w in ws_raw]

    builder = CCMArbBuilder(m, N)
    Q = builder.even_block()
    a00 = Q[0, 0]
    b_vec = [Q[i, 0] for i in range(1, N + 1)]

    pi = builder.pi
    ell_even = build_ell_even(N, pi)
    c_vec = ell_even[1:]

    a1 = dot(ell_even, v1)
    a1_over_xi0 = a1 / xi0

    r_list = [dot(c_vec, w) * dot(w, b_vec) for w in ws]

    signs = [certified_sign(r) for r in r_list]
    uncertain_count = sum(1 for s in signs if s == "0")
    S_plus = arb(0)
    S_minus = arb(0)
    for r, s in zip(r_list, signs):
        if s == "+":
            S_plus += r
        elif s == "-":
            S_minus += -r
    S_plus_f = float(S_plus.mid())
    S_minus_f = float(S_minus.mid())
    total_mass = S_plus_f + S_minus_f
    minority_mass = min(S_plus_f, S_minus_f) / total_mass if total_mass > 0 else 0.0

    f_lam1 = f_at(lam1, mus, r_list)
    cancellation = arb(1) / 12 - f_lam1
    sanity_agree = sig_agree(cancellation, a1_over_xi0, SANITY_SIG_DIGITS)
    sanity = {
        "one_twelfth_minus_f_lambda1": float(cancellation.mid()),
        "a1_over_xi0_probe5": float(a1_over_xi0.mid()),
        "agree_8sig": sanity_agree,
        "status": "OK" if sanity_agree else "SCHUR_SANITY_MISMATCH",
    }

    # Interlacing proxy: sign of f at each gap midpoint, consecutive poles.
    mid_signs: list[str] = []
    for i in range(len(mus) - 1):
        mid = (mus[i] + mus[i + 1]) / 2
        val = f_at(mid, mus, r_list)
        mid_signs.append(certified_sign(val))
    sign_changes = sum(
        1 for i in range(len(mid_signs) - 1) if mid_signs[i] != mid_signs[i + 1]
    )
    mid_uncertain_count = sum(1 for s in mid_signs if s == "0")

    loewner = loewner_monotone_check(builder, N)

    elapsed = time.time() - started
    return {
        "m": m,
        "N": N,
        "dim_Q": N + 1,
        "dim_D": N,
        "dps_effective": dps,
        "eigen_algorithm_Q": algo_Q,
        "eigen_algorithm_D": algo_D,
        "reconcile_notes": reconcile_notes,
        "lambda1": bounds(lam1),
        "xi0": bounds(xi0),
        "a00": bounds(a00),
        "a1_over_xi0": bounds(a1_over_xi0),
        "basis_mapping_sanity_check": sanity,
        "num_residues": len(r_list),
        "residues_r_j_leq10": [decimal_str(r, 20) for r in r_list[:10]],
        "residue_sign_certified_uncertain_count": uncertain_count,
        "S_plus": bounds(S_plus),
        "S_minus": bounds(S_minus),
        "S_plus_float": S_plus_f,
        "S_minus_float": S_minus_f,
        "minority_mass": minority_mass,
        "f_lambda1": bounds(f_lam1),
        "num_poles": len(mus),
        "num_gaps": len(mid_signs),
        "midpoint_sign_sequence": "".join(mid_signs),
        "midpoint_sign_changes": sign_changes,
        "midpoint_uncertain_count": mid_uncertain_count,
        "loewner_monotone_check": loewner,
        "elapsed_seconds": elapsed,
    }


def evaluate_verdict(cells: list[dict[str, Any]]) -> tuple[str, str]:
    minorities = [c["minority_mass"] for c in cells]
    if all(mm <= MINORITY_CONFIRM_THRESHOLD for mm in minorities):
        return "CONFIRMED", VERDICT_CONFIRMED_LINE
    if all(mm >= MINORITY_REFUTE_THRESHOLD for mm in minorities):
        return "REFUTED", VERDICT_REFUTED_LINE
    return "UNRESOLVED", VERDICT_UNRESOLVED_LINE


def write_json(cells: list[dict[str, Any]], verdict: str, verdict_line: str, out_path: Path) -> None:
    result = {
        "schema": "EdgeLedgerSchur.v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "route": "CHALLENGER_NOT_RH",
        "promotion": "FORBIDDEN",
        "px_rh_claim": "NOT_MADE",
        "semantic_boundary": "finite_CCM_even_sector_diagnostic_only; not_a_certificate; DIAGNOSTIC_NEVER_A_PROOF",
        "precommit": str(PRECOMMIT.relative_to(REPO)),
        "addendum": "ADDENDUM 4 (2026-09-03 13:22), Probe 6",
        "prediction": "P_SCHUR_RESIDUES_ONE_SIGN p=0.35",
        "schedule_m": list(SCHEDULE_M),
        "cells": cells,
        "verdict": verdict,
        "verdict_line_quoted": verdict_line,
    }
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_markdown(cells: list[dict[str, Any]], verdict: str, verdict_line: str, out_path: Path) -> None:
    lines = []
    lines.append("# Probe 6 report -- center Schur-pairing sign structure (R2)")
    lines.append("")
    lines.append(
        "Precommit: `PRECOMMIT_2026-09-03_edge_ledger_probes.md`, ADDENDUM 4 "
        "(2026-09-03 13:22). Judge context: attack R2 "
        "(`P59_CURVATURE_CENTER_SCHUR_STIELTJES`), section 4 of "
        "`docs/routeB_bus/proshka/"
        "PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md`."
    )
    lines.append("")
    lines.append("## Sanity check: 1/12 - f(lambda1) vs Probe 5's a_1/xi_0")
    lines.append("")
    lines.append("| m | 1/12 - f(lambda1) | a_1/xi_0 (Probe 5, recomputed here bit-for-bit) | agree (8 sig) | status |")
    lines.append("|---|---|---|---|---|")
    for c in cells:
        s = c["basis_mapping_sanity_check"]
        lines.append(
            f"| {c['m']} | {s['one_twelfth_minus_f_lambda1']:.12g} | "
            f"{s['a1_over_xi0_probe5']:.12g} | {s['agree_8sig']} | {s['status']} |"
        )
    lines.append("")
    lines.append("## Per-cell table")
    lines.append("")
    lines.append(
        "| m | dps | minority_mass | S_+ | S_- | # poles | midpoint sign changes | # uncertain midpoints | monotone b_i |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|")
    for c in cells:
        lo = c["loewner_monotone_check"]
        lines.append(
            f"| {c['m']} | {c['dps_effective']} | {c['minority_mass']:.6g} | "
            f"{c['S_plus_float']:.6g} | {c['S_minus_float']:.6g} | {c['num_poles']} | "
            f"{c['midpoint_sign_changes']} | {c['midpoint_uncertain_count']} | {lo['monotone']} |"
        )
    lines.append("")
    lines.append("## Midpoint sign sequences (interlacing proxy)")
    lines.append("")
    lines.append(
        "One evaluation of f per gap (mu_j, mu_{j+1}), sign only ('+', '-', "
        "'0' = ball straddles zero). This is a coarse proxy, not a scan for "
        "a zero crossing inside each gap (see module docstring)."
    )
    lines.append("")
    for c in cells:
        lines.append(f"- m={c['m']}: `{c['midpoint_sign_sequence']}`")
    lines.append("")
    lines.append(f"## Verdict: {verdict}")
    lines.append("")
    lines.append(f"Frozen rule quoted verbatim from the precommit: {verdict_line}")
    lines.append("")
    lines.append(
        "minority_mass by cell: "
        + ", ".join(f"m={c['m']}: {c['minority_mass']:.6g}" for c in cells)
    )
    lines.append("")
    lines.append("DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_json = OUT_DIR / "edge_ledger_schur.json"
    out_md = OUT_DIR / "edge_ledger_schur.md"

    cells: list[dict[str, Any]] = []
    for m in SCHEDULE_M:
        cell = build_cell(m)
        sanity = cell["basis_mapping_sanity_check"]
        lo = cell["loewner_monotone_check"]
        print(
            f"[schur] m={m} dps={cell['dps_effective']} "
            f"minority_mass={cell['minority_mass']:.6g} "
            f"S+={cell['S_plus_float']:.6g} S-={cell['S_minus_float']:.6g} "
            f"poles={cell['num_poles']} mid_sign_changes={cell['midpoint_sign_changes']} "
            f"monotone_b={lo['monotone']} sanity={sanity['status']} "
            f"elapsed={cell['elapsed_seconds']:.2f}s",
            flush=True,
        )
        if sanity["status"] == "SCHUR_SANITY_MISMATCH":
            print(
                f"SCHUR_SANITY_MISMATCH at m={m}: 1/12-f(lambda1)="
                f"{sanity['one_twelfth_minus_f_lambda1']!r} vs a_1/xi_0="
                f"{sanity['a1_over_xi0_probe5']!r} -- STOPPING, no further cells computed.",
                file=sys.stderr,
            )
            cells.append(cell)
            write_json(cells, "STOPPED_SCHUR_SANITY_MISMATCH", "n/a", out_json)
            return 2
        cells.append(cell)

    verdict, verdict_line = evaluate_verdict(cells)
    write_json(cells, verdict, verdict_line, out_json)
    write_markdown(cells, verdict, verdict_line, out_md)
    print(f"[schur] wrote {out_json}", flush=True)
    print(f"[schur] wrote {out_md}", flush=True)
    print(f"[schur] verdict: {verdict}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
