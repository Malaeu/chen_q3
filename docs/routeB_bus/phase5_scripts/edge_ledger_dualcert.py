#!/usr/bin/env python3
"""Probe 5 (dual-annihilator gap-pay test) for the Goal 058 edge ledger.

Precommit: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md,
ADDENDUM 3 (2026-09-03 13:15). Judge context: attack R1
(`P59_CURVATURE_DUAL_ANNIHILATOR`), section 4 (Q3) of
docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md.

Object (production, no substitutes): the EVEN block of the finite CCM Weil
matrix, built by importing ``CCMArbBuilder`` from ``edge_ledger_build.py``
(never copied). Same kernel, same prime cutoff, same mode indexing as every
other Phase 5 script. Schedule: m = N in {13, 23, 43, 83} (m=163 excluded,
per the precommit -- no full spectrum there). DIAGNOSTIC_NEVER_A_PROOF.
PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.

--------------------------------------------------------------------------
Basis-mapping statement (read before touching a_j / ell_even)
--------------------------------------------------------------------------
edge_ledger_build.py documents the even-basis <-> +-N isometry used
throughout Phase 5 (see its module docstring and ``even_to_pm_row``):
for a J-even vector with raw +-N coordinates c_n = c_{-n},

    xi_even[0] = c_0                      (no sqrt(2) factor)
    xi_even[i] = sqrt(2) * c_i,  i = 1..N  (sqrt(2) factor from the pair)

so a unit-l2 eigenvector in the even basis is automatically unit-l2 in the
+-N indexing once mapped back by c_0 = xi_even[0], c_i = c_{-i} =
xi_even[i]/sqrt(2).

The dual functional ell_N is, in +-N coordinates (frozen in the precommit
and in the judge's own Q3 definition):

    ell_0 = 1/12,   ell_n = 1/(2*pi^2*n^2)  for n != 0.

ell_N pairs against a +-N vector ``c`` via the PLAIN dot product
sum_n ell_n * c_n over n = -N..N (ell itself is even: ell_n = ell_{-n}).
Substituting the isometry above (c_0 = xi_even[0], c_i = c_{-i} =
xi_even[i]/sqrt(2) for i=1..N) and using ell_i = ell_{-i}:

    <ell_N, c> = ell_0 * xi_even[0]
               + sum_{i=1}^N (ell_i + ell_{-i}) * xi_even[i]/sqrt(2)
               = ell_0 * xi_even[0]
               + sum_{i=1}^N sqrt(2) * ell_i * xi_even[i].

So the SAME plain dot product taken directly in the even basis against the
vector

    ell_even[0] = ell_0 = 1/12
    ell_even[i] = sqrt(2) * ell_i = sqrt(2) / (2*pi^2*i^2),  i = 1..N

reproduces <ell_N, c> exactly: <ell_N, c>_{+-N} = ell_even . xi_even. This
is the *only* i=1..N coordinates that carry the sqrt(2) factor -- the
n=0 (i=0) coordinate of ell_even is unscaled, exactly mirroring how
edge_ledger_build.even_block() builds column/row 0 of the Weil matrix
itself (``even[0, j] = sqrt2 * k(0, j)`` for j != 0, ``even[0, 0] = k(0, 0)``
unscaled) -- ell_N is mapped by the identical "row-0 interaction" rule.

Sanity check (frozen in the precommit): a_1 / xi_0 (a_1 = <ell_N, v_1> in
the even basis, xi_0 = v_1's n=0 / i=0 coordinate) must equal 2*kappa/L^2,
kappa taken from out/edge_ledger_ratio.json (Probe 4) for the SAME cell.
Proof this must hold: edge_ledger_ratio.py's own curvature() computes
bracket = xi_0/12 + S/(2*pi^2) with S = sum_{n=1}^N (xi_n+xi_{-n})/n^2 --
this is *identical* algebra to a_1 as derived above (bracket ==
<ell_N, xi>_{+-N} == a_1), and kappa = L^2 * bracket / (2*xi_0), so
a_1/xi_0 = bracket/xi_0 = 2*kappa/L^2 identically. If the two numbers
computed by two independent scripts disagree beyond 8 digits, the basis
mapping used here is wrong and the script STOPs with BASIS_MAPPING_MISMATCH.

--------------------------------------------------------------------------
Sign convention
--------------------------------------------------------------------------
flint's acb_mat.eig(right=True) returns an arbitrary global sign per
eigenvector (already unit-l2, per edge_ledger_build.py's empirical note;
this script re-normalizes explicitly regardless, see ``unit_normalize``).
v_1 (lambda_1's eigenvector) is sign-fixed so its n=0 (i=0) coordinate is
positive: if v1_even[0] < 0, the whole vector v_1 is negated. This does not
affect a_1/xi_0 (both numerator and denominator flip together) but keeps
the reported table's xi_0, a_1, kappa etc. in the same sign convention as
edge_ledger_ratio.py's stored kappa. v_2..v_6 are left at whatever sign
flint returns -- every quantity reported for them (a_j^2 via w_j^2,
gap_share, pay, a_2/v_{2,0}) is invariant under a global sign flip of v_j,
so no convention is imposed on them.
"""

from __future__ import annotations

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))

from flint import acb, acb_mat, arb, ctx  # noqa: E402

from edge_ledger_build import (  # noqa: E402
    CCMArbBuilder,
    EIGEN_ALGORITHMS,
    bounds,
    decimal_str,
    sig_agree,
    unit_normalize,
)

REPO = Path(__file__).resolve().parents[3]
OUT_DIR = Path(__file__).resolve().parent / "out"
PRECOMMIT = Path(__file__).resolve().parent / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"
RATIO_JSON = OUT_DIR / "edge_ledger_ratio.json"

# Schedule: m = N. m=163 excluded per the precommit (no full spectrum).
SCHEDULE_M = (13, 23, 43, 83)
BASE_DPS = 240
# Precision-escalation ladder, mirroring edge_ledger_build.PRECISION_BUMPS.
# m=83 was found (this run) to need +120 (dps=360 effective).
PRECISION_BUMPS = (0, 60, 120, 240, 480)
MAX_REPORT_J = 6
CUMULATIVE_J_UPTO = 6

# a_1/xi_0 vs 2*kappa/L^2 sanity: required agreement, significant digits.
SANITY_SIG_DIGITS = 8

# Verdict thresholds, quoted verbatim from ADDENDUM 3.
VERDICT_CONFIRMED_LINE = (
    "- CONFIRMED: gap_share >= 0.5 at every cell of the schedule -> R1 in its "
    "minimal-norm form pays 1/(lambda2-lambda1); move to R2 (Schur-Stieltjes) "
    "per the judge's ordered rule."
)
VERDICT_REFUTED_LINE = (
    "- REFUTED: gap_share <= 0.05 at every cell (the functional nearly "
    "annihilates v2 as well; a bounded certificate is not excluded by the "
    "spectrum)."
)
VERDICT_UNRESOLVED_LINE = "- else UNRESOLVED. m = 163 excluded (no full spectrum); descriptive only if computed."
GAP_SHARE_CONFIRM_THRESHOLD = 0.5
GAP_SHARE_REFUTE_THRESHOLD = 0.05


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


def full_spectrum_eig(matrix, algorithm: str) -> tuple[list[arb], list[list[arb]]]:
    """Full spectrum with right eigenvectors, ascending by real part.

    Same certification discipline as edge_ledger_build.two_smallest_eigs,
    generalized to the whole spectrum (flint's acb_mat.eig(right=True)
    already computes every eigenpair; two_smallest_eigs just slices two of
    them out). Every eigenvalue and every eigenvector component is checked
    to have an enclosure containing the real axis / real value before its
    real part is accepted.
    """
    ac = acb_mat(matrix)
    eigenvalues, right = ac.eig(right=True, algorithm=algorithm)
    n = len(eigenvalues)
    if n != matrix.nrows():
        raise RuntimeError("flint did not isolate the complete spectrum")
    order = sorted(range(n), key=lambda i: float(eigenvalues[i].real.mid()))
    lambdas: list[arb] = []
    vectors: list[list[arb]] = []
    for idx in order:
        lam_c = eigenvalues[idx]
        if 0 not in lam_c.imag:
            raise RuntimeError(f"eigenvalue enclosure missed the real axis: {lam_c}")
        col = [right[i, idx] for i in range(n)]
        for c in col:
            if 0 not in c.imag:
                raise RuntimeError(f"eigenvector component not real: {c}")
        lambdas.append(lam_c.real)
        vectors.append([c.real for c in col])
    return lambdas, vectors


def compute_full_eig(matrix) -> tuple[list[arb], list[list[arb]], str]:
    last_exc: Exception | None = None
    for algorithm in EIGEN_ALGORITHMS:
        try:
            lambdas, vectors = full_spectrum_eig(matrix, algorithm)
            return lambdas, vectors, algorithm
        except Exception as exc:  # noqa: BLE001 - deliberate multi-algorithm fallback
            last_exc = exc
            continue
    raise RuntimeError(f"full-spectrum eig failed under all algorithms {EIGEN_ALGORITHMS}: {last_exc}")


def robust_full_eig(m: int, N: int, base_dps: int) -> tuple[list[arb], list[list[arb]], str, int]:
    """compute_full_eig with the builder's own escalating-precision fallback
    (mirrors edge_ledger_build.robust_eig): rebuild the even block from
    scratch at each bumped precision until full-spectrum isolation succeeds.
    """
    last_exc: Exception | None = None
    for bump in PRECISION_BUMPS:
        dps = base_dps + bump
        ctx.dps = dps
        ctx.threads = 1
        matrix = CCMArbBuilder(m, N).even_block()
        try:
            lambdas, vectors, algorithm = compute_full_eig(matrix)
            return lambdas, vectors, algorithm, dps
        except Exception as exc:  # noqa: BLE001 - deliberate precision-escalation fallback
            last_exc = exc
            continue
    raise RuntimeError(
        f"full-spectrum eig failed even after precision bumps {PRECISION_BUMPS} "
        f"above base dps={base_dps} for m={m}, N={N}: {last_exc}"
    )


def build_ell_even(N: int, pi: arb) -> list[arb]:
    """ell_even[0] = 1/12; ell_even[i] = sqrt(2)/(2*pi^2*i^2) for i=1..N.

    See the module docstring's basis-mapping derivation.
    """
    sqrt2 = arb(2).sqrt()
    two_pi2 = 2 * pi * pi
    out = [arb(1) / 12]
    for i in range(1, N + 1):
        out.append(sqrt2 / (two_pi2 * arb(i * i)))
    return out


def dot(a: list[arb], b: list[arb]) -> arb:
    total = arb(0)
    for x, y in zip(a, b):
        total += x * y
    return total


def load_kappa_L(m: int) -> tuple[float, float] | None:
    """Read Probe 4's kappa and L for cell (m, N=m) at dps=240 from
    out/edge_ledger_ratio.json's probe4_records. Returns None if not found
    (caller treats a missing reference as SANITY_CHECK_SKIPPED, not a
    silent pass)."""
    if not RATIO_JSON.exists():
        return None
    data = json.loads(RATIO_JSON.read_text(encoding="utf-8"))
    for rec in data.get("probe4_records", []):
        if rec.get("m") == m and rec.get("N") == m and rec.get("dps") == 240:
            return float(rec["kappa"]), float(rec["L"])
    return None


def build_cell(m: int) -> dict[str, Any]:
    N = m
    dim = N + 1
    started = time.time()
    progress(f"[dualcert] m={m} N={N} dim={dim} full-spectrum eig at dps>={BASE_DPS} ...")
    lambdas, vectors, algorithm, dps_effective = robust_full_eig(m, N, BASE_DPS)
    progress_done()

    ctx.dps = dps_effective
    ctx.threads = 1

    # Unit-normalize every eigenvector explicitly (belt-and-suspenders on
    # top of flint's own claimed unit-l2 normalization).
    vectors = [unit_normalize(v) for v in vectors]

    # Sign convention: v_1's n=0 (index 0) coordinate positive.
    if vectors[0][0].mid() < 0:
        vectors[0] = [-x for x in vectors[0]]

    pi = arb.pi()
    ell_even = build_ell_even(N, pi)
    ell_norm_sq = dot(ell_even, ell_even)

    lam1 = lambdas[0]
    xi0 = vectors[0][0]

    a_all = [dot(ell_even, vectors[j]) for j in range(dim)]
    a1 = a_all[0]

    # Sanity check: a_1/xi_0 must equal 2*kappa/L^2 from Probe 4 (ratio.json).
    kappa_L = load_kappa_L(m)
    ratio_computed = a1 / xi0
    ratio_computed_f = float(ratio_computed.mid())
    sanity: dict[str, Any] = {
        "a1_over_xi0": ratio_computed_f,
        "reference_source": str(RATIO_JSON.relative_to(REPO)) if kappa_L is not None else None,
    }
    if kappa_L is None:
        sanity["status"] = "SANITY_CHECK_SKIPPED_NO_REFERENCE"
        sanity["two_kappa_over_L2"] = None
        sanity["agree_8sig"] = None
    else:
        kappa_ref, L_ref = kappa_L
        two_kappa_over_L2 = 2.0 * kappa_ref / (L_ref * L_ref)
        agree = sig_agree(arb(repr(ratio_computed_f)), arb(repr(two_kappa_over_L2)), SANITY_SIG_DIGITS)
        sanity["two_kappa_over_L2"] = two_kappa_over_L2
        sanity["kappa_ref"] = kappa_ref
        sanity["L_ref"] = L_ref
        sanity["agree_8sig"] = agree
        sanity["status"] = "OK" if agree else "BASIS_MAPPING_MISMATCH"

    # w_j = a_j/(lambda_j - lambda_1) for j = 2..dim (index 1..dim-1).
    w_all = [a_all[j] / (lambdas[j] - lam1) for j in range(1, dim)]
    u_norm_sq = dot(w_all, w_all)
    w2_sq = w_all[0] * w_all[0]
    gap_share = w2_sq / u_norm_sq

    # ||P_perp ell||^2 = ||ell||^2 - a1^2 (Parseval, ell_even in the
    # orthonormal eigenbasis). Cross-checked against sum_{j>=2} a_j^2.
    pperp_norm_sq_direct = ell_norm_sq - a1 * a1
    a_sq_tail_sum = dot(a_all[1:], a_all[1:])
    pperp_norm_sq_via_sum = a_sq_tail_sum
    pperp_cross_check_agree = sig_agree(pperp_norm_sq_direct, pperp_norm_sq_via_sum, 6)

    u_norm = u_norm_sq.sqrt()
    pperp_norm = pperp_norm_sq_direct.sqrt()
    delta = lambdas[1] - lam1
    pay = u_norm * delta / pperp_norm

    n_cum = min(CUMULATIVE_J_UPTO, dim) - 1  # number of w-terms among j=2..CUMULATIVE_J_UPTO
    cumulative_share = dot(w_all[:n_cum], w_all[:n_cum]) / u_norm_sq if n_cum > 0 else arb(0)

    n_report = min(MAX_REPORT_J, dim)
    lambdas_report = [decimal_str(lambdas[j]) for j in range(n_report)]
    a_report = [decimal_str(a_all[j]) for j in range(n_report)]

    a2 = a_all[1] if dim > 1 else None
    v2_0 = vectors[1][0] if dim > 1 else None
    a2_over_v2_0 = (a2 / v2_0) if (a2 is not None and v2_0 is not None) else None

    elapsed = time.time() - started
    result = {
        "m": m,
        "N": N,
        "dim": dim,
        "dps_base": BASE_DPS,
        "dps_effective": dps_effective,
        "eigen_algorithm": algorithm,
        "sign_convention_note": (
            "v1 sign-fixed so v1_even[0] (xi_0) > 0; v2..v6 left at flint's own "
            "arbitrary sign (every reported quantity for them is sign-invariant)"
        ),
        "lambda1": bounds(lam1),
        "lambda2": bounds(lambdas[1]),
        "delta_lambda2_minus_lambda1": bounds(delta),
        "xi0_v1": bounds(xi0),
        "lambda_j_leq6": lambdas_report,
        "a_j_leq6": a_report,
        "basis_mapping_sanity_check": sanity,
        "a2": bounds(a2) if a2 is not None else None,
        "v2_0": bounds(v2_0) if v2_0 is not None else None,
        "a2_over_v2_0": bounds(a2_over_v2_0) if a2_over_v2_0 is not None else None,
        "u_norm_sq": bounds(u_norm_sq),
        "u_norm": bounds(u_norm),
        "gap_share_w2sq_over_unormsq": bounds(gap_share),
        "cumulative_share_j2to6": bounds(cumulative_share),
        "cumulative_share_j_upto": min(CUMULATIVE_J_UPTO, dim),
        "ell_norm_sq": bounds(ell_norm_sq),
        "pperp_ell_norm_sq_direct": bounds(pperp_norm_sq_direct),
        "pperp_ell_norm_sq_via_eigensum": bounds(pperp_norm_sq_via_sum),
        "pperp_cross_check_agree_6sig": pperp_cross_check_agree,
        "pperp_ell_norm": bounds(pperp_norm),
        "pay": bounds(pay),
        "gap_share_float": float(gap_share.mid()),
        "pay_float": float(pay.mid()),
        "cumulative_share_float": float(cumulative_share.mid()),
        "elapsed_seconds": elapsed,
    }
    return result


def evaluate_verdict(cells: list[dict[str, Any]]) -> tuple[str, str]:
    gap_shares = [c["gap_share_float"] for c in cells]
    if all(g >= GAP_SHARE_CONFIRM_THRESHOLD for g in gap_shares):
        return "CONFIRMED", VERDICT_CONFIRMED_LINE
    if all(g <= GAP_SHARE_REFUTE_THRESHOLD for g in gap_shares):
        return "REFUTED", VERDICT_REFUTED_LINE
    return "UNRESOLVED", VERDICT_UNRESOLVED_LINE


def write_json(cells: list[dict[str, Any]], verdict: str, verdict_line: str, out_path: Path) -> None:
    result = {
        "schema": "EdgeLedgerDualCert.v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "route": "CHALLENGER_NOT_RH",
        "promotion": "FORBIDDEN",
        "px_rh_claim": "NOT_MADE",
        "semantic_boundary": "finite_CCM_even_sector_diagnostic_only; not_a_certificate; DIAGNOSTIC_NEVER_A_PROOF",
        "precommit": str(PRECOMMIT.relative_to(REPO)),
        "addendum": "ADDENDUM 3 (2026-09-03 13:15), Probe 5",
        "prediction": "P_DUAL_CERT_PAYS_GAP p=0.75",
        "schedule_m": list(SCHEDULE_M),
        "cells": cells,
        "verdict": verdict,
        "verdict_line_quoted": verdict_line,
    }
    out_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_markdown(cells: list[dict[str, Any]], verdict: str, verdict_line: str, out_path: Path) -> None:
    lines = []
    lines.append("# Probe 5 report -- dual annihilator vs. absolute gap (R1)")
    lines.append("")
    lines.append(
        "Precommit: `PRECOMMIT_2026-09-03_edge_ledger_probes.md`, ADDENDUM 3 "
        "(2026-09-03 13:15). Judge context: attack R1 "
        "(`P59_CURVATURE_DUAL_ANNIHILATOR`), section 4 of "
        "`docs/routeB_bus/proshka/"
        "PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md`."
    )
    lines.append("")
    lines.append("## Basis-mapping statement")
    lines.append("")
    lines.append(
        "ell_N in +-N coordinates: ell_0 = 1/12, ell_n = 1/(2*pi^2*n^2) for n != 0. "
        "Mapped into the even eigenbasis by the SAME row-0 rule "
        "edge_ledger_build.even_block() uses for the n=0 interaction row "
        "(off-diagonal entries scaled by sqrt(2), the n=0/i=0 entry itself "
        "unscaled): ell_even[0] = 1/12, ell_even[i] = sqrt(2)/(2*pi^2*i^2) for "
        "i = 1..N. This reproduces the plain +-N dot product <ell_N, c> exactly "
        "as the plain dot product ell_even . xi_even (isometry proof in the "
        "script's module docstring)."
    )
    lines.append("")
    lines.append("## Sign convention")
    lines.append("")
    lines.append(
        "v1 (lambda1's eigenvector) is sign-fixed so its n=0/i=0 coordinate "
        "xi_0 is positive. v2..v6 are left at flint's arbitrary sign; every "
        "reported quantity for them (a_j via w_j^2, gap_share, pay, "
        "a2/v2_0) is invariant under a global sign flip of the eigenvector."
    )
    lines.append("")
    lines.append("## Sanity check: a_1/xi_0 vs 2*kappa/L^2 (Probe 4 cross-check)")
    lines.append("")
    lines.append("| m | a_1/xi_0 (this script) | 2*kappa/L^2 (Probe 4, ratio.json) | agree (8 sig) | status |")
    lines.append("|---|---|---|---|---|")
    for c in cells:
        s = c["basis_mapping_sanity_check"]
        lines.append(
            f"| {c['m']} | {s['a1_over_xi0']:.12g} | "
            f"{s['two_kappa_over_L2'] if s['two_kappa_over_L2'] is not None else 'N/A'} | "
            f"{s['agree_8sig']} | {s['status']} |"
        )
    lines.append("")
    lines.append("## Per-cell dual-certificate table")
    lines.append("")
    lines.append(
        "| m | dps_eff | lambda1 | lambda2 | a_1/xi_0 | a_2 | gap_share | pay | "
        "cumulative share j<=6 |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|")
    for c in cells:
        s = c["basis_mapping_sanity_check"]
        lines.append(
            f"| {c['m']} | {c['dps_effective']} | {c['lambda1']['ball']} | "
            f"{c['lambda2']['ball']} | {s['a1_over_xi0']:.10g} | "
            f"{c['a2']['ball'] if c['a2'] else 'N/A'} | "
            f"{c['gap_share_float']:.10g} | {c['pay_float']:.10g} | "
            f"{c['cumulative_share_float']:.10g} |"
        )
    lines.append("")
    lines.append(f"## Verdict: {verdict}")
    lines.append("")
    lines.append(f"Frozen rule quoted verbatim from the precommit: {verdict_line}")
    lines.append("")
    lines.append(
        "gap_share values by cell: "
        + ", ".join(f"m={c['m']}: {c['gap_share_float']:.6g}" for c in cells)
    )
    lines.append("")
    lines.append(
        "pperp cross-check (direct ||ell||^2-a1^2 vs sum_{j>=2} a_j^2) agrees to "
        "6 sig figs at every cell: "
        + str(all(c["pperp_cross_check_agree_6sig"] for c in cells))
    )
    lines.append("")
    lines.append("DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_json = OUT_DIR / "edge_ledger_dualcert.json"
    out_md = OUT_DIR / "edge_ledger_dualcert.md"

    cells: list[dict[str, Any]] = []
    for m in SCHEDULE_M:
        cell = build_cell(m)
        sanity = cell["basis_mapping_sanity_check"]
        print(
            f"[dualcert] m={m} dps_eff={cell['dps_effective']} "
            f"lambda1={cell['lambda1']['ball']} lambda2={cell['lambda2']['ball']} "
            f"gap_share={cell['gap_share_float']:.6g} pay={cell['pay_float']:.6g} "
            f"sanity={sanity['status']} elapsed={cell['elapsed_seconds']:.2f}s",
            flush=True,
        )
        if sanity["status"] == "BASIS_MAPPING_MISMATCH":
            print(
                "BASIS_MAPPING_MISMATCH at m="
                f"{m}: a1/xi0={sanity['a1_over_xi0']!r} vs "
                f"2*kappa/L^2={sanity['two_kappa_over_L2']!r} "
                "-- STOPPING, no further cells computed.",
                file=sys.stderr,
            )
            cells.append(cell)
            write_json(cells, "STOPPED_BASIS_MAPPING_MISMATCH", "n/a", out_json)
            return 2
        cells.append(cell)

    verdict, verdict_line = evaluate_verdict(cells)
    write_json(cells, verdict, verdict_line, out_json)
    write_markdown(cells, verdict, verdict_line, out_md)
    print(f"[dualcert] wrote {out_json}", flush=True)
    print(f"[dualcert] wrote {out_md}", flush=True)
    print(f"[dualcert] verdict: {verdict}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
