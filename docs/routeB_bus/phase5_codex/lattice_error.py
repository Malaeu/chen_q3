#!/usr/bin/env python3
"""Probe 9: lattice error of the ledger's finite even eigenvector against
the true completed zeta xi, and the alternating-curvature decomposition of
kappa_k into a Xi-part, an error-part and an exact tail.

Frozen precommit: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md
ADDENDUM 10 (2026-09-03 21:20). All definitions, the two predictions and the
verdict rules are quoted from there, not re-derived here.

Coordinate convention for Xi (verified against
q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean lines 10-25):
  riemannXi(s)   = 1/2 + (1/2) s (s-1) completedRiemannZeta0(s)   (Mathlib's
                   pole-removed entire completion; agrees with the classical
                   xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s) away
                   from s=0,1 by completedRiemannZeta(s) = completedRiemannZeta0(s)
                   - 1/s - 1/(1-s), and by continuity everywhere, since both
                   sides are entire -- so the classical formula IS riemannXi).
  centeredXi(z)  = riemannXi(1/2 + i z)
This script implements Xi(z) := centeredXi(z) directly via the classical
formula in acb (acb.zeta, acb.gamma, acb.pi()), since s = 1/2 + i z never
hits the poles 0, 1 for real z. Verified: (a) Xi is real on the real axis
(im part checked at every evaluated sample point, relative to the working
ball's own accuracy); (b) kappa_Xi := -Xi''(0)/(2 Xi(0)) ~ 0.02310, computed
here from the exact Taylor coefficients of Xi via acb_series composition
(s(t) = 1/2 + i t, order-4 series through zeta/gamma/exp on the series ring)
-- this is the "or by acb series" alternative the task offers instead of a
finite h=1e-12 central difference, and avoids that difference's h^-2 noise
amplification entirely (the series coefficients are each individually
correctly-rounded arb balls, not a subtraction of nearly-equal numbers).

Per-cell definitions (m = N in {13,23,43,83,163}, xi from the ledger's
xi1_pm_index row at the cell's WORKING precision -- reusing
edge_ledger_ratio.py's RecordArb, which already implements the
WORKING_DPS_CAP_THRESHOLD/WORKING_DPS_FALLBACK rule for m=163's single
dps=900 record -- and Xi in acb at that same working precision, always
>= 120 dps >> the 60 dps floor the task asks for):

  x_n       = 2 pi n / L                                    (L = ln(m))
  f_k(x_n)  = (-1)^n xi_n / xi_0                             (exact P59 sampling,
              raw +-N index; ADDENDUM 10's own formula, checked against the
              kappa_k identity below rather than assumed)
  f(x_n)    = Xi(x_n) / Xi(0)
  Delta_n   = f_k(x_n) - f(x_n)
  W_k       = sum_{n<=N} |Delta_n| / n^2
  S_Xi      = 2 sum_{n<=N} (-1)^n (f(x_n) - 1) / x_n^2
  S_Delta   = 2 sum_{n<=N} (-1)^n Delta_n / x_n^2
  tail      = -(L^2 / (2 pi^2)) sum_{n>N} (-1)^n / n^2       (exact: the total
              alternating sum is -pi^2/12, so the n>N tail is a finite
              subtraction, never a literal infinite sum)
  kappa_check = S_Xi + S_Delta + tail, checked to >= 8 digits against Probe
              4's own kappa_k (docs/routeB_bus/phase5_scripts/out/edge_ledger_ratio.json)
              -- STOP ALTERNATING_FORM_MISMATCH if it fails (after first
              re-checking the xi_n vs xi_{-n} sign convention, moot for an
              even row).

Predictions (K6, observer, ADDENDUM 10):
  P_WEIGHTED_LATTICE_ERROR_POLYLOG (p=0.65): W_k * L^2 <= 10 at every cell.
  P_SUP_LATTICE_ERROR_POLYLOG      (p=0.45): sup_{n<=N} |Delta_n| * L^2 <= 10
                                              at every cell.
  CONFIRMED / REFUTED per prediction by the inequality holding (or failing)
  at every cell with a computed kappa_check; UNRESOLVED if any cell could
  not be computed/checked.

DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.
"""

from __future__ import annotations

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from flint import acb, acb_series, arb, ctx

REPO = Path(__file__).resolve().parents[3]
PHASE5_SCRIPTS = REPO / "docs" / "routeB_bus" / "phase5_scripts"
sys.path.insert(0, str(PHASE5_SCRIPTS))

from edge_ledger_ratio import (  # noqa: E402
    RecordArb,
    WORKING_DPS_CAP_THRESHOLD,
    WORKING_DPS_FALLBACK,
    load_ledger,
)

OUT_DIR = Path(__file__).resolve().parent / "out"
RATIO_JSON = PHASE5_SCRIPTS / "out" / "edge_ledger_ratio.json"
PRECOMMIT = PHASE5_SCRIPTS / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"
XI_LEAN_SOURCE = (
    REPO / "q3.lean.aristotle" / "Q3" / "Proofs" / "RouteB" / "ClassicalXiInterface.lean"
)
OUT_JSON = OUT_DIR / "lattice_error.json"
OUT_MD = OUT_DIR / "lattice_error.md"

SCHEDULE_M: list[int] = [13, 23, 43, 83, 163]
BOUND_THRESHOLD = 10.0
KAPPA_CHECK_SIG_DIGITS = 8
PROGRESS_INTERVAL_SECONDS = 60.0

_last_progress = 0.0
_t0 = time.time()


def progress(message: str, force: bool = False) -> None:
    global _last_progress
    now = time.time()
    if not force and now - _last_progress < PROGRESS_INTERVAL_SECONDS:
        return
    _last_progress = now
    el = now - _t0
    print(f"[progress {time.strftime('%H:%M:%S')}] +{int(el)}s {message}", file=sys.stderr, flush=True)


def sig_agree(a: float, b: float, sig: int = KAPPA_CHECK_SIG_DIGITS) -> bool:
    """Same convention as edge_ledger_build.py / edge_ledger_ratio.py's own
    sig_agree: relative difference < 0.5e-(sig-1)."""
    if a == 0.0 and b == 0.0:
        return True
    denom = max(abs(a), abs(b))
    if denom == 0.0:
        return True
    rel = abs(a - b) / denom
    return rel < 0.5 * 10 ** (-(sig - 1))


# --------------------------------------------------------------------------
# Xi in acb: classical formula xi(s) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s).
# --------------------------------------------------------------------------


def xi_complex(s: acb) -> acb:
    """Classical completed zeta xi(s), = Mathlib's riemannXi(s) (see module
    docstring for the algebraic identity), evaluated at the CURRENT ctx.dps
    working precision. Valid for any acb s (s = 1/2 real part here, so never
    hits the poles 0, 1 of the raw zeta(s)/(s-1) factor)."""
    pi = acb.pi()
    logpi = pi.log()
    half = acb("0.5")
    return half * s * (s - 1) * (-(s / 2) * logpi).exp() * (s / 2).gamma() * s.zeta()


def centered_xi(z: acb) -> acb:
    """centeredXi(z) = riemannXi(1/2 + i z) (ClassicalXiInterface.lean line 18)."""
    return xi_complex(acb("0.5") + acb(0, 1) * z)


def imag_rel_error(v: acb) -> float:
    """Relative size of the imaginary part of v against its own magnitude --
    the "Xi real on the real axis" check. Uses abs_upper() on both the
    imaginary ball and the value so a zero real part cannot divide by zero
    (falls back to the imaginary part's raw magnitude in that degenerate
    case, which will already be far below any real threshold at working
    precision)."""
    im_mag = v.imag.abs_upper()
    val_mag = v.abs_upper()
    if val_mag == 0:
        return float(im_mag)
    return float(im_mag) / float(val_mag)


def compute_kappa_xi(work_dps: int = 90) -> dict[str, Any]:
    """kappa_Xi = -Xi''(0) / (2 Xi(0)) via the exact Taylor coefficients of
    Xi(t) = xi_complex(1/2 + i t) at t=0, obtained by composing zeta/gamma/exp
    on the acb_series ring with s(t) = 1/2 + i t (order-4 series) -- the
    "acb series" alternative to a finite central difference (module
    docstring). c0 = Xi(0), c1 = Xi'(0) (must vanish -- Xi is even, checked
    below), c2 = Xi''(0)/2."""
    ctx.dps = work_dps + 15
    pi = acb.pi()
    logpi = pi.log()
    half = acb("0.5")
    prec = 4
    s = acb_series([half, acb(0, 1)] + [acb(0)] * (prec - 2), prec)
    half_s = s * half
    xi_series = half * (s * (s - 1)) * ((-(half_s) * logpi).exp()) * half_s.gamma() * s.zeta()
    c0, c1, c2 = xi_series.coeffs()[:3]
    xi0 = c0
    xipp0 = acb(2) * c2
    kappa_xi = -xipp0 / (acb(2) * xi0)
    return {
        "working_dps": work_dps,
        "Xi0": float(xi0.real),
        "Xi0_imag_rel_error": imag_rel_error(xi0),
        "Xi_prime_0": float(c1.real),
        "Xi_prime_0_abs": float(c1.abs_upper()),
        "Xi_pp_0": float(xipp0.real),
        "kappa_Xi": float(kappa_xi.real),
        "kappa_Xi_imag_rel_error": imag_rel_error(kappa_xi),
    }


def load_probe4_kappa() -> dict[int, float]:
    """Probe 4's own kappa_k per m (main_schedule role, m == N), highest
    dps entry per cell -- the ADDENDUM 10 cross-check target."""
    if not RATIO_JSON.exists():
        raise SystemExit(f"missing {RATIO_JSON}; run edge_ledger_ratio.py first")
    payload = json.loads(RATIO_JSON.read_text(encoding="utf-8"))
    by_m: dict[int, tuple[int, float]] = {}
    for rec in payload["probe4_records"]:
        m, n_val, dps = rec["m"], rec["N"], rec["dps"]
        if m != n_val:
            continue  # skip the n_check partners (13:26, 43:86)
        prev = by_m.get(m)
        if prev is None or dps > prev[0]:
            by_m[m] = (dps, rec["kappa"])
    return {m: v[1] for m, v in by_m.items()}


def best_main_schedule_record(m: int) -> dict[str, Any]:
    records = load_ledger()
    if records is None:
        raise SystemExit(f"missing {PHASE5_SCRIPTS / 'out' / 'edge_ledger.json'}")
    candidates = [r for r in records if r["m"] == m and r["N"] == m and r["role"] == "main_schedule"]
    if not candidates:
        raise SystemExit(f"no main_schedule record for m={m} in edge_ledger.json")
    return max(candidates, key=lambda r: r["dps"])


def alt_sum_1_to_N(n_max: int, work_dps_ctx: int) -> arb:
    """sum_{n=1}^{n_max} (-1)^n / n^2, exact arb (finite loop, tiny N<=163)."""
    total = arb(0)
    for n in range(1, n_max + 1):
        sgn = -1 if (n % 2) else 1
        total += sgn * (arb(1) / arb(n * n))
    return total


def run_cell(m: int, kappa_probe4: float) -> dict[str, Any]:
    raw = best_main_schedule_record(m)
    rec = RecordArb(raw)  # sets ctx.dps = rec.dps + 15 as a side effect
    N = rec.N
    L = rec.L
    L_float = rec.L_float
    pi2 = rec.pi * rec.pi
    xi0 = rec.xi0

    Xi0_acb = centered_xi(acb(0))
    xi0_imag_rel = imag_rel_error(Xi0_acb)
    Xi0_re = Xi0_acb.real

    S_Xi = arb(0)
    S_Delta = arb(0)
    kappa_direct = arb(0)  # 2 sum (-1)^n (f_k(x_n)-1)/x_n^2, independent cross-check
    W_k = arb(0)
    partial_alt = arb(0)
    deltas: list[float] = []
    xi_imag_rel_max = xi0_imag_rel

    for n in range(1, N + 1):
        sgn = -1 if (n % 2) else 1
        x_n = rec.two_pi_over_L * n
        x_n2 = x_n * x_n
        f_k_n = sgn * (rec.xi_at(n) / xi0)
        Xi_n_acb = centered_xi(x_n)
        rel = imag_rel_error(Xi_n_acb)
        if rel > xi_imag_rel_max:
            xi_imag_rel_max = rel
        f_n = Xi_n_acb.real / Xi0_re
        delta_n = f_k_n - f_n
        deltas.append(float(delta_n.mid()))

        inv_n2 = arb(1) / arb(n * n)
        W_k += abs(delta_n) * inv_n2
        S_Xi += 2 * sgn * (f_n - 1) / x_n2
        S_Delta += 2 * sgn * delta_n / x_n2
        kappa_direct += 2 * sgn * (f_k_n - 1) / x_n2
        partial_alt += sgn * inv_n2

        if n % 20 == 0 or n == N:
            progress(f"m={m} n={n}/{N}")

    tail_alt = (-pi2 / 12) - partial_alt  # sum_{n>N} (-1)^n/n^2, exact closed form
    tail = -(L * L / (2 * pi2)) * tail_alt

    kappa_check = S_Xi + S_Delta + tail
    kappa_direct_total = kappa_direct + tail

    kappa_check_f = float(kappa_check.mid())
    kappa_direct_f = float(kappa_direct_total.mid())
    kappa_agree = sig_agree(kappa_check_f, kappa_probe4)
    direct_agree = sig_agree(kappa_direct_f, kappa_probe4)

    W_k_f = float(W_k.mid())
    delta_abs = [abs(d) for d in deltas]
    sup_delta = max(delta_abs)
    n_star = delta_abs.index(sup_delta) + 1  # deltas[0] is n=1

    return {
        "m": m,
        "N": N,
        "dps_record": rec.record_dps,
        "dps_working": rec.dps,
        "L": L_float,
        "Xi0": float(Xi0_re.mid()),
        "Xi0_imag_rel_error": xi0_imag_rel,
        "Xi_imag_rel_error_max_over_samples": xi_imag_rel_max,
        "W_k": W_k_f,
        "W_k_times_L2": W_k_f * L_float * L_float,
        "sup_delta": sup_delta,
        "sup_delta_times_L2": sup_delta * L_float * L_float,
        "n_star": n_star,
        "S_Xi": float(S_Xi.mid()),
        "S_Delta": float(S_Delta.mid()),
        "tail": float(tail.mid()),
        "kappa_check": kappa_check_f,
        "kappa_direct": kappa_direct_f,
        "kappa_probe4": kappa_probe4,
        "kappa_check_agrees_8sig": kappa_agree,
        "kappa_direct_agrees_8sig": direct_agree,
        "delta_n_low_modes": deltas[:8],
        "weighted_bound_holds": (W_k_f * L_float * L_float) <= BOUND_THRESHOLD,
        "sup_bound_holds": (sup_delta * L_float * L_float) <= BOUND_THRESHOLD,
    }


def main() -> None:
    progress("start", force=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    kappa_ref = load_probe4_kappa()
    kappa_xi_info = compute_kappa_xi()
    progress(f"kappa_Xi = {kappa_xi_info['kappa_Xi']:.10g}", force=True)

    cells: list[dict[str, Any]] = []
    stop_token: str | None = None
    for m in SCHEDULE_M:
        if m not in kappa_ref:
            raise SystemExit(f"no Probe 4 kappa_k for m={m} in {RATIO_JSON}")
        progress(f"cell m={m} starting", force=True)
        cell = run_cell(m, kappa_ref[m])
        progress(
            f"cell m={m} done: W_k*L2={cell['W_k_times_L2']:.6g} "
            f"sup|D|*L2={cell['sup_delta_times_L2']:.6g} kappa_agree={cell['kappa_check_agrees_8sig']}",
            force=True,
        )
        if not cell["kappa_check_agrees_8sig"] and not cell["kappa_direct_agrees_8sig"]:
            stop_token = "ALTERNATING_FORM_MISMATCH"
        cells.append(cell)

    have_all = len(cells) == len(SCHEDULE_M)
    all_kappa_ok = all(c["kappa_check_agrees_8sig"] or c["kappa_direct_agrees_8sig"] for c in cells)

    if stop_token is not None:
        weighted_verdict = "UNRESOLVED"
        sup_verdict = "UNRESOLVED"
    elif not have_all or not all_kappa_ok:
        weighted_verdict = "UNRESOLVED"
        sup_verdict = "UNRESOLVED"
    else:
        weighted_holds = [c["weighted_bound_holds"] for c in cells]
        sup_holds = [c["sup_bound_holds"] for c in cells]
        weighted_verdict = "CONFIRMED" if all(weighted_holds) else "REFUTED"
        sup_verdict = "CONFIRMED" if all(sup_holds) else "REFUTED"

    result = {
        "schema": "LatticeErrorProbe9.v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "precommit": str(PRECOMMIT.relative_to(REPO)),
        "addendum": "ADDENDUM 10",
        "xi_lean_source": str(XI_LEAN_SOURCE.relative_to(REPO)),
        "xi_convention": (
            "centeredXi(z) = riemannXi(1/2 + i z), riemannXi(s) = 1/2 + (1/2) s(s-1) "
            "completedRiemannZeta0(s); implemented here via the algebraically identical "
            "classical formula xi(s) = (1/2) s(s-1) pi^{-s/2} Gamma(s/2) zeta(s) in acb "
            "(valid since s = 1/2 + i*real never hits the poles 0,1)."
        ),
        "kappa_Xi_check": kappa_xi_info,
        "kappa_check_stop_token": stop_token,
        "cells": cells,
        "predictions": {
            "P_WEIGHTED_LATTICE_ERROR_POLYLOG": {
                "p": 0.65,
                "rule": "W_k * L^2 <= 10 at every cell",
                "verdict": weighted_verdict,
            },
            "P_SUP_LATTICE_ERROR_POLYLOG": {
                "p": 0.45,
                "rule": "sup_{n<=N} |Delta_n| * L^2 <= 10 at every cell",
                "verdict": sup_verdict,
            },
        },
        "diagnostic_never_a_proof": True,
        "px_rh_claim": "NOT_MADE",
    }
    OUT_JSON.write_text(json.dumps(result, indent=2, default=str) + "\n", encoding="utf-8")

    lines: list[str] = []
    lines.append("# Probe 9 -- lattice error against Xi and the alternating curvature form")
    lines.append("")
    lines.append(f"Precommit: `{result['precommit']}` (ADDENDUM 10). DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.")
    lines.append("")
    lines.append("## Xi convention")
    lines.append("")
    lines.append(result["xi_convention"])
    lines.append(f"Source checked: `{result['xi_lean_source']}` lines 10-25.")
    lines.append("")
    lines.append("## Xi implementation checks")
    lines.append("")
    ki = kappa_xi_info
    lines.append(f"- Xi(0) = {ki['Xi0']:.15g} (imag rel error {ki['Xi0_imag_rel_error']:.3e})")
    lines.append(f"- Xi'(0) = {ki['Xi_prime_0']:.3e} (should vanish -- Xi is even)")
    lines.append(f"- Xi''(0) = {ki['Xi_pp_0']:.15g}")
    lines.append(f"- kappa_Xi = -Xi''(0)/(2 Xi(0)) = {ki['kappa_Xi']:.10g}  (reference ~0.02310)")
    lines.append("")
    lines.append("## Per-cell table")
    lines.append("")
    lines.append("| m=N | dps (rec/work) | W_k*L^2 | sup|Delta|*L^2 | n* | S_Xi | S_Delta | tail | kappa_check | kappa_Probe4 | 8-sig agree |")
    lines.append("|---|---|---|---|---|---|---|---|---|---|---|")
    for c in cells:
        lines.append(
            f"| {c['m']} | {c['dps_record']}/{c['dps_working']} | {c['W_k_times_L2']:.6g} | "
            f"{c['sup_delta_times_L2']:.6g} | {c['n_star']} | {c['S_Xi']:.10g} | {c['S_Delta']:.10g} | "
            f"{c['tail']:.10g} | {c['kappa_check']:.10g} | {c['kappa_probe4']:.10g} | "
            f"{c['kappa_check_agrees_8sig'] or c['kappa_direct_agrees_8sig']} |"
        )
    lines.append("")
    lines.append("## Low-mode profile (Delta_n, n = 1..8)")
    lines.append("")
    for c in cells:
        vals = ", ".join(f"{v:.6e}" for v in c["delta_n_low_modes"])
        lines.append(f"- m={c['m']}: [{vals}]")
    lines.append("")
    lines.append("## Verdicts")
    lines.append("")
    for name, pred in result["predictions"].items():
        lines.append(f"- `{name}` (p={pred['p']}): {pred['rule']} -> **{pred['verdict']}**")
    if stop_token:
        lines.append("")
        lines.append(f"STOP: `{stop_token}`")
    OUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")
    progress("done", force=True)


if __name__ == "__main__":
    main()
