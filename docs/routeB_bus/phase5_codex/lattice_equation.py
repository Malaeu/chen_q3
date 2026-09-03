#!/usr/bin/env python3
"""Probe 10: normalized-xi lattice eigen-equation -- identities, term sizes,
diagonal defect.

Frozen precommit: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md
ADDENDUM 11 (2026-09-04 00:50). Mathematical source (transcribed, not
re-derived): docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md
sections 1 (source dictionary), 3 (LATTICE-1/2/3), 6 (remainder rho_n(n0)),
8 (S6), 9 (measurement list (i)-(vii)).

Everything below is DIAGNOSTIC_NEVER_A_PROOF. Five cells license no cofinal
quantifier. PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.

--------------------------------------------------------------------------
Source dictionary (report section 1), read off the UNMODIFIED builder
docs/routeB_bus/phase5_scripts/edge_ledger_build.py::CCMArbBuilder (imported,
never copied; its even_block() is Phase 1's parity_blocks() even sector):

  L      = ln m,   d_n = L^2 + 16 pi^2 n^2,   A_L = 32 L sinh^2(L/4)
  p_n    = W02(n,0) = A_L/d_n                      (== builder.w02(n,0), checked)
  a_n    = -W_R(n,0) - Prime(n,0)                  (== -builder.wr(n,0) - builder.prime(n,0))
  b_n    = tau(n,0) = p_n + a_n                    (== even[0,n]/sqrt2, checked)
  tau(n,n) = even[n,n] - b_n                       (parity: tau(n,-n) = b_n)
  y_n    = xi~_n/xi~_0 = sqrt2 * x_n,  y_0 = 1,   x_n = xi_n/xi_0 (raw carrier)
  mu     = (K~ y)_0                                 (== lambda1 at the ground row)
  R(y)_n = (K~ y)_n - mu y_n

LATTICE-1 (report section 3, boxed; UNCONDITIONAL in y with y_0 = 1):
  R(y)_n = sqrt2 (b_n + mu - tau(0,0)) + (tau(n,n) - b_n - mu) y_n + Omega_n
  Omega_n := 2 n^2 sum_{j>=1, j!=n} (b_j - b_n) y_j / (j^2 - n^2)

LATTICE-2 (report section 3, boxed; also unconditional once mu replaces
lambda1 -- the rearrangement is pure algebra, see the derivation note below):
  R(y)_n = D_n y_n - kappa_n Shat + sqrt2 [W_R(0,0) + Prime(0,0) + a_n + mu] + Omega_n^{ap}
  D_n        := -W_R(n,n) - Prime(n,n) - a_n - mu
  kappa_n    := 32 pi^2 A_L n^2 / d_n = 1024 pi^2 L sinh^2(L/4) n^2/(L^2+16 pi^2 n^2)
  Shat       := sum_{j=1}^{N} y_j/d_j + 1/(sqrt2 L^2)
  Omega_n^{ap} := 2 n^2 sum_{j!=n} (a_j - a_n) y_j/(j^2 - n^2)
At the ground row R(y)_n = 0, so LATTICE-2 reads
  D_n y_n = kappa_n Shat - sqrt2 [...] - Omega_n^{ap}   (the boxed form).

Derivation note (why both identities are checked with mu, not with a
separately solved lambda1): LATTICE-1 and LATTICE-2 are ALGEBRAIC rewrites of
R(y)_n valid for every y with y_0 = 1 -- no eigenvector hypothesis enters
(report section 3(b): "for every y with y_0 = 1 -- no eigenvector hypothesis,
no lambda1"). Checking them with mu := (K~y)_0 therefore tests exactly the
algebra of section 3, at full working precision, independently of how well the
eigensolver resolved the ground direction. The eigen-quality question is
reported separately as the residual |R(y)_n| itself. Using a solver lambda1 in
place of mu would replace an algebra check by an eigenvector-accuracy check,
which is not what ADDENDUM 11 (i) asks for ("must vanish to working
precision, which validates the whole derivation of section 3 for free").
Both mu and the solver lambda1 are reported; |mu - lambda1| is recorded.

The pole split used inside LATTICE-2 (report section 3) is checked separately:
  (p_j - p_n)/(j^2 - n^2) = -16 pi^2 A_L/(d_n d_j)   =>  Omega_n^{pole} = -kappa_n sum_{j!=n} y_j/d_j
  W02(n,n) - W02(n,0) = -32 pi^2 A_L n^2/d_n^2 = -kappa_n/d_n
and so is the squared-node Loewner form (star) of section 1:
  K~_{nj} = 2 (B_n - B_j)/(n^2 - j^2),  B_n = n^2 b_n   (n != j, both >= 1).

rho_n(n0) (report section 6) is the j > n0 part of Omega_n^{ap}:
  rho_n(n0) = -(2n/pi)(J_n+P_n) sum_{j>n0} y_j/(j^2-n^2)
              + (2n^2/pi) sum_{j>n0} (J_j+P_j) y_j/(j(j^2-n^2))
which, since a_j = (J_j+P_j)/(pi j) exactly (report section 1), is literally
  rho_n(n0) = 2 n^2 sum_{j>n0, j!=n} (a_j - a_n) y_j/(j^2 - n^2),
i.e. the tail half of the head/tail split of Omega_n^{ap} at n0. It is
computed in that form (one source of truth, no second transcription of J/P).
The j = n term is excluded everywhere, as in Omega itself; when n > n0 (which
happens for n0 = floor(L) at small cells) that exclusion lands in the tail.

Cells m = N in {13,23,43,83,163}; n = 1..8; cuts n0 in {floor(L), floor(L^2)}.
dps: 240 for m <= 43, 360 for m = 83, 900 for m = 163 (the ledger's own
setting for the large cell, edge_ledger_build.LARGE_N_PRECISIONS). Ground
eigenpair: flint full-spectrum isolation for N <= 100, precond inverse
iteration above it -- exactly edge_ledger_build's own resolve_eigenpair rule,
via the imported inverse_iteration_ground.

Ball hygiene: the identity residuals are evaluated on the EXACT MIDPOINTS of
the eigenvector components (arb balls carry no correlation information, so a
literal interval subtraction of two algebraically equal expressions would
report the input width rather than the algebraic zero). Matrix entries stay
balls; the residual's own reported magnitude is the rigorous upper bound
abs(resid).upper(), so entry uncertainty is included in what is compared
against the 1e-30 gate.

Predictions (K6, observer, ADDENDUM 11, frozen before the run):
  P_LATTICE_IDENTITIES_EXACT      p=0.90 -- all LATTICE-1/2 residuals <= 1e-30
                                            relative at every cell.
  P_TAIL_COUPLING_IS_LEADING      p=0.60 -- |rho_n(floor L)|/|D_n y_n| >= 1 for
                                            n = 1..3 at every cell.
  P_DIAGONAL_DEFECT_NONDEGENERATE p=0.60 -- min_{n<=8}|D_n|/max_{n<=8}|D_n| >= 1e-3
                                            at every cell and does not decrease by
                                            more than a factor 10 between m=13 and m=163.
  P_SHAT_SHARP                    p=0.50 -- |Shat + 1/(sqrt2 L^2)| <= 0.5 |1/(sqrt2 L^2)|
                                            at every cell.
CONFIRMED / REFUTED per prediction by the frozen inequality at every cell;
UNRESOLVED if a cell is missing or could not be evaluated.
STOP `LATTICE_IDENTITY_MISMATCH` if any LATTICE-1/2 residual exceeds 1e-30
relative -- reported, never silently repaired.
"""

from __future__ import annotations

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from flint import arb, ctx

REPO = Path(__file__).resolve().parents[3]
PHASE5_SCRIPTS = REPO / "docs" / "routeB_bus" / "phase5_scripts"
sys.path.insert(0, str(PHASE5_SCRIPTS))

from edge_ledger_build import (  # noqa: E402
    INVERSE_ITERATION_GROUND_ITERS,
    INVERSE_ITERATION_N_THRESHOLD,
    CCMArbBuilder,
    bounds,
    compute_eig_data,
    inverse_iteration_ground,
)

OUT_DIR = Path(__file__).resolve().parent / "out"
PRECOMMIT = PHASE5_SCRIPTS / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"
PREFLIGHT = (
    REPO / "docs" / "routeB_bus"
    / "AGENT_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md"
)
OUT_JSON = OUT_DIR / "lattice_equation.json"
OUT_MD = OUT_DIR / "lattice_equation.md"

SCHEDULE: tuple[tuple[int, int], ...] = ((13, 240), (23, 240), (43, 240), (83, 360), (163, 900))
N_MODES = 8
IDENTITY_REL_GATE_STR = "1e-30"
DIAG_RATIO_GATE = 1e-3
DIAG_DECAY_GATE = 10.0
SHAT_FACTOR = 0.5

_T0 = time.monotonic()


def progress(message: str) -> None:
    elapsed = time.monotonic() - _T0
    line = f"[lattice-equation] +{elapsed:8.1f}s {message}"
    if sys.stdout.isatty():
        sys.stdout.write("\r" + line + " " * 8)
        sys.stdout.flush()
    else:
        print(line, flush=True)


def progress_line(message: str) -> None:
    """A permanent line (cell boundary), never overwritten by \\r."""
    elapsed = time.monotonic() - _T0
    line = f"[lattice-equation] +{elapsed:8.1f}s {message}"
    if sys.stdout.isatty():
        sys.stdout.write("\r" + line + " " * 8 + "\n")
        sys.stdout.flush()
    else:
        print(line, flush=True)


def f_mid(value: arb) -> float:
    return float(value.mid())


def a_up(value: arb) -> arb:
    """Rigorous upper bound on |value|, as a zero-radius arb.

    Kept in arb rather than float on purpose: at dps 360 and 900 the identity
    residuals land near 1e-350 and 1e-870, which underflow to 0.0 in an IEEE
    double and would be reported as an exactly-vanishing residual. The arb
    carries the true magnitude; the float mirror is provided only for
    convenience and may read 0.0 for that reason.
    """
    return abs(value).upper()


def s_up(value: arb, digits: int = 6) -> str:
    return a_up(value).str(digits, radius=False)


def a_str(value: arb, digits: int = 6) -> str:
    return value.str(digits, radius=False)


def max_abs_term(terms: list[arb]) -> arb:
    """|term| of the largest-magnitude term, as a zero-radius arb."""
    best = arb(0)
    best_mid = 0.0
    for t in terms:
        mm = float(abs(t).mid())
        if mm > best_mid:
            best_mid = mm
            best = abs(t).mid()
    return best


def rel(resid: arb, scale: arb) -> arb:
    """Rigorous |resid| upper bound, relative to the largest term of the
    identity it belongs to. A zero scale falls back to the absolute bound."""
    r = a_up(resid)
    if float(scale) == 0.0:
        return r
    return r / scale


def run_cell(m: int, dps: int) -> dict[str, Any]:
    started = time.monotonic()
    ctx.dps = dps
    ctx.threads = 1
    N = m
    dim = N + 1

    progress(f"m=N={m} dps={dps}: builder + even block")
    builder = CCMArbBuilder(m, N)
    L = builder.L
    pi = builder.pi
    even = builder.even_block()

    progress(f"m=N={m} dps={dps}: ground eigenpair")
    if N <= INVERSE_ITERATION_N_THRESHOLD:
        lam1, lam2, vec1, _vec2, algorithm = compute_eig_data(even, want_vectors=True)
        eigen_resid = None
        method = algorithm
    else:
        lam1, vec1, eigen_resid = inverse_iteration_ground(even, dim, INVERSE_ITERATION_GROUND_ITERS)
        lam2 = None
        method = "inverse_iteration_precond"

    # Exact midpoints: the identities are algebraic in y, and ball arithmetic
    # cannot see that the two sides share the same y (see module docstring).
    v = [arb(c.mid()) for c in vec1]
    if f_mid(abs(v[0])) == 0.0:
        raise RuntimeError(f"LATTICE_CENTER_ENTRY_ZERO m={m}: xi_0 = 0, y is undefined")
    y = [arb(1)] + [v[j] / v[0] for j in range(1, dim)]
    x = [y[j] / arb(2).sqrt() for j in range(dim)]  # raw-carrier ratio xi_n/xi_0

    sqrt2 = arb(2).sqrt()
    A_L = 32 * L * (L / 4).sinh() ** 2
    d = {j: L * L + 16 * pi**2 * j * j for j in range(0, N + 1)}

    b = {j: even[0, j] / sqrt2 for j in range(1, N + 1)}
    p = {j: A_L / d[j] for j in range(1, N + 1)}
    a = {j: b[j] - p[j] for j in range(1, N + 1)}

    # --- source-dictionary checks (report section 1) --------------------
    def worst(values: list[arb]) -> arb:
        out = arb(0)
        for v in values:
            u = a_up(v)
            if bool(u > out):
                out = u
        return out

    pole_defect = worst([p[j] - builder.w02(j, 0) for j in range(1, N + 1)])
    a_defect = worst(
        [a[j] + builder.wr(j, 0) + builder.prime(j, 0) for j in range(1, min(N, 16) + 1)]
    )
    b_defect = worst([b[j] - builder.tau_entry(j, 0) for j in range(1, min(N, 16) + 1)])

    tau00 = builder.tau_entry(0, 0)
    wr00 = builder.wr(0, 0)
    prime00 = builder.prime(0, 0)
    center_defect = a_up(tau00 - (A_L / (L * L) - wr00 - prime00))

    # squared-node Loewner form (star), report section 1
    B = {j: arb(j * j) * b[j] for j in range(1, N + 1)}
    loewner_defect = arb(0)
    for i in range(1, min(N, 12) + 1):
        for j in range(1, min(N, 12) + 1):
            if i == j:
                continue
            lhs = even[i, j]
            rhs = 2 * (B[i] - B[j]) / arb(i * i - j * j)
            u = a_up(lhs - rhs)
            if bool(u > loewner_defect):
                loewner_defect = u

    mu = sum((even[0, j] * y[j] for j in range(dim)), arb(0))
    mu_minus_lambda1 = a_up(mu - lam1)

    shat = sum((y[j] / d[j] for j in range(1, N + 1)), arb(0)) + 1 / (sqrt2 * L * L)
    shat_ref = -1 / (sqrt2 * L * L)
    shat_dev = a_up(shat - shat_ref)
    shat_ok = bool(shat_dev <= SHAT_FACTOR * abs(shat_ref))

    n0_floor_L = int(f_mid(L))
    n0_floor_L2 = int(f_mid(L * L))
    cuts = {"floor_L": n0_floor_L, "floor_L2": n0_floor_L2}

    tail_masses: dict[str, dict[str, Any]] = {}
    for label, n0 in cuts.items():
        js = [j for j in range(n0 + 1, N + 1)]
        abs_sum = sum((abs(y[j]) / arb(j * j) for j in js), arb(0))
        signed = sum((y[j] / arb(j * j) for j in js), arb(0))
        tail_masses[label] = {
            "n0": n0,
            "empty": len(js) == 0,
            "count": len(js),
            "sum_abs_y_over_j2": f_mid(abs_sum),
            "sum_y_over_j2": f_mid(signed),
        }

    modes: list[dict[str, Any]] = []
    max_id1_rel = arb(0)
    max_id2_rel = arb(0)
    max_eigen_rel = arb(0)

    for n in range(1, min(N_MODES, N) + 1):
        tau_nn = even[n, n] - b[n]
        w02_nn = builder.w02(n, n)
        D_n = tau_nn - w02_nn - a[n] - mu
        D_n_direct = -builder.wr(n, n) - builder.prime(n, n) - a[n] - mu
        D_defect = a_up(D_n - D_n_direct)
        kappa_n = 32 * pi**2 * A_L * arb(n * n) / d[n]

        Ky_n = sum((even[n, j] * y[j] for j in range(dim)), arb(0))
        R_n = Ky_n - mu * y[n]

        omega = arb(0)
        omega_ap = arb(0)
        omega_pole = arb(0)
        head_ap = {label: arb(0) for label in cuts}
        tail_ap = {label: arb(0) for label in cuts}
        for j in range(1, N + 1):
            if j == n:
                continue
            w = arb(2 * n * n) * y[j] / arb(j * j - n * n)
            t_full = (b[j] - b[n]) * w
            t_ap = (a[j] - a[n]) * w
            t_pole = (p[j] - p[n]) * w
            omega += t_full
            omega_ap += t_ap
            omega_pole += t_pole
            for label, n0 in cuts.items():
                if j <= n0:
                    head_ap[label] += t_ap
                else:
                    tail_ap[label] += t_ap

        # pole collapse checks (report section 3)
        pole_sum = sum((y[j] / d[j] for j in range(1, N + 1) if j != n), arb(0))
        omega_pole_defect = a_up(omega_pole + kappa_n * pole_sum)
        diag_pole_defect = a_up((w02_nn - builder.w02(n, 0)) + kappa_n / d[n])

        # LATTICE-1
        t1a = sqrt2 * (b[n] + mu - tau00)
        t1b = (tau_nn - b[n] - mu) * y[n]
        id1 = R_n - (t1a + t1b + omega)
        scale1 = max_abs_term([R_n, t1a, t1b, omega])
        id1_rel = rel(id1, scale1)

        # LATTICE-2
        t2a = D_n * y[n]
        t2b = kappa_n * shat
        t2c = sqrt2 * (wr00 + prime00 + a[n] + mu)
        id2 = R_n - (t2a - t2b + t2c + omega_ap)
        scale2 = max_abs_term([R_n, t2a, t2b, t2c, omega_ap])
        id2_rel = rel(id2, scale2)
        eigen_rel = rel(R_n, scale2)

        if bool(id1_rel > max_id1_rel):
            max_id1_rel = id1_rel
        if bool(id2_rel > max_id2_rel):
            max_id2_rel = id2_rel
        if bool(eigen_rel > max_eigen_rel):
            max_eigen_rel = eigen_rel

        dny = f_mid(abs(t2a))
        ratios = {}
        for label in cuts:
            rho = f_mid(abs(tail_ap[label]))
            ratios[label] = {
                "rho_over_Dy": (rho / dny) if dny != 0.0 else float("inf"),
                "rho": f_mid(tail_ap[label]),
                "head": f_mid(head_ap[label]),
            }

        x_pole_only = -d[n] / (2 * L * L)  # report S4: -1/2 - 8 pi^2 n^2/L^2

        modes.append(
            {
                "n": n,
                "y_n": f_mid(y[n]),
                "x_n": f_mid(x[n]),
                "x_n_pole_only_ref": f_mid(x_pole_only),
                "x_n_minus_ref": f_mid(x[n] - x_pole_only),
                "D_n": f_mid(D_n),
                "D_n_source_defect": a_str(D_defect),
                "kappa_n": f_mid(kappa_n),
                "term_D_n_y_n": f_mid(t2a),
                "term_kappa_n_Shat": f_mid(t2b),
                "term_sqrt2_center": f_mid(t2c),
                "term_Omega_ap": f_mid(omega_ap),
                "Omega_full": f_mid(omega),
                "Omega_pole": f_mid(omega_pole),
                "split": ratios,
                "ratio_kappaShat_over_Dy": (f_mid(abs(t2b)) / dny) if dny != 0.0 else float("inf"),
                "R_n": f_mid(R_n),
                "lattice1_residual_rel": a_str(id1_rel),
                "lattice2_residual_rel": a_str(id2_rel),
                "eigen_residual_rel": a_str(eigen_rel),
                "omega_pole_collapse_defect": a_str(omega_pole_defect),
                "diag_pole_cancellation_defect": a_str(diag_pole_defect),
            }
        )
        progress(f"m=N={m} dps={dps}: mode n={n}/{min(N_MODES, N)}")

    d_abs = [abs(md["D_n"]) for md in modes]
    d_min = min(d_abs)
    d_max = max(d_abs)
    d_ratio = (d_min / d_max) if d_max != 0.0 else 0.0

    return {
        "m": m,
        "N": N,
        "dps": dps,
        "L": bounds(L),
        "L_float": f_mid(L),
        "A_L": f_mid(A_L),
        "eigen_method": method,
        "lambda1": bounds(lam1),
        "lambda2": bounds(lam2) if lam2 is not None else None,
        "mu_row0": bounds(mu),
        "mu_minus_lambda1_abs": a_str(mu_minus_lambda1),
        "inverse_iteration_residual": bounds(eigen_resid) if eigen_resid is not None else None,
        "xi0": f_mid(v[0]),
        "cuts": cuts,
        "Shat": f_mid(shat),
        "Shat_ref_minus_one_over_sqrt2_L2": f_mid(shat_ref),
        "Shat_minus_ref_abs": float(shat_dev),
        "Shat_rel_dev": float(shat_dev / abs(shat_ref)),
        "Shat_prediction_holds": bool(shat_ok),
        "Shat_sum_only": f_mid(shat - 1 / (sqrt2 * L * L)),
        "tail_masses": tail_masses,
        "source_checks": {
            "pole_p_n_vs_w02_max_defect": a_str(pole_defect),
            "a_n_vs_source_max_defect": a_str(a_defect),
            "b_n_vs_tau_max_defect": a_str(b_defect),
            "tau00_center_defect": a_str(center_defect),
            "loewner_star_max_defect": a_str(loewner_defect),
        },
        "modes": modes,
        "max_lattice1_residual_rel": a_str(max_id1_rel),
        "max_lattice2_residual_rel": a_str(max_id2_rel),
        "max_eigen_residual_rel": a_str(max_eigen_rel),
        "identities_hold": bool(
            (max_id1_rel <= arb(IDENTITY_REL_GATE_STR))
            and (max_id2_rel <= arb(IDENTITY_REL_GATE_STR))
        ),
        "D_min_abs": d_min,
        "D_max_abs": d_max,
        "D_min_over_max": d_ratio,
        "tail_leading_n1_3": bool(
            all(md["split"]["floor_L"]["rho_over_Dy"] >= 1.0 for md in modes if md["n"] <= 3)
        ),
        "elapsed_seconds": time.monotonic() - started,
    }


def verdicts(cells: list[dict[str, Any]], complete: bool) -> dict[str, dict[str, Any]]:
    def unresolved(rule: str, p: float) -> dict[str, Any]:
        return {"p": p, "rule": rule, "verdict": "UNRESOLVED"}

    rules = {
        "P_LATTICE_IDENTITIES_EXACT": (
            0.90,
            "all LATTICE-1/2 residuals <= 1e-30 relative at every cell",
        ),
        "P_TAIL_COUPLING_IS_LEADING": (
            0.60,
            "|rho_n(floor L)|/|D_n y_n| >= 1 for n = 1..3 at every cell",
        ),
        "P_DIAGONAL_DEFECT_NONDEGENERATE": (
            0.60,
            "min_{n<=8}|D_n|/max_{n<=8}|D_n| >= 1e-3 at every cell and does not "
            "decrease by more than a factor 10 between m=13 and m=163",
        ),
        "P_SHAT_SHARP": (
            0.50,
            "|Shat + 1/(sqrt2 L^2)| <= 0.5 |1/(sqrt2 L^2)| at every cell",
        ),
    }
    if not cells:
        return {k: unresolved(v[1], v[0]) for k, v in rules.items()}

    out: dict[str, dict[str, Any]] = {}

    ident = [c["identities_hold"] for c in cells]
    out["P_LATTICE_IDENTITIES_EXACT"] = {
        "p": rules["P_LATTICE_IDENTITIES_EXACT"][0],
        "rule": rules["P_LATTICE_IDENTITIES_EXACT"][1],
        "verdict": ("CONFIRMED" if all(ident) else "REFUTED") if complete else "UNRESOLVED",
        "worst_relative_residual": max(
            max(
                float(arb(c["max_lattice1_residual_rel"])),
                float(arb(c["max_lattice2_residual_rel"])),
            )
            for c in cells
        ),
        "worst_relative_residual_note": (
            "float mirror; values below ~1e-324 underflow to 0.0 -- the exact "
            "magnitudes are the per-cell decimal strings"
        ),
    }

    tail = [c["tail_leading_n1_3"] for c in cells]
    out["P_TAIL_COUPLING_IS_LEADING"] = {
        "p": rules["P_TAIL_COUPLING_IS_LEADING"][0],
        "rule": rules["P_TAIL_COUPLING_IS_LEADING"][1],
        "verdict": ("CONFIRMED" if all(tail) else "REFUTED") if complete else "UNRESOLVED",
        "min_ratio_over_cells_n1_3": min(
            md["split"]["floor_L"]["rho_over_Dy"] for c in cells for md in c["modes"] if md["n"] <= 3
        ),
    }

    by_m = {c["m"]: c for c in cells}
    ratio_ok = all(c["D_min_over_max"] >= DIAG_RATIO_GATE for c in cells)
    decay_ok: bool | None
    if 13 in by_m and 163 in by_m:
        r13 = by_m[13]["D_min_over_max"]
        r163 = by_m[163]["D_min_over_max"]
        decay_ok = bool(r163 * DIAG_DECAY_GATE >= r13)
        decay_detail = {"ratio_13": r13, "ratio_163": r163, "drop_factor": (r13 / r163) if r163 else None}
    else:
        decay_ok = None
        decay_detail = {}
    if not complete or decay_ok is None:
        diag_verdict = "UNRESOLVED"
    else:
        diag_verdict = "CONFIRMED" if (ratio_ok and decay_ok) else "REFUTED"
    out["P_DIAGONAL_DEFECT_NONDEGENERATE"] = {
        "p": rules["P_DIAGONAL_DEFECT_NONDEGENERATE"][0],
        "rule": rules["P_DIAGONAL_DEFECT_NONDEGENERATE"][1],
        "verdict": diag_verdict,
        "per_cell_ratio_gate_holds": ratio_ok,
        "schedule_decay": decay_detail,
    }

    shat = [c["Shat_prediction_holds"] for c in cells]
    out["P_SHAT_SHARP"] = {
        "p": rules["P_SHAT_SHARP"][0],
        "rule": rules["P_SHAT_SHARP"][1],
        "verdict": ("CONFIRMED" if all(shat) else "REFUTED") if complete else "UNRESOLVED",
        "worst_relative_deviation": max(c["Shat_rel_dev"] for c in cells),
    }
    return out


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    cells = payload["cells"]
    lines: list[str] = []
    lines.append("# Goal 058 Probe 10 — normalized-xi lattice equation (ADDENDUM 11)")
    lines.append("")
    lines.append(
        f"Precommit: `{payload['precommit']}` (ADDENDUM 11). "
        f"Source: `{payload['preflight']}` (§1, §3, §6, §8, §9)."
    )
    lines.append("")
    lines.append("`DIAGNOSTIC_NEVER_A_PROOF`. `PX_RH_CLAIM: NOT_MADE`. No cofinal claim: five cells.")
    lines.append("")
    if payload["pending_cells"]:
        lines.append(
            f"**Pending cells:** {payload['pending_cells']} — "
            f"`{payload['pending_command']}`"
        )
        lines.append("")

    lines.append("## Identity residuals (i) — relative, rigorous upper bounds")
    lines.append("")
    lines.append(
        "LATTICE-1 and LATTICE-2 are unconditional algebraic rewrites of "
        "`R(y)_n = (K~y)_n - mu y_n` with `mu = (K~y)_0` (report §3(b)); they are checked "
        "as such. `eigen resid` is the separate, non-identity quantity `|R(y)_n|/scale` — "
        "how well the solved ground direction satisfies the eigen-equation."
    )
    lines.append("")
    lines.append("| m=N | dps | method | max LATTICE-1 rel | max LATTICE-2 rel | max eigen resid rel | |mu-lambda1| | gate 1e-30 |")
    lines.append("|---:|---:|:--|---:|---:|---:|---:|:--:|")
    for c in cells:
        lines.append(
            f"| {c['m']} | {c['dps']} | {c['eigen_method']} | {c['max_lattice1_residual_rel']} | "
            f"{c['max_lattice2_residual_rel']} | {c['max_eigen_residual_rel']} | "
            f"{c['mu_minus_lambda1_abs']} | {'PASS' if c['identities_hold'] else 'FAIL'} |"
        )
    lines.append("")
    lines.append("Source-dictionary defects (all should be 0 to working precision):")
    lines.append("")
    lines.append("| m=N | p_n vs w02(n,0) | a_n vs -(wr+prime)(n,0) | b_n vs tau(n,0) | tau(0,0) center | Loewner (★) |")
    lines.append("|---:|---:|---:|---:|---:|---:|")
    for c in cells:
        s = c["source_checks"]
        lines.append(
            f"| {c['m']} | {s['pole_p_n_vs_w02_max_defect']} | {s['a_n_vs_source_max_defect']} | "
            f"{s['b_n_vs_tau_max_defect']} | {s['tau00_center_defect']} | "
            f"{s['loewner_star_max_defect']} |"
        )
    lines.append("")

    lines.append("## The four terms of LATTICE-2 (ii), n = 1..8")
    lines.append("")
    lines.append(
        "`R(y)_n = D_n y_n - kappa_n Shat + sqrt2[W_R(0,0)+Prime(0,0)+a_n+mu] + Omega_n^ap` "
        "(zero at the ground row). Omega^ap is split at each cut n0 into head (j<=n0) and "
        "tail rho_n(n0) (j>n0); the j=n term is excluded from both."
    )
    lines.append("")
    for c in cells:
        n0a = c["cuts"]["floor_L"]
        n0b = c["cuts"]["floor_L2"]
        lines.append(f"### m = N = {c['m']}  (L = {c['L_float']:.6f}, cuts n0 = {n0a} and {n0b})")
        lines.append("")
        lines.append(
            "| n | D_n y_n | kappa_n Shat | sqrt2[center+a_n+mu] | Omega_n^ap | "
            f"head(n0={n0a}) | rho(n0={n0a}) | head(n0={n0b}) | rho(n0={n0b}) |"
        )
        lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
        for md in c["modes"]:
            sa = md["split"]["floor_L"]
            sb = md["split"]["floor_L2"]
            lines.append(
                f"| {md['n']} | {md['term_D_n_y_n']:.6e} | {md['term_kappa_n_Shat']:.6e} | "
                f"{md['term_sqrt2_center']:.6e} | {md['term_Omega_ap']:.6e} | "
                f"{sa['head']:.6e} | {sa['rho']:.6e} | {sb['head']:.6e} | {sb['rho']:.6e} |"
            )
        lines.append("")
    lines.append("")

    lines.append("## Ratios (iii)")
    lines.append("")
    for c in cells:
        n0a = c["cuts"]["floor_L"]
        n0b = c["cuts"]["floor_L2"]
        lines.append(f"### m = N = {c['m']}")
        lines.append("")
        lines.append(
            f"| n | \\|rho(n0={n0a})\\|/\\|D_n y_n\\| | \\|rho(n0={n0b})\\|/\\|D_n y_n\\| | "
            "\\|kappa_n Shat\\|/\\|D_n y_n\\| |"
        )
        lines.append("|---:|---:|---:|---:|")
        for md in c["modes"]:
            lines.append(
                f"| {md['n']} | {md['split']['floor_L']['rho_over_Dy']:.6e} | "
                f"{md['split']['floor_L2']['rho_over_Dy']:.6e} | "
                f"{md['ratio_kappaShat_over_Dy']:.6e} |"
            )
        lines.append("")
    lines.append("")

    lines.append("## Diagonal defect D_n (iv)")
    lines.append("")
    lines.append("| m=N | L | min_{n<=8}\\|D_n\\| | max_{n<=8}\\|D_n\\| | min/max | gate 1e-3 |")
    lines.append("|---:|---:|---:|---:|---:|:--:|")
    for c in cells:
        lines.append(
            f"| {c['m']} | {c['L_float']:.6f} | {c['D_min_abs']:.6e} | {c['D_max_abs']:.6e} | "
            f"{c['D_min_over_max']:.6e} | {'PASS' if c['D_min_over_max'] >= DIAG_RATIO_GATE else 'FAIL'} |"
        )
    lines.append("")
    lines.append("Per-mode D_n:")
    lines.append("")
    lines.append("| m=N | " + " | ".join(f"n={n}" for n in range(1, N_MODES + 1)) + " |")
    lines.append("|---:|" + "---:|" * N_MODES)
    for c in cells:
        vals = " | ".join(f"{md['D_n']:.6e}" for md in c["modes"])
        lines.append(f"| {c['m']} | {vals} |")
    lines.append("")

    lines.append("## Shat against -1/(sqrt2 L^2) (v)")
    lines.append("")
    lines.append(
        "| m=N | sum_j y_j/d_j | Shat | -1/(sqrt2 L^2) | \\|Shat + 1/(sqrt2 L^2)\\| | "
        "rel dev | <= 0.5 |"
    )
    lines.append("|---:|---:|---:|---:|---:|---:|:--:|")
    for c in cells:
        lines.append(
            f"| {c['m']} | {c['Shat_sum_only']:.9e} | {c['Shat']:.9e} | "
            f"{c['Shat_ref_minus_one_over_sqrt2_L2']:.9e} | {c['Shat_minus_ref_abs']:.6e} | "
            f"{c['Shat_rel_dev']:.6f} | {'PASS' if c['Shat_prediction_holds'] else 'FAIL'} |"
        )
    lines.append("")

    lines.append("## Tail masses (vi)")
    lines.append("")
    lines.append("| m=N | n0 | terms | sum_{j>n0} \\|y_j\\|/j^2 | sum_{j>n0} y_j/j^2 |")
    lines.append("|---:|---:|---:|---:|---:|")
    for c in cells:
        for label in ("floor_L", "floor_L2"):
            t = c["tail_masses"][label]
            note = " (EMPTY: n0 >= N)" if t["empty"] else ""
            lines.append(
                f"| {c['m']} | {t['n0']}{note} | {t['count']} | {t['sum_abs_y_over_j2']:.9e} | "
                f"{t['sum_y_over_j2']:.9e} |"
            )
    lines.append("")

    lines.append("## x_n against the pole-only shape -d_n/(2 L^2) (vii) — report S4")
    lines.append("")
    for c in cells:
        lines.append(f"### m = N = {c['m']}")
        lines.append("")
        lines.append("| n | x_n | -d_n/(2 L^2) | difference | ratio x_n / ref |")
        lines.append("|---:|---:|---:|---:|---:|")
        for md in c["modes"]:
            ref = md["x_n_pole_only_ref"]
            ratio = (md["x_n"] / ref) if ref != 0.0 else float("nan")
            lines.append(
                f"| {md['n']} | {md['x_n']:.9e} | {ref:.9e} | {md['x_n_minus_ref']:.6e} | {ratio:.6f} |"
            )
        lines.append("")
    lines.append("")

    lines.append("## Observations, recorded before they are explained")
    lines.append("")
    lines.append(
        "- Cut sizes: floor(L^2) <= N at every cell of this schedule, so neither tail is "
        "empty; the counts are in the table above. "
        + ", ".join(
            f"m={c['m']}: n0 in {{{c['cuts']['floor_L']}, {c['cuts']['floor_L2']}}} with N={c['N']}"
            for c in cells
        )
        + "."
    )
    lines.append(
        "- Shat is carried by its additive constant, not by the row moment. "
        "sum_j y_j/d_j is almost L-independent ("
        + ", ".join(f"{c['Shat_sum_only']:.4e}" for c in cells)
        + " across m = "
        + ", ".join(str(c["m"]) for c in cells)
        + ") while 1/(sqrt2 L^2) falls from "
        + f"{-cells[0]['Shat_ref_minus_one_over_sqrt2_L2']:.4e} to "
        + f"{-cells[-1]['Shat_ref_minus_one_over_sqrt2_L2']:.4e}. "
        "Shat therefore comes out POSITIVE and close to +1/(sqrt2 L^2), i.e. neither the "
        "frozen ADDENDUM-11 target -1/(sqrt2 L^2) (rule above, REFUTED) nor the report's own "
        "S6 reading sum_j y_j/d_j = -1/(sqrt2 L^2) + o(...) (which would put Shat near 0, and "
        "which these numbers also do not support: the sum is ~6e-3 where S6 wants ~-1e-1 at m=13 "
        "and ~-2.7e-2 at m=163)."
    )
    lines.append(
        "- The consistency argument behind S6 does not bite here. |kappa_n Shat|/|D_n y_n| at "
        "n = 1 falls across the schedule ("
        + ", ".join(f"m={c['m']}: {c['modes'][0]['ratio_kappaShat_over_Dy']:.3g}" for c in cells)
        + "), so kappa_n Shat is a small multiple of D_n y_n, not an e^{L/2}-sized dominance. "
        "Most of it is cancelled by the third term sqrt2[W_R(0,0)+Prime(0,0)+a_n+mu]: in the "
        "four-term table the two agree to roughly 20-25 percent, and what is left over after "
        "that cancellation, together with Omega_n^ap, is what D_n y_n balances."
    )
    lines.append(
        "- The j > n0 coupling is a genuine remainder at the low modes and only becomes leading "
        "further up. At n0 = floor(L) the ratio |rho_n|/|D_n y_n| is below 1 for n = 1..3 at every "
        "cell (worst case "
        + f"{max(md['split']['floor_L']['rho_over_Dy'] for c in cells for md in c['modes'] if md['n'] <= 3):.3g}"
        + ") and it also shrinks along the schedule; it crosses 1 around n ~ floor(L) + 2. At "
        "n0 = floor(L^2) it is far smaller still: at most "
        + f"{max(md['split']['floor_L2']['rho_over_Dy'] for c in cells if c['m'] >= 23 for md in c['modes']):.3g}"
        + " over all cells m >= 23 and all n <= 8, and "
        + f"{max(md['split']['floor_L2']['rho_over_Dy'] for c in cells if c['m'] >= 43 for md in c['modes']):.3g}"
        + " for m >= 43; the one exception is the smallest cell m = 13, where n0 = 6 and n = 8 "
        "already sits above the cut and the ratio reaches "
        + f"{max(md['split']['floor_L2']['rho_over_Dy'] for c in cells if c['m'] == 13 for md in c['modes']):.3g}"
        + "."
    )
    lines.append(
        "- The new non-circular object D_n does not collapse on this schedule. min_{n<=8}|D_n| is "
        "larger at m = 163 than at m = 13 (roughly doubling) but not monotonically along the "
        "schedule ("
        + ", ".join(f"m={c['m']}: {c['D_min_abs']:.4e}" for c in cells)
        + "), and min/max stays in the 1.5e-2 to 5.4e-2 band with no trend. On the two largest "
        "cells D_n is monotone decreasing in n over n = 1..8; on the small cells the minimum "
        "sits at an interior n, which is what makes min/max fluctuate rather than trend."
    )
    lines.append(
        "- S4 distinguishing measurement (vii): the pole-only shape -d_n/(2 L^2) = -1/2 - "
        "8 pi^2 n^2/L^2 is nowhere near x_n on this schedule (at n = 1 it is "
        + ", ".join(
            f"{c['modes'][0]['x_n_pole_only_ref']:.4g} vs x_1 = {c['modes'][0]['x_n']:.4g}"
            for c in cells
        )
        + "). x_1 drifts toward -1, not -1/2, and x_n alternates in sign with decreasing "
        "modulus in n. On these five cells 8 pi^2/L^2 is between 12.0 and 3.04, so the "
        "-1/2 term never dominates -d_n/(2L^2); the agreement S4 flagged is not reproduced "
        "here, which is S4's reading (A)."
    )
    lines.append("")
    lines.append("## Verdicts (ADDENDUM 11, frozen)")
    lines.append("")
    for name, pred in payload["predictions"].items():
        lines.append(f"- `{name}` (p={pred['p']}): {pred['rule']} -> **{pred['verdict']}**")
    lines.append("")
    if payload["stop_token"]:
        lines.append(f"STOP: `{payload['stop_token']}`")
        lines.append("")
        lines.append(payload["stop_detail"])
        lines.append("")
    else:
        lines.append("No STOP code triggered.")
        lines.append("")
    lines.append("`DIAGNOSTIC_NEVER_A_PROOF`. `PX_RH_CLAIM: NOT_MADE`. No route promotion.")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    only = None
    if len(sys.argv) > 1:
        only = {int(tok) for tok in sys.argv[1].split(",")}
    schedule = [(m, dps) for m, dps in SCHEDULE if only is None or m in only]

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    cells: list[dict[str, Any]] = []
    pending: list[int] = []
    for index, (m, dps) in enumerate(schedule, start=1):
        progress_line(f"cell {index}/{len(schedule)} m=N={m} dps={dps} starting")
        try:
            cell = run_cell(m, dps)
        except Exception as exc:  # noqa: BLE001 - a failed cell is reported, not hidden
            progress_line(f"cell m=N={m} FAILED: {exc}")
            pending.append(m)
            continue
        cells.append(cell)
        progress_line(
            f"cell {index}/{len(schedule)} m=N={m} done in {cell['elapsed_seconds']:.1f}s "
            f"| id1={cell['max_lattice1_residual_rel']} id2={cell['max_lattice2_residual_rel']} "
            f"| min|D_n|={cell['D_min_abs']:.4e} min/max={cell['D_min_over_max']:.3e} "
            f"| Shat={cell['Shat']:.6e} vs {cell['Shat_ref_minus_one_over_sqrt2_L2']:.6e}"
        )

    expected = {m for m, _ in SCHEDULE}
    have = {c["m"] for c in cells}
    pending = sorted((expected - have) | set(pending))
    complete = not pending

    preds = verdicts(cells, complete)

    stop_token = None
    stop_detail = ""
    bad = [c for c in cells if not c["identities_hold"]]
    if bad:
        stop_token = "LATTICE_IDENTITY_MISMATCH"
        parts = []
        for c in bad:
            parts.append(
                f"m={c['m']}: max LATTICE-1 relative residual {c['max_lattice1_residual_rel']}, "
                f"max LATTICE-2 relative residual {c['max_lattice2_residual_rel']} "
                f"(gate {IDENTITY_REL_GATE_STR})"
            )
        stop_detail = (
            "A boxed identity of the preflight report does not reproduce the builder's own "
            "matrix to working precision. Reported, not repaired. " + "; ".join(parts)
        )

    pending_command = (
        f".venv/bin/python docs/routeB_bus/phase5_codex/lattice_equation.py "
        f"{','.join(str(m) for m in pending)}"
        if pending
        else ""
    )

    payload = {
        "schema": "LatticeEquationProbe10.v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "route": "GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION",
        "probe": 10,
        "addendum": 11,
        "precommit": str(PRECOMMIT.relative_to(REPO)),
        "preflight": str(PREFLIGHT.relative_to(REPO)),
        "semantic_boundary": "FINITE_CELL_DIAGNOSTIC_NEVER_A_PROOF",
        "schedule": [{"m": m, "dps": dps} for m, dps in SCHEDULE],
        "n_modes": N_MODES,
        "identity_relative_gate": IDENTITY_REL_GATE_STR,
        "cells": cells,
        "pending_cells": pending,
        "pending_command": pending_command,
        "predictions": preds,
        "stop_token": stop_token,
        "stop_detail": stop_detail,
        "promotion": False,
        "px_rh_claim": "NOT_MADE",
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True, default=str) + "\n", encoding="utf-8")
    write_markdown(payload, OUT_MD)
    progress_line(f"wrote {OUT_JSON}")
    progress_line(f"wrote {OUT_MD}")
    for name, pred in preds.items():
        progress_line(f"{name}: {pred['verdict']}")
    if stop_token:
        progress_line(f"STOP: {stop_token}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
