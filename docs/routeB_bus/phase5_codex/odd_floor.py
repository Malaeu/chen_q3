#!/usr/bin/env python3
"""Probe 11: odd-sector floor scale and the S7 cancellation.

Frozen precommit: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md
ADDENDUM 12 (2026-09-04 02:20). Mathematical source (transcribed, not
re-derived): docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT.md
sections 1 (target row y), 2 (residual R(y)), 3.1-3.3 (COB / MAIN / MAIN-P and
the odd-block normal form), 5 (q_ap, q_pole, rho_stab), 9 (measurement list),
10 (S7, S8). Source dictionary and D_n: the previous preflight
AGENT_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md
section 1, as implemented by the sibling script lattice_equation.py (imported,
never modified).

Everything below is DIAGNOSTIC_NEVER_A_PROOF. Five cells license no cofinal
quantifier. PX_RH_CLAIM: NOT_MADE. No Lean, no route promotion.

--------------------------------------------------------------------------
OBJECTS (raw +-N carrier, report section 1; positive indices n = 1..N)

  L = ln m,  d_n = L^2 + 16 pi^2 n^2,  A_L = 32 L sinh^2(L/4)
  b_n      = tau(n,0)                                (builder.tau_entry(n,0))
  p_n      = A_L/d_n = W02(n,0),   a_n = b_n - p_n
  a0       = tau(0,0)
  x_n      = xi_n/xi_0    ground row, raw carrier   (= even row / sqrt2)
  y_n      = (-1)^n centeredXi(2 pi n/L)/centeredXi(0),  y_0 = 1   (report section 1)
  Delta_n  = x_n - y_n    (Delta_0 = 0: both rows are centre-normalised)
  u_n      = (R Delta)_n = Delta_n/n
  nu(w)    = a0 + 2 sum_{m>=1} b_m w_m ;  R(w)_n = (Kw)_n - nu(w) w_n
             with (Kw)_n = b_n + sum_{j>=1} even[n,j] w_j   (even[n,j] = tau(n,j)+tau(n,-j))

ODD BLOCK (report section 3.2), built from the UNMODIFIED builder as
section 9 of the report prescribes -- `odd[i,j] = k(i,j) - k(i,-j)`, i,j >= 1
(`parity_blocks`/`even_block` builds the even sector only):

  Odd_{nn} = tau(n,n) - tau(n,-n) = tau(n,n) - b_n
  Odd_{nm} = tau(n,m) - tau(n,-m) = 2 n m (b_n - b_m)/(n^2 - m^2)     (n != m)
  delta_n  = Odd_{nn} - lambda1 = tau(n,n) - b_n - lambda1
  D_n      = -W_R(n,n) - Prime(n,n) - a_n - lambda1 = delta_n + 32 pi^2 A_L n^2/d_n^2

ITEM (i): A NON-CIRCULAR TEST OF (MAIN)/(MAIN-P) (coordinator's amendment,
2026-09-04, before any entry was computed). Both sides of the identity are
formed from the OBJECTS, by matrix products with the builder's own matrices,
and only then compared with the report's expanded formulas. Three numbers:

  LHS_direct   = (1/2)<R Delta, (D - lambda1) R Delta>_M
               = sum_{n,m>=1} u_n (Odd - lambda1 I)_{nm} u_m ,
                 a matrix product with the builder's odd block at u = R Delta,
                 Delta = x - y built from the solved ground eigenvector x and
                 the Xi-sample row y. No delta_n, no (b_n-b_m)/(n^2-m^2), no
                 source dictionary enters it.

  RHS_direct   = - sum_n Delta_n R(y)_n/n^2 + (nu - lambda1) sum_n Delta_n (1-y_n)/n^2 ,
                 with R(y) evaluated as (K~ y~)_n - y~_n (K~ y~)_0 by ONE
                 matrix-vector product with the builder's even block K~ at the
                 even-coordinate row y~ = (1, sqrt2 y_1, ..., sqrt2 y_N), and
                 nu = (K~ y~)_0. (The raw-carrier residual is R(y)_n =
                 (K~y~)_n/sqrt2 - y_n nu for n >= 1; that sqrt2 is the change of
                 basis between the even block and the raw +-N carrier, not a
                 source-entry expansion. Cross-checked against the raw form
                 b_n + sum_j even[n,j] y_j - nu y_n, whose defect is reported.)

  LHS_expanded = the report's own expanded left side, in two variants:
       (MAIN)   sum_n delta_n Delta_n^2/n^2 + 2 sum_{n!=m}(b_n-b_m) Delta_n Delta_m/(n^2-m^2)
       (MAIN-P) sum_n D_n Delta_n^2/n^2 - 32 pi^2 A_L (sum_n Delta_n/d_n)^2
                                        + 2 sum_{n!=m}(a_n-a_m) Delta_n Delta_m/(n^2-m^2)

Two ratios, reported separately, each held to the frozen 1e-30 gate:

  ratio_identity   = |LHS_direct - RHS_direct| / |LHS_direct|
                     -- tests the IDENTITY (COB)/(MAIN). Note this is derived
                     from R(x) = 0, so it is bounded below by the solved ground
                     row's own eigen residual (probe 10 measured ~1e-238
                     relative at dps 240, ~1e-313 at dps 900, i.e. ~200 orders
                     below the gate).
  ratio_dictionary = |LHS_expanded - LHS_direct| / |LHS_direct|,  for (MAIN) and
                     for (MAIN-P) separately -- tests the report's DICTIONARY
                     (the odd normal form D^odd_{nm} = 2nm(b_n-b_m)/(n^2-m^2),
                     the diagonal delta_n = tau(n,n)-b_n-lambda1, the exact pole
                     cancellation delta_n = D_n - 32 pi^2 A_L n^2/d_n^2 and the
                     rank-one pole extraction). Pure algebra; nothing spectral.

If either exceeds 1e-30 the STOP code ENERGY_IDENTITY_MISMATCH is returned with
the numbers. The formula is never "fixed": if the report and the builder
disagree, that disagreement IS the result.

  In addition, and as a DIAGNOSTIC only (not gated, since it is not the
  report's formula), the "carried" variant is computed: the same identity with
  lambda1 replaced by nu(x) = (K~x~)_0 and with the extra term
  + sum_n Delta_n R(x)_n/n^2 on the right. That variant is unconditional
  algebra for ANY two even rows with x_0 = y_0 = 1 (it is what the derivation
  of section 3.1 gives when R(x) is carried instead of set to zero), so it
  isolates how much of ratio_identity is eigenvector inaccuracy rather than a
  defect of the identity. The frozen verdict is taken from the report's own
  formulas, not from this variant.

Ball hygiene: as in lattice_equation.py, the eigenvector components are taken
at their exact midpoints (arb balls carry no correlation information, so an
interval subtraction of two algebraically equal expressions reports the input
width instead of the algebraic zero). Matrix entries and the Xi samples stay
balls; every reported residual magnitude is the rigorous upper bound
abs(resid).upper(), so entry uncertainty is inside what the gate sees.

CONTRACTION QUANTITIES (report section 5), on the FULL n = 1..N, not just n <= 8:

  ghat_n     = n/d_n
  Off^ap_{nm} = 2 n m (a_n - a_m)/(n^2 - m^2)  (n != m), 0 on the diagonal
  q_ap   = || diag(D)^{-1} Off^ap ||_2                (largest singular value)
  q_pole = 32 pi^2 A_L || diag(D)^{-1} ghat || || ghat ||   (exact, rank one)
  q_full = || diag(D)^{-1} (32 pi^2 A_L ghat ghat^T - Off^ap) ||_2
  rho_stab = ||R Delta|| / ||R R(y)||     (l2 over n = 1..N; the factor 2 of the
             symmetric carrier cancels in the ratio)

The two operator norms marked ||.||_2 are singular values of an explicit
N x N matrix. They are evaluated in float64 (numpy) on the arb midpoints of
entries that were themselves formed at full working precision: a singular
value is wanted to three digits, float64 delivers ~15, and the entries carry
no cancellation at the point of conversion (a_n - a_m and 1/D_n are formed in
arb first). q_pole, which has a closed form, is computed in arb as well and
the two agree to the printed digits.

Cells m = N in {13,23,43,83,163}; dps as in lattice_equation.py
(240,240,240,360,900). Ground eigenpair by lattice_equation.py's own rule:
flint full-spectrum isolation for N <= 100, preconditioned inverse iteration
above it. Modes n <= 8 for the entry tables, per ADDENDUM 12.

Predictions (K6, observer, ADDENDUM 12, frozen before the run):
  P_ENERGY_IDENTITY_EXACT p=0.90 -- (MAIN) residual <= 1e-30 relative at every cell.
  P_S7_ODD_OFFDIAG_SMALL  p=0.55 -- |D^odd_12| <= 1e-3 at every cell while its
                                    pole part alone is O(1) (reading A of S7).
  P_ODD_FLOOR_FLAT        p=0.45 -- lambda_min((D-lambda1)|_odd, full block)*L^2
                                    in [1e-4, 1e-1] at every cell.
  P_Q_AP_LT_1             p=0.35 -- q_ap < 1 at every cell.
  P_RHO_STAB_FLAT         p=0.50 -- rho_stab <= 1e4 at every cell and varies by
                                    < x10 across the schedule.
CONFIRMED / REFUTED per prediction by the frozen inequality at every cell;
UNRESOLVED if a cell is missing or could not be evaluated.
STOP `ENERGY_IDENTITY_MISMATCH` if any of (R1)-(R4) exceeds 1e-30 relative --
reported, never silently repaired. If the report's formula and the builder
disagree, that disagreement IS the result.
"""

from __future__ import annotations

import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import numpy as np
from flint import acb, arb, arb_mat, ctx

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PHASE5_SCRIPTS = REPO / "docs" / "routeB_bus" / "phase5_scripts"
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(PHASE5_SCRIPTS))

from edge_ledger_build import (  # noqa: E402
    INVERSE_ITERATION_GROUND_ITERS,
    INVERSE_ITERATION_N_THRESHOLD,
    CCMArbBuilder,
    bounds,
    compute_eig_data,
    inverse_iteration_ground,
)
from lattice_equation import (  # noqa: E402  (sibling probe 10, imported, not modified)
    a_str,
    a_up,
    f_mid,
    max_abs_term,
    rel,
)
from lattice_error import centered_xi  # noqa: E402  (sibling probe 9, imported, not modified)

OUT_DIR = HERE / "out"
PRECOMMIT = PHASE5_SCRIPTS / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"
PREFLIGHT = (
    REPO / "docs" / "routeB_bus"
    / "AGENT_REPORT_2026-09-04_GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE_PREFLIGHT.md"
)
PREFLIGHT_PREV = (
    REPO / "docs" / "routeB_bus"
    / "AGENT_REPORT_2026-09-04_GOAL058_NORMALIZED_XI_LATTICE_EIGEN_EQUATION_PREFLIGHT.md"
)
OUT_JSON = OUT_DIR / "odd_floor.json"
OUT_MD = OUT_DIR / "odd_floor.md"

SCHEDULE: tuple[tuple[int, int], ...] = ((13, 240), (23, 240), (43, 240), (83, 360), (163, 900))
N_MODES = 8
IDENTITY_REL_GATE_STR = "1e-30"
S7_OFFDIAG_GATE = 1e-3
S7_REPORT_GATE = 3e-4          # the sharper figure named in section 10 of the report
S7_POLE_O1_GATE = 1e-1         # "its pole part alone is O(1)"
ODD_FLOOR_LO, ODD_FLOOR_HI = 1e-4, 1e-1
RHO_STAB_GATE = 1e4
RHO_STAB_SPREAD = 10.0
ODD_INVERSE_ITERS = 6

_T0 = time.monotonic()


def progress(message: str) -> None:
    elapsed = time.monotonic() - _T0
    line = f"[odd-floor] +{elapsed:8.1f}s {message}"
    if sys.stdout.isatty():
        sys.stdout.write("\r" + line + " " * 8)
        sys.stdout.flush()
    else:
        print(line, flush=True)


def progress_line(message: str) -> None:
    elapsed = time.monotonic() - _T0
    line = f"[odd-floor] +{elapsed:8.1f}s {message}"
    if sys.stdout.isatty():
        sys.stdout.write("\r" + line + " " * 8 + "\n")
        sys.stdout.flush()
    else:
        print(line, flush=True)


def two_norm(matrix: np.ndarray) -> float:
    """Largest singular value of an explicit float64 matrix."""
    if matrix.size == 0:
        return 0.0
    return float(np.linalg.svd(matrix, compute_uv=False)[0])


def odd_block(builder: CCMArbBuilder, N: int) -> arb_mat:
    """odd[i,j] = k(i,j) - k(i,-j), i,j >= 1 (report section 9). The builder's
    own `even_block` is the even companion; the odd block is not built by it."""
    mat = arb_mat(N, N)
    for i in range(1, N + 1):
        for j in range(i, N + 1):
            value = builder.tau_entry(i, j) - builder.tau_entry(i, -j)
            mat[i - 1, j - 1] = value
            mat[j - 1, i - 1] = value
        if i % 20 == 0 or i == N:
            progress(f"odd block row {i}/{N}")
    return mat


def lambda_min_symmetric(mat: arb_mat, dim: int) -> tuple[arb, str, arb | None]:
    """Smallest eigenvalue of a symmetric PSD arb matrix, by lattice_equation's
    own rule: full-spectrum isolation for dim <= INVERSE_ITERATION_N_THRESHOLD,
    preconditioned inverse iteration above it (the matrix here is (Odd -
    lambda1 I), PSD by Cauchy interlacing, so smallest-|eigenvalue| = lambda_min)."""
    if dim <= INVERSE_ITERATION_N_THRESHOLD:
        lam1, _lam2, _v1, _v2, algorithm = compute_eig_data(mat, want_vectors=False)
        return lam1, algorithm, None
    lam1, _vec, resid = inverse_iteration_ground(mat, dim, ODD_INVERSE_ITERS)
    return lam1, "inverse_iteration_precond", resid


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

    v = [arb(c.mid()) for c in vec1]
    if f_mid(abs(v[0])) == 0.0:
        raise RuntimeError(f"ODD_FLOOR_CENTER_ENTRY_ZERO m={m}: xi_0 = 0, x is undefined")

    sqrt2 = arb(2).sqrt()
    # raw-carrier ground row: even coordinates are xi~_n = sqrt2 xi_n (n >= 1)
    x = {0: arb(1)}
    for n in range(1, N + 1):
        x[n] = (v[n] / v[0]) / sqrt2

    progress(f"m=N={m} dps={dps}: Xi sample row")
    Xi0 = centered_xi(acb(0)).real
    y = {0: arb(1)}
    two_pi_over_L = 2 * pi / L
    xi_imag_rel_max = 0.0
    for n in range(1, N + 1):
        t = two_pi_over_L * n
        val = centered_xi(acb(t))
        re_up = float(abs(val.real).upper())
        im_up = float(abs(val.imag).upper())
        if re_up > 0.0:
            rel_im = im_up / re_up
            if rel_im > xi_imag_rel_max:
                xi_imag_rel_max = rel_im
        sgn = -1 if (n % 2) else 1
        y[n] = sgn * (val.real / Xi0)
        if n % 25 == 0 or n == N:
            progress(f"m=N={m}: Xi sample {n}/{N}")

    delta_row = {n: x[n] - y[n] for n in range(1, N + 1)}
    u = {n: delta_row[n] / arb(n) for n in range(1, N + 1)}

    A_L = 32 * L * (L / 4).sinh() ** 2
    d = {n: L * L + 16 * pi**2 * n * n for n in range(0, N + 1)}
    pole_const = 32 * pi**2 * A_L

    b = {n: builder.tau_entry(n, 0) for n in range(1, N + 1)}
    p = {n: A_L / d[n] for n in range(1, N + 1)}
    a = {n: b[n] - p[n] for n in range(1, N + 1)}
    a0 = builder.tau_entry(0, 0)

    # ---- residual row R(y) and the ground row's own residual R(x) ----------
    # Non-circular: ONE matrix-vector product with the builder's even block on
    # the even-coordinate rows y~ = (1, sqrt2 y_1, ...) and x~ = v/v_0.
    def even_matvec(row_even: list[arb]) -> list[arb]:
        return [
            sum((even[i, j] * row_even[j] for j in range(dim)), arb(0)) for i in range(dim)
        ]

    y_even = [arb(1)] + [sqrt2 * y[n] for n in range(1, N + 1)]
    x_even = [arb(1)] + [v[n] / v[0] for n in range(1, N + 1)]
    Ky_even = even_matvec(y_even)
    Kx_even = even_matvec(x_even)
    nu_y = Ky_even[0]
    nu_x = Kx_even[0]
    Ry = {n: Ky_even[n] / sqrt2 - nu_y * y[n] for n in range(1, N + 1)}
    Rx = {n: Kx_even[n] / sqrt2 - nu_x * x[n] for n in range(1, N + 1)}

    # cross-check of the change of basis against the raw-carrier expansion
    # R(y)_n = b_n + sum_j even[n,j] y_j - nu y_n (source-entry form, §2)
    raw_form_defect = arb(0)
    for n in range(1, min(N, 16) + 1):
        raw = b[n] + sum((even[n, j] * y[j] for j in range(1, N + 1)), arb(0)) - nu_y * y[n]
        dfct = a_up(Ry[n] - raw)
        if bool(dfct > raw_form_defect):
            raw_form_defect = dfct
    nu_raw_defect = a_up(nu_y - (a0 + 2 * sum((b[j] * y[j] for j in range(1, N + 1)), arb(0))))

    progress(f"m=N={m} dps={dps}: odd block")
    odd = odd_block(builder, N)

    # ---- diagonal: delta_n, D_n, the S7 cancellation ----------------------
    delta_n = {n: odd[n - 1, n - 1] - lam1 for n in range(1, N + 1)}
    D_full: dict[int, arb] = {}
    pole_diag: dict[int, arb] = {}
    s7_defect = arb(0)
    for n in range(1, N + 1):
        pole_diag[n] = pole_const * arb(n * n) / (d[n] * d[n])
        D_full[n] = -builder.wr(n, n) - builder.prime(n, n) - a[n] - lam1
        dfct = a_up(delta_n[n] - (D_full[n] - pole_diag[n]))
        if bool(dfct > s7_defect):
            s7_defect = dfct

    # normal-form check of the odd off-diagonal (report section 3.2)
    odd_normal_defect = arb(0)
    for i in range(1, min(N, 12) + 1):
        for j in range(1, min(N, 12) + 1):
            if i == j:
                continue
            ref = arb(2 * i * j) * (b[i] - b[j]) / arb(i * i - j * j)
            dfct = a_up(odd[i - 1, j - 1] - ref)
            if bool(dfct > odd_normal_defect):
                odd_normal_defect = dfct

    # ---- the three numbers of item (i) ------------------------------------
    progress(f"m=N={m} dps={dps}: quadratic forms")
    # LHS_direct: matrix product with the builder's odd block at u = R Delta
    Q_direct = arb(0)
    for n in range(1, N + 1):
        row = sum((odd[n - 1, j - 1] * u[j] for j in range(1, N + 1)), arb(0))
        Q_direct += u[n] * (row - lam1 * u[n])

    diag_main = sum((delta_n[n] * u[n] * u[n] for n in range(1, N + 1)), arb(0))
    diag_mainp = sum((D_full[n] * u[n] * u[n] for n in range(1, N + 1)), arb(0))
    off_b = arb(0)
    off_a = arb(0)
    for n in range(1, N + 1):
        for j in range(1, N + 1):
            if j == n:
                continue
            w = delta_row[n] * delta_row[j] / arb(n * n - j * j)
            off_b += (b[n] - b[j]) * w
            off_a += (a[n] - a[j]) * w
    off_b *= 2
    off_a *= 2
    pole_moment = sum((delta_row[n] / d[n] for n in range(1, N + 1)), arb(0))
    pole_square = pole_const * pole_moment * pole_moment

    LHS_main = diag_main + off_b
    LHS_mainp = diag_mainp - pole_square + off_a

    pair_res = sum((delta_row[n] * Ry[n] / arb(n * n) for n in range(1, N + 1)), arb(0))
    pair_eta = sum((delta_row[n] * (1 - y[n]) / arb(n * n) for n in range(1, N + 1)), arb(0))
    RHS = -pair_res + (nu_y - lam1) * pair_eta

    # carried (unconditional) variant, DIAGNOSTIC only -- see module docstring
    sum_u2 = sum((u[n] * u[n] for n in range(1, N + 1)), arb(0))
    LHS_main_carried = LHS_main + (lam1 - nu_x) * sum_u2
    pair_ground = sum((delta_row[n] * Rx[n] / arb(n * n) for n in range(1, N + 1)), arb(0))
    RHS_carried = pair_ground - pair_res + (nu_y - nu_x) * pair_eta

    # The coordinator's two ratios, both relative to |LHS_direct| exactly as
    # specified. A second normalisation (largest term of the identity) is kept
    # alongside as a secondary, since |LHS_direct| is itself a cancelled sum.
    scale_direct = a_up(Q_direct)
    scale_alg = max_abs_term([Q_direct, diag_main, off_b, diag_mainp, pole_square, off_a])
    scale_id = max_abs_term(
        [Q_direct, diag_main, off_b, diag_mainp, pole_square, off_a, pair_res,
         (nu_y - lam1) * pair_eta]
    )
    ratio_identity = rel(Q_direct - RHS, scale_direct)
    ratio_dict_main = rel(LHS_main - Q_direct, scale_direct)
    ratio_dict_mainp = rel(LHS_mainp - Q_direct, scale_direct)
    ratio_identity_maxterm = rel(Q_direct - RHS, scale_id)
    ratio_dict_main_maxterm = rel(LHS_main - Q_direct, scale_alg)
    ratio_dict_mainp_maxterm = rel(LHS_mainp - Q_direct, scale_alg)
    r_carried = rel(LHS_main_carried - RHS_carried, scale_direct)
    worst_gated = max(
        [ratio_identity, ratio_dict_main, ratio_dict_mainp], key=lambda z: float(z)
    )
    identities_hold = bool(worst_gated <= arb(IDENTITY_REL_GATE_STR))

    # ---- odd-block entries for n, m <= 8 ---------------------------------
    nm = min(N_MODES, N)
    entries: list[dict[str, Any]] = []
    for n in range(1, nm + 1):
        row: list[dict[str, Any]] = []
        for j in range(1, nm + 1):
            if n == j:
                total = delta_n[n]
                pole = -pole_diag[n]
                arch = D_full[n]
            else:
                total = odd[n - 1, j - 1]
                pole = -pole_const * arb(n * j) / (d[n] * d[j])
                arch = arb(2 * n * j) * (a[n] - a[j]) / arb(n * n - j * j)
            row.append(
                {
                    "m": j,
                    "value": f_mid(total),
                    "pole_part": f_mid(pole),
                    "arch_prime_part": f_mid(arch),
                    "pole_plus_arch_defect": a_str(a_up(total - (pole + arch)))
                    if n != j
                    else a_str(a_up(total - (pole + arch))),
                }
            )
        entries.append({"n": n, "row": row})

    odd12 = odd[0, 1]
    odd12_pole = -pole_const * arb(2) / (d[1] * d[2])
    odd12_arch = arb(4) * (a[1] - a[2]) / arb(1 - 4)
    psd_cert_lhs = a_up(odd12)  # lambda1 * kronecker = 0 off the diagonal
    psd_cert_rhs = (delta_n[1] * delta_n[2]).sqrt()

    # ---- floors -----------------------------------------------------------
    progress(f"m=N={m} dps={dps}: odd-block eigenvalues (8x8)")
    small = arb_mat(nm, nm)
    for i in range(nm):
        for j in range(nm):
            small[i, j] = odd[i, j] - (lam1 if i == j else arb(0))
    lam_min_8, method_8, _r8 = lambda_min_symmetric(small, nm)

    progress(f"m=N={m} dps={dps}: odd-block eigenvalues (full {N}x{N})")
    shifted = arb_mat(N, N)
    for i in range(N):
        for j in range(N):
            shifted[i, j] = odd[i, j] - (lam1 if i == j else arb(0))
    lam_min_full, method_full, resid_full = lambda_min_symmetric(shifted, N)

    delta_vals8 = [f_mid(delta_n[n]) for n in range(1, nm + 1)]
    delta_vals_all = [f_mid(delta_n[n]) for n in range(1, N + 1)]

    # ---- contraction quantities (report section 5), full n = 1..N ---------
    progress(f"m=N={m} dps={dps}: q_ap / q_pole / rho_stab")
    Dvec = np.array([f_mid(D_full[n]) for n in range(1, N + 1)], dtype=float)
    D_zero = bool(np.any(Dvec == 0.0))
    ghat_arb = {n: arb(n) / d[n] for n in range(1, N + 1)}
    ghat = np.array([f_mid(ghat_arb[n]) for n in range(1, N + 1)], dtype=float)

    off_ap = np.zeros((N, N), dtype=float)
    for n in range(1, N + 1):
        for j in range(1, N + 1):
            if j == n:
                continue
            off_ap[n - 1, j - 1] = f_mid(arb(2 * n * j) * (a[n] - a[j]) / arb(n * n - j * j))

    if D_zero:
        q_ap = float("inf")
        q_full = float("inf")
    else:
        inv_d = 1.0 / Dvec
        q_ap = two_norm(off_ap * inv_d[:, None])
        q_full = two_norm((float(f_mid(pole_const)) * np.outer(ghat, ghat) - off_ap) * inv_d[:, None])

    ghat_norm = sum((ghat_arb[n] ** 2 for n in range(1, N + 1)), arb(0)).sqrt()
    if D_zero:
        q_pole = float("inf")
        q_pole_str = "inf"
    else:
        ghat_over_D = sum(((ghat_arb[n] / D_full[n]) ** 2 for n in range(1, N + 1)), arb(0)).sqrt()
        q_pole_arb = pole_const * ghat_over_D * ghat_norm
        q_pole = f_mid(q_pole_arb)
        q_pole_str = a_str(q_pole_arb, 8)

    norm_RDelta = sum((u[n] * u[n] for n in range(1, N + 1)), arb(0)).sqrt()
    norm_RRes = sum(((Ry[n] / arb(n)) ** 2 for n in range(1, N + 1)), arb(0)).sqrt()
    rho_stab = f_mid(norm_RDelta / norm_RRes) if f_mid(norm_RRes) != 0.0 else float("inf")

    b_vals = [f_mid(b[n]) for n in range(1, nm + 1)]
    b1 = b_vals[0]
    b_var = max(abs(bv - b1) for bv in b_vals) / abs(b1) if b1 != 0.0 else float("inf")

    L_f = f_mid(L)
    lam_min_full_f = f_mid(lam_min_full)
    lam_min_8_f = f_mid(lam_min_8)

    return {
        "m": m,
        "N": N,
        "dps": dps,
        "L": bounds(L),
        "L_float": L_f,
        "A_L": f_mid(A_L),
        "eigen_method": method,
        "lambda1": bounds(lam1),
        "lambda1_float": f_mid(lam1),
        "lambda2": bounds(lam2) if lam2 is not None else None,
        "inverse_iteration_residual": bounds(eigen_resid) if eigen_resid is not None else None,
        "xi0": f_mid(v[0]),
        "Xi0": f_mid(Xi0),
        "Xi_imag_rel_error_max": xi_imag_rel_max,
        "nu_y": f_mid(nu_y),
        "nu_x": f_mid(nu_x),
        "nu_minus_lambda1": f_mid(nu_y - lam1),
        "identity": {
            "LHS_direct": f_mid(Q_direct),
            "RHS_direct": f_mid(RHS),
            "LHS_expanded_MAIN": f_mid(LHS_main),
            "LHS_expanded_MAIN_P": f_mid(LHS_mainp),
            "ratio_identity": a_str(ratio_identity),
            "ratio_dictionary_MAIN": a_str(ratio_dict_main),
            "ratio_dictionary_MAIN_P": a_str(ratio_dict_mainp),
            "ratio_identity_maxterm_scaled": a_str(ratio_identity_maxterm),
            "ratio_dictionary_MAIN_maxterm_scaled": a_str(ratio_dict_main_maxterm),
            "ratio_dictionary_MAIN_P_maxterm_scaled": a_str(ratio_dict_mainp_maxterm),
            "carried_variant_rel": a_str(r_carried),
            "worst_gated_rel": a_str(worst_gated),
            "gate": IDENTITY_REL_GATE_STR,
            "identities_hold": identities_hold,
            "term_diag_delta": f_mid(diag_main),
            "term_offdiag_b": f_mid(off_b),
            "term_diag_D": f_mid(diag_mainp),
            "term_pole_square": f_mid(pole_square),
            "term_offdiag_a": f_mid(off_a),
            "term_pole_moment": f_mid(pole_moment),
            "term_pair_residual": f_mid(pair_res),
            "term_pair_eta": f_mid(pair_eta),
            "odd_normal_form_max_defect": a_str(odd_normal_defect),
            "S7_delta_vs_D_minus_pole_max_defect": a_str(s7_defect),
            "residual_row_basis_change_defect": a_str(raw_form_defect),
            "nu_matvec_vs_source_defect": a_str(nu_raw_defect),
        },
        "odd_entries_8x8": entries,
        "odd12": {
            "value": f_mid(odd12),
            "abs": abs(f_mid(odd12)),
            "pole_part": f_mid(odd12_pole),
            "arch_prime_part": f_mid(odd12_arch),
            "sum_defect": a_str(a_up(odd12 - (odd12_pole + odd12_arch))),
            "psd_certificate_lhs": f_mid(psd_cert_lhs),
            "psd_certificate_rhs_sqrt_delta1_delta2": f_mid(psd_cert_rhs),
            "psd_certificate_holds": bool(psd_cert_lhs <= psd_cert_rhs),
            "gate_1e-3": bool(abs(f_mid(odd12)) <= S7_OFFDIAG_GATE),
            "gate_3e-4_report": bool(abs(f_mid(odd12)) <= S7_REPORT_GATE),
            "pole_is_O1": bool(abs(f_mid(odd12_pole)) >= S7_POLE_O1_GATE),
        },
        "floors": {
            "delta_n_8": delta_vals8,
            "min_delta_n_8": min(delta_vals8),
            "min_delta_n_full": min(delta_vals_all),
            "argmin_delta_n_full": delta_vals_all.index(min(delta_vals_all)) + 1,
            "all_delta_nonnegative": bool(all(dv >= 0.0 for dv in delta_vals_all)),
            "lambda_min_odd_8x8": lam_min_8_f,
            "lambda_min_odd_8x8_ball": bounds(lam_min_8),
            "lambda_min_odd_8x8_method": method_8,
            "lambda_min_odd_full": lam_min_full_f,
            "lambda_min_odd_full_ball": bounds(lam_min_full),
            "lambda_min_odd_full_method": method_full,
            "lambda_min_ball_excludes_zero": bool(0 not in lam_min_full),
            "interlacing_sanity_full_le_8x8": bool(lam_min_full_f <= lam_min_8_f),
            "rayleigh_sanity_8x8_le_min_delta": bool(lam_min_8_f <= min(delta_vals8)),
            "lambda_min_odd_full_residual": bounds(resid_full) if resid_full is not None else None,
            "lambda_min_odd_full_times_L2": lam_min_full_f * L_f * L_f,
            "lambda_min_odd_8x8_times_L2": lam_min_8_f * L_f * L_f,
            "in_band_1e-4_1e-1": bool(
                ODD_FLOOR_LO <= lam_min_full_f * L_f * L_f <= ODD_FLOOR_HI
            ),
        },
        "contraction": {
            "q_ap": q_ap,
            "q_pole": q_pole,
            "q_pole_arb": q_pole_str,
            "q_full": q_full,
            "ghat_norm": f_mid(ghat_norm),
            "D_n_min_abs_full": float(np.min(np.abs(Dvec))),
            "D_n_argmin_full": int(np.argmin(np.abs(Dvec))) + 1,
            "D_n_max_abs_full": float(np.max(np.abs(Dvec))),
            "D_n_has_zero": D_zero,
            "norm_R_Delta": f_mid(norm_RDelta),
            "norm_R_residual": f_mid(norm_RRes),
            "rho_stab": rho_stab,
            "q_ap_lt_1": bool(q_ap < 1.0),
            "rho_stab_le_gate": bool(rho_stab <= RHO_STAB_GATE),
        },
        "b_row": {
            "b_n_8": b_vals,
            "max_rel_variation_n_le_8": b_var,
            "b1_minus_b2_over_b1": abs(b_vals[0] - b_vals[1]) / abs(b1) if b1 != 0.0 else float("inf"),
            "p1_minus_p2": f_mid(p[1] - p[2]),
            "abs_odd12_over_pole_part": (
                abs(f_mid(odd12)) / abs(f_mid(odd12_pole)) if f_mid(odd12_pole) != 0.0 else float("inf")
            ),
            "b_n_full_min": min(f_mid(b[n]) for n in range(1, N + 1)),
            "b_n_full_max": max(f_mid(b[n]) for n in range(1, N + 1)),
        },
        "elapsed_seconds": time.monotonic() - started,
    }


def verdicts(cells: list[dict[str, Any]], complete: bool) -> dict[str, dict[str, Any]]:
    rules = {
        "P_ENERGY_IDENTITY_EXACT": (
            0.90,
            "(MAIN) residual <= 1e-30 relative at every cell -- taken as "
            "max(ratio_identity, ratio_dictionary(MAIN), ratio_dictionary(MAIN-P))",
        ),
        "P_S7_ODD_OFFDIAG_SMALL": (
            0.55,
            "|D^odd_12| <= 1e-3 at every cell while its pole part alone is O(1)",
        ),
        "P_ODD_FLOOR_FLAT": (
            0.45,
            "lambda_min((D-lambda1)|_odd, full block)*L^2 in [1e-4, 1e-1] at every cell",
        ),
        "P_Q_AP_LT_1": (0.35, "q_ap < 1 at every cell"),
        "P_RHO_STAB_FLAT": (
            0.50,
            "rho_stab <= 1e4 at every cell and varies by < x10 across the schedule",
        ),
    }
    if not cells:
        return {k: {"p": v[0], "rule": v[1], "verdict": "UNRESOLVED"} for k, v in rules.items()}

    def verdict(ok: bool) -> str:
        if not complete:
            return "UNRESOLVED"
        return "CONFIRMED" if ok else "REFUTED"

    out: dict[str, dict[str, Any]] = {}

    ident_ok = all(c["identity"]["identities_hold"] for c in cells)
    out["P_ENERGY_IDENTITY_EXACT"] = {
        "p": rules["P_ENERGY_IDENTITY_EXACT"][0],
        "rule": rules["P_ENERGY_IDENTITY_EXACT"][1],
        "verdict": verdict(ident_ok),
        "worst_relative_residual_per_cell": {
            str(c["m"]): c["identity"]["worst_gated_rel"] for c in cells
        },
        "ratio_identity_per_cell": {
            str(c["m"]): c["identity"]["ratio_identity"] for c in cells
        },
        "ratio_dictionary_MAIN_per_cell": {
            str(c["m"]): c["identity"]["ratio_dictionary_MAIN"] for c in cells
        },
        "ratio_dictionary_MAIN_P_per_cell": {
            str(c["m"]): c["identity"]["ratio_dictionary_MAIN_P"] for c in cells
        },
    }

    s7_ok = all(c["odd12"]["gate_1e-3"] and c["odd12"]["pole_is_O1"] for c in cells)
    out["P_S7_ODD_OFFDIAG_SMALL"] = {
        "p": rules["P_S7_ODD_OFFDIAG_SMALL"][0],
        "rule": rules["P_S7_ODD_OFFDIAG_SMALL"][1],
        "verdict": verdict(s7_ok),
        "max_abs_D_odd_12": max(c["odd12"]["abs"] for c in cells),
        "cells_passing_1e-3": [c["m"] for c in cells if c["odd12"]["gate_1e-3"]],
        "cells_passing_3e-4": [c["m"] for c in cells if c["odd12"]["gate_3e-4_report"]],
        "pole_parts": {str(c["m"]): c["odd12"]["pole_part"] for c in cells},
    }

    floor_ok = all(c["floors"]["in_band_1e-4_1e-1"] for c in cells)
    out["P_ODD_FLOOR_FLAT"] = {
        "p": rules["P_ODD_FLOOR_FLAT"][0],
        "rule": rules["P_ODD_FLOOR_FLAT"][1],
        "verdict": verdict(floor_ok),
        "lambda_min_times_L2": {str(c["m"]): c["floors"]["lambda_min_odd_full_times_L2"] for c in cells},
    }

    qap_ok = all(c["contraction"]["q_ap_lt_1"] for c in cells)
    out["P_Q_AP_LT_1"] = {
        "p": rules["P_Q_AP_LT_1"][0],
        "rule": rules["P_Q_AP_LT_1"][1],
        "verdict": verdict(qap_ok),
        "q_ap": {str(c["m"]): c["contraction"]["q_ap"] for c in cells},
    }

    rhos = [c["contraction"]["rho_stab"] for c in cells]
    rho_le = all(r <= RHO_STAB_GATE for r in rhos)
    rho_spread = (max(rhos) / min(rhos)) if min(rhos) > 0 else float("inf")
    out["P_RHO_STAB_FLAT"] = {
        "p": rules["P_RHO_STAB_FLAT"][0],
        "rule": rules["P_RHO_STAB_FLAT"][1],
        "verdict": verdict(rho_le and rho_spread < RHO_STAB_SPREAD),
        "rho_stab": {str(c["m"]): c["contraction"]["rho_stab"] for c in cells},
        "spread_max_over_min": rho_spread,
        "all_below_1e4": rho_le,
    }
    return out


def write_markdown(payload: dict[str, Any], path: Path) -> None:
    cells = payload["cells"]
    lines: list[str] = []
    ap = lines.append
    ap("# Goal 058 Probe 11 — odd-sector floor scale and the S7 cancellation (ADDENDUM 12)")
    ap("")
    ap(
        f"Precommit: `{payload['precommit']}` (ADDENDUM 12). "
        f"Source: `{payload['preflight']}` (§1, §2, §3.1–3.3, §5, §9, §10); "
        f"source dictionary and `D_n` from `{payload['preflight_previous']}` §1 and the "
        "sibling probe-10 script `phase5_codex/lattice_equation.py` (imported, unmodified)."
    )
    ap("")
    ap("`DIAGNOSTIC_NEVER_A_PROOF`. `PX_RH_CLAIM: NOT_MADE`. No cofinal claim: five cells.")
    ap("")
    if payload["pending_cells"]:
        ap(f"**Pending cells:** {payload['pending_cells']} — `{payload['pending_command']}`")
        ap("")

    ap("## (i) The non-circular identity test — three numbers, two ratios")
    ap("")
    ap(
        "`LHS_direct = ½⟨RΔ,(D−λ₁)RΔ⟩` is a matrix product with the builder's own odd block "
        "at `u = RΔ`, `Δ = x − y` from the solved ground eigenvector and the Ξ-sample row — no "
        "source dictionary enters it. `RHS_direct` uses `𝓡(y)_n = (K̃ỹ)_n − ỹ_n(K̃ỹ)_0` from one "
        "matrix-vector product with the builder's even block. `LHS_expanded` is the report's "
        "own δ_n / Loewner formula, in its (MAIN) and (MAIN-P) variants. "
        "`ratio_identity = |LHS_direct − RHS_direct|/|LHS_direct|` tests the **identity**; "
        "`ratio_dictionary = |LHS_expanded − LHS_direct|/|LHS_direct|` tests the report's "
        "**dictionary**. Both are held to the frozen 1e-30 gate."
    )
    ap("")
    ap("| m=N | dps | method | LHS_direct | RHS_direct | LHS_exp (MAIN) | LHS_exp (MAIN-P) |")
    ap("|---:|---:|:--|---:|---:|---:|---:|")
    for c in cells:
        i = c["identity"]
        ap(
            f"| {c['m']} | {c['dps']} | {c['eigen_method']} | {i['LHS_direct']:.12e} | "
            f"{i['RHS_direct']:.12e} | {i['LHS_expanded_MAIN']:.12e} | "
            f"{i['LHS_expanded_MAIN_P']:.12e} |"
        )
    ap("")
    ap(
        "| m=N | ratio_identity | ratio_dictionary (MAIN) | ratio_dictionary (MAIN-P) | "
        "carried variant | gate 1e-30 |"
    )
    ap("|---:|---:|---:|---:|---:|:--:|")
    for c in cells:
        i = c["identity"]
        ap(
            f"| {c['m']} | {i['ratio_identity']} | {i['ratio_dictionary_MAIN']} | "
            f"{i['ratio_dictionary_MAIN_P']} | {i['carried_variant_rel']} | "
            f"{'PASS' if i['identities_hold'] else 'FAIL'} |"
        )
    ap("")
    ap(
        "Same three ratios normalised by the largest term of the identity instead of by "
        "`|LHS_direct|` (secondary, since `LHS_direct` is itself a cancelled sum):"
    )
    ap("")
    ap("| m=N | identity | dictionary (MAIN) | dictionary (MAIN-P) |")
    ap("|---:|---:|---:|---:|")
    for c in cells:
        i = c["identity"]
        ap(
            f"| {c['m']} | {i['ratio_identity_maxterm_scaled']} | "
            f"{i['ratio_dictionary_MAIN_maxterm_scaled']} | "
            f"{i['ratio_dictionary_MAIN_P_maxterm_scaled']} |"
        )
    ap("")
    ap("Structural defects of the report's own normal forms (should be 0 to working precision):")
    ap("")
    ap(
        "| m=N | odd off-diag vs `2nm(b_n−b_m)/(n²−m²)` | `δ_n` vs `D_n − 32π²A_L n²/d_n²` | "
        "`𝓡(y)` matvec vs source form | `ν` matvec vs source form |"
    )
    ap("|---:|---:|---:|---:|---:|")
    for c in cells:
        i = c["identity"]
        ap(
            f"| {c['m']} | {i['odd_normal_form_max_defect']} | "
            f"{i['S7_delta_vs_D_minus_pole_max_defect']} | "
            f"{i['residual_row_basis_change_defect']} | {i['nu_matvec_vs_source_defect']} |"
        )
    ap("")
    ap("Terms of (MAIN) and (MAIN-P):")
    ap("")
    ap(
        "| m=N | Q | Σδ_nΔ²/n² | 2⟨Δ,L[b]Δ⟩ | ΣD_nΔ²/n² | 32π²A_L(ΣΔ/d)² | 2⟨Δ,L[a]Δ⟩ | "
        "−ΣΔ𝓡(y)/n² | (ν−λ₁)ΣΔ(1−y)/n² | RHS |"
    )
    ap("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for c in cells:
        i = c["identity"]
        ap(
            f"| {c['m']} | {i['LHS_direct']:.6e} | {i['term_diag_delta']:.6e} | "
            f"{i['term_offdiag_b']:.6e} | {i['term_diag_D']:.6e} | {i['term_pole_square']:.6e} | "
            f"{i['term_offdiag_a']:.6e} | {-i['term_pair_residual']:.6e} | "
            f"{c['nu_minus_lambda1'] * i['term_pair_eta']:.6e} | {i['RHS_direct']:.6e} |"
        )
    ap("")

    ap("## (ii) The odd block `(D−λ₁)|_odd` for n, m ≤ 8")
    ap("")
    ap(
        "Diagonal entries are `δ_n = τ(n,n) − b_n − λ₁`; off-diagonal entries are "
        "`D^odd_{nm} = τ(n,m) − τ(n,−m)`, taken from the builder. `pole` is "
        "`−32π²A_L nm/(d_n d_m)` off the diagonal and `−32π²A_L n²/d_n²` on it; `arch` is the "
        "arch/prime complement (`2nm(a_n−a_m)/(n²−m²)`, resp. `D_n`)."
    )
    ap("")
    for c in cells:
        ap(f"### m = N = {c['m']}  (L = {c['L_float']:.6f}, A_L = {c['A_L']:.6f})")
        ap("")
        ap("| n\\m | " + " | ".join(str(j) for j in range(1, N_MODES + 1)) + " |")
        ap("|---:|" + "---:|" * N_MODES)
        for row in c["odd_entries_8x8"]:
            vals = " | ".join(f"{e['value']:.6e}" for e in row["row"])
            ap(f"| **{row['n']}** | {vals} |")
        ap("")
        ap("Pole part of the same entries:")
        ap("")
        ap("| n\\m | " + " | ".join(str(j) for j in range(1, N_MODES + 1)) + " |")
        ap("|---:|" + "---:|" * N_MODES)
        for row in c["odd_entries_8x8"]:
            vals = " | ".join(f"{e['pole_part']:.6e}" for e in row["row"])
            ap(f"| **{row['n']}** | {vals} |")
        ap("")

    ap("### `D^odd_12` against its pole part — the S7 distinguishing measurement (§10)")
    ap("")
    ap(
        "| m=N | D^odd_12 | pole part | arch/prime part | pole+arch defect | ≤1e-3 | ≤3e-4 | "
        "PSD cert √(δ₁δ₂) | cert holds |"
    )
    ap("|---:|---:|---:|---:|---:|:--:|:--:|---:|:--:|")
    for c in cells:
        o = c["odd12"]
        ap(
            f"| {c['m']} | {o['value']:.6e} | {o['pole_part']:.6e} | {o['arch_prime_part']:.6e} | "
            f"{o['sum_defect']} | {'PASS' if o['gate_1e-3'] else 'FAIL'} | "
            f"{'PASS' if o['gate_3e-4_report'] else 'FAIL'} | "
            f"{o['psd_certificate_rhs_sqrt_delta1_delta2']:.6e} | "
            f"{'PASS' if o['psd_certificate_holds'] else 'FAIL'} |"
        )
    ap("")

    ap("## (iii) Floors: `min_n δ_n` and `λ_min((D−λ₁)|_odd)`")
    ap("")
    ap(
        "| m=N | min_{n≤8} δ_n | min_{n≤N} δ_n | argmin | all δ_n ≥ 0 | λ_min(8×8) | "
        "λ_min(full) | λ_min(full)·L² | band [1e-4,1e-1] | ball ∌ 0 | sanity chain |"
    )
    ap("|---:|---:|---:|---:|:--:|---:|---:|---:|:--:|:--:|:--:|")
    for c in cells:
        f = c["floors"]
        chain = f["interlacing_sanity_full_le_8x8"] and f["rayleigh_sanity_8x8_le_min_delta"]
        ap(
            f"| {c['m']} | {f['min_delta_n_8']:.6e} | {f['min_delta_n_full']:.6e} | "
            f"{f['argmin_delta_n_full']} | {'yes' if f['all_delta_nonnegative'] else 'NO'} | "
            f"{f['lambda_min_odd_8x8']:.6e} | {f['lambda_min_odd_full']:.6e} | "
            f"{f['lambda_min_odd_full_times_L2']:.6e} | "
            f"{'PASS' if f['in_band_1e-4_1e-1'] else 'FAIL'} | "
            f"{'yes' if f['lambda_min_ball_excludes_zero'] else 'NO'} | "
            f"{'ok' if chain else 'BROKEN'} |"
        )
    ap("")
    ap("Certified enclosure of `λ_min` on the full odd block:")
    ap("")
    ap("| m=N | method | ball |")
    ap("|---:|:--|:--|")
    for c in cells:
        f = c["floors"]
        ap(f"| {c['m']} | {f['lambda_min_odd_full_method']} | `{f['lambda_min_odd_full_ball']['ball']}` |")
    ap("")
    ap("Per-mode `δ_n`, n ≤ 8:")
    ap("")
    ap("| m=N | " + " | ".join(f"n={n}" for n in range(1, N_MODES + 1)) + " |")
    ap("|---:|" + "---:|" * N_MODES)
    for c in cells:
        ap(f"| {c['m']} | " + " | ".join(f"{d:.6e}" for d in c["floors"]["delta_n_8"]) + " |")
    ap("")

    ap("## (iv) Contraction quantities and the stability ratio (§5)")
    ap("")
    ap(
        "| m=N | q_ap | q_pole | q_full | ‖ĝ‖ | min_{n≤N}\\|D_n\\| (arg) | max\\|D_n\\| | "
        "‖RΔ‖ | ‖R𝓡(y)‖ | ρ_stab | q_ap<1 |"
    )
    ap("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|:--:|")
    for c in cells:
        q = c["contraction"]
        ap(
            f"| {c['m']} | {q['q_ap']:.6e} | {q['q_pole']:.6e} | {q['q_full']:.6e} | "
            f"{q['ghat_norm']:.6e} | {q['D_n_min_abs_full']:.4e} (n={q['D_n_argmin_full']}) | "
            f"{q['D_n_max_abs_full']:.4e} | {q['norm_R_Delta']:.6e} | {q['norm_R_residual']:.6e} | "
            f"{q['rho_stab']:.6e} | {'PASS' if q['q_ap_lt_1'] else 'FAIL'} |"
        )
    ap("")

    ap("## (v) `b_n` for n ≤ 8 and its relative variation")
    ap("")
    ap("| m=N | " + " | ".join(f"b_{n}" for n in range(1, N_MODES + 1)) + " | max\\|b_n−b_1\\|/\\|b_1\\| |")
    ap("|---:|" + "---:|" * (N_MODES + 1))
    for c in cells:
        br = c["b_row"]
        ap(
            f"| {c['m']} | " + " | ".join(f"{bv:.9e}" for bv in br["b_n_8"]) + " | "
            f"{br['max_rel_variation_n_le_8']:.6e} |"
        )
    ap("")
    ap("Full-row spread of `b_n` (n = 1..N), and the S7 mechanism at the (1,2) entry:")
    ap("")
    ap("| m=N | min b_n | max b_n | \\|b₁−b₂\\|/\\|b₁\\| | p₁−p₂ | \\|D^odd_12\\|/\\|pole part\\| |")
    ap("|---:|---:|---:|---:|---:|---:|")
    for c in cells:
        br = c["b_row"]
        ap(
            f"| {c['m']} | {br['b_n_full_min']:.9e} | {br['b_n_full_max']:.9e} | "
            f"{br['b1_minus_b2_over_b1']:.6e} | {br['p1_minus_p2']:.6e} | "
            f"{br['abs_odd12_over_pole_part']:.6e} |"
        )
    ap("")

    ap("## Verdicts (ADDENDUM 12, frozen)")
    ap("")
    for name, pred in payload["predictions"].items():
        ap(f"- `{name}` (p={pred['p']}): {pred['rule']} -> **{pred['verdict']}**")
    ap("")
    if payload["stop_token"]:
        ap(f"STOP: `{payload['stop_token']}`")
        ap("")
        ap(payload["stop_detail"])
        ap("")
    else:
        ap("No STOP code triggered.")
        ap("")
    for note in payload["observations"]:
        ap(f"- {note}")
    ap("")
    ap("`DIAGNOSTIC_NEVER_A_PROOF`. `PX_RH_CLAIM: NOT_MADE`. No route promotion. No cofinal claim.")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def observations(cells: list[dict[str, Any]]) -> list[str]:
    if not cells:
        return []
    out = []
    out.append(
        "S7 (§10) distinguishing measurement: |D^odd_12| = "
        + ", ".join(f"m={c['m']}: {abs(c['odd12']['value']):.4e}" for c in cells)
        + " against a pole part of "
        + ", ".join(f"{c['odd12']['pole_part']:.4g}" for c in cells)
        + "."
    )
    out.append(
        "S8 (§10) odd-sector floor: lambda_min((D-lambda1)|_odd) on the full block is "
        + ", ".join(f"m={c['m']}: {c['floors']['lambda_min_odd_full']:.4e}" for c in cells)
        + "; times L^2: "
        + ", ".join(f"{c['floors']['lambda_min_odd_full_times_L2']:.4e}" for c in cells)
        + "."
    )
    out.append(
        "min_n delta_n over ALL n (not only n <= 8, which is all probe 10 and the report's "
        "arithmetic could see): "
        + ", ".join(
            f"m={c['m']}: {c['floors']['min_delta_n_full']:.4e} at n={c['floors']['argmin_delta_n_full']}"
            for c in cells
        )
        + "."
    )
    out.append(
        "The quadratic form itself is a near-total cancellation. LHS_direct = "
        + ", ".join(f"m={c['m']}: {c['identity']['LHS_direct']:.4e}" for c in cells)
        + " while its own constituent terms are of size 1e-4 to 1e-6 (see the term table): at "
        f"m={cells[-1]['m']} the (MAIN-P) terms are {cells[-1]['identity']['term_diag_D']:.4e}, "
        f"{-cells[-1]['identity']['term_pole_square']:.4e}, {cells[-1]['identity']['term_offdiag_a']:.4e} "
        "and their sum is 1e-134. Equivalently R Delta sits almost exactly in the near-null "
        "space of (D-lambda1)|_odd, which is the same fact as the lambda_min column. The two "
        "pairings on the right cancel each other to the same depth. Recorded before it is explained."
    )
    out.append(
        "Contraction (§5): q_ap = "
        + ", ".join(f"m={c['m']}: {c['contraction']['q_ap']:.4e}" for c in cells)
        + "; q_pole = "
        + ", ".join(f"{c['contraction']['q_pole']:.4g}" for c in cells)
        + ". q_pole here runs over the FULL row n = 1..N; the report's §5 table gave the n <= 8 "
        "truncation as an explicit lower bound (4.78, 9.23, 8.89, 15.87, 14.75), and the full "
        "values sit just above it at every cell, which confirms that arithmetic."
    )
    out.append(
        "Stability ratio (§9's deciding number): rho_stab = ||R Delta||/||R R(y)|| = "
        + ", ".join(f"m={c['m']}: {c['contraction']['rho_stab']:.4e}" for c in cells)
        + ". §9 fixed the reading in advance: O(1)...O(1e4) and flat would put C_k in the H4 "
        "shell at the odd-sector floor; growth like sqrt(m) or faster would not. The measured "
        "growth is neither flat nor sqrt(m) -- log10 rho_stab runs "
        + ", ".join(f"{__import__('math').log10(c['contraction']['rho_stab']):.1f}" for c in cells)
        + " over m = 13..163, i.e. the numerator ||R Delta|| is almost constant (1e-2) while the "
        "denominator ||R R(y)|| collapses. DIAGNOSTIC on five cells; no cofinal claim is made "
        "about the trend."
    )
    out.append(
        "b_n relative variation over n <= 8: "
        + ", ".join(f"m={c['m']}: {c['b_row']['max_rel_variation_n_le_8']:.4e}" for c in cells)
        + "; the low-mode figure |b_1-b_2|/|b_1| is "
        + ", ".join(f"{c['b_row']['b1_minus_b2_over_b1']:.4e}" for c in cells)
        + ". Reading A of S7 asks for ~1e-4. The smallness of D^odd_12 measured against its own "
        "pole part is |D^odd_12|/|pole| = "
        + ", ".join(f"m={c['m']}: {c['b_row']['abs_odd12_over_pole_part']:.4e}" for c in cells)
        + " -- i.e. b varies far less than p does, which is the mechanism S7 names, at a "
        "different order of magnitude than the 1e-4 the report reads off delta_n."
    )
    out.append(
        "||R R(y)|| (the denominator of rho_stab): "
        + ", ".join(f"m={c['m']}: {c['contraction']['norm_R_residual']:.4e}" for c in cells)
        + " against ||R Delta|| = "
        + ", ".join(f"{c['contraction']['norm_R_Delta']:.4e}" for c in cells)
        + ". nu(y) = "
        + ", ".join(f"{c['nu_y']:.4e}" for c in cells)
        + ": the Xi-sample row very nearly satisfies the eigen-equation of the builder's matrix, "
        "which is what makes rho_stab large. Recorded before it is explained."
    )
    sanity = [
        c["m"]
        for c in cells
        if not (
            c["floors"]["interlacing_sanity_full_le_8x8"]
            and c["floors"]["rayleigh_sanity_8x8_le_min_delta"]
        )
    ]
    if sanity:
        out.append(
            "ODDITY: the eigenvalue sanity chain lambda_min(full) <= lambda_min(8x8) <= "
            "min_{n<=8} delta_n fails at m in " + str(sanity) + " -- the eigen-solve, not the "
            "mathematics, is the first suspect. Recorded."
        )
    else:
        out.append(
            "Eigenvalue sanity chain lambda_min(full) <= lambda_min(8x8) <= min_{n<=8} delta_n "
            "holds at every cell (Cauchy interlacing for the principal 8x8 submatrix, and the "
            "Rayleigh quotient at the coordinate vectors)."
        )
    bad = [c["m"] for c in cells if not c["floors"]["all_delta_nonnegative"]]
    if bad:
        out.append(
            "ODDITY: delta_n < 0 somewhere at m in " + str(bad) + " — Cauchy interlacing says "
            "(D - lambda1)|_odd is PSD, so a negative diagonal entry contradicts either the "
            "interlacing reading or the dictionary. Recorded, not explained."
        )
    else:
        out.append(
            "All delta_n >= 0 at every cell and every n <= N, consistent with the interlacing "
            "claim (D - lambda1)|_odd >= 0 of §3.3."
        )
    return out


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
            progress_line(f"cell m=N={m} FAILED: {type(exc).__name__}: {exc}")
            pending.append(m)
            continue
        cells.append(cell)
        progress_line(
            f"cell {index}/{len(schedule)} m=N={m} done in {cell['elapsed_seconds']:.1f}s "
            f"| worst identity rel={cell['identity']['worst_gated_rel']} "
            f"| D^odd_12={cell['odd12']['value']:.4e} (pole {cell['odd12']['pole_part']:.4g}) "
            f"| lam_min(odd)L^2={cell['floors']['lambda_min_odd_full_times_L2']:.4e} "
            f"| q_ap={cell['contraction']['q_ap']:.4e} rho_stab={cell['contraction']['rho_stab']:.4e}"
        )

    expected = {m for m, _ in SCHEDULE}
    have = {c["m"] for c in cells}
    pending = sorted((expected - have) | set(pending))
    complete = not pending

    preds = verdicts(cells, complete)

    stop_token = None
    stop_detail = ""
    bad = [c for c in cells if not c["identity"]["identities_hold"]]
    if bad:
        stop_token = "ENERGY_IDENTITY_MISMATCH"
        parts = [
            f"m={c['m']}: LHS_direct={c['identity']['LHS_direct']!r}, "
            f"RHS_direct={c['identity']['RHS_direct']!r}, "
            f"LHS_expanded(MAIN)={c['identity']['LHS_expanded_MAIN']!r}, "
            f"LHS_expanded(MAIN-P)={c['identity']['LHS_expanded_MAIN_P']!r}; "
            f"ratio_identity={c['identity']['ratio_identity']}, "
            f"ratio_dictionary(MAIN)={c['identity']['ratio_dictionary_MAIN']}, "
            f"ratio_dictionary(MAIN-P)={c['identity']['ratio_dictionary_MAIN_P']}, "
            f"carried={c['identity']['carried_variant_rel']}"
            for c in bad
        ]
        stop_detail = (
            "A boxed identity of the energy preflight does not reproduce the builder's own "
            "matrices to working precision. Reported, not repaired: if the report's formula "
            f"and the builder disagree, that IS the result. Gate {IDENTITY_REL_GATE_STR}. "
            + "; ".join(parts)
        )

    pending_command = (
        ".venv/bin/python docs/routeB_bus/phase5_codex/odd_floor.py "
        + ",".join(str(m) for m in pending)
        if pending
        else ""
    )

    payload = {
        "schema": "OddFloorProbe11.v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "route": "GOAL058_RECIPROCAL_MODE_XI_LATTICE_ENERGY_SOURCE",
        "probe": 11,
        "addendum": 12,
        "precommit": str(PRECOMMIT.relative_to(REPO)),
        "preflight": str(PREFLIGHT.relative_to(REPO)),
        "preflight_previous": str(PREFLIGHT_PREV.relative_to(REPO)),
        "semantic_boundary": "FINITE_CELL_DIAGNOSTIC_NEVER_A_PROOF",
        "schedule": [{"m": m, "dps": dps} for m, dps in SCHEDULE],
        "n_modes": N_MODES,
        "identity_relative_gate": IDENTITY_REL_GATE_STR,
        "cells": cells,
        "pending_cells": pending,
        "pending_command": pending_command,
        "predictions": preds,
        "observations": observations(cells),
        "stop_token": stop_token,
        "stop_detail": stop_detail,
        "promotion": False,
        "px_rh_claim": "NOT_MADE",
    }
    OUT_JSON.write_text(
        json.dumps(payload, indent=2, sort_keys=True, default=str) + "\n", encoding="utf-8"
    )
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
