#!/usr/bin/env python3
"""Edge ledger Probe 3 (ratio kill-test of wall B) and Probe 2 verdict.

Reads `docs/routeB_bus/phase5_scripts/out/edge_ledger.json` (per-record eigenpair
data produced by `edge_ledger_build.py`) and computes:

  Probe 3 -- q_m(t) := L^{-1/2} sum_{|n|<=N} (-1)^n xi_n e^{2*pi*i*n*t/L},
  t in [-L/2, L/2]; M_m(sigma) := int |q_m(t)| e^{sigma*|t|} dt for
  sigma in {0.10 .. 0.45}; R_m(sigma) := M_m(sigma) / (sqrt(L)*|xi_0|); the
  GROWS / BOUNDED / GEOMETRY_FIRST / UNRESOLVED verdict.

  Probe 2 -- c_m := -(dlambda1/dL)_HF / edge_sq, sign of dGap/dL, the
  CONFIRMED / REFUTED / UNRESOLVED verdict.

Rules are frozen in
`docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md` and
are NOT re-derived here; this script only implements the arithmetic on top of
the ledger's numbers.

DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE.

--------------------------------------------------------------------------
Numerical method for Probe 3 (why it is done this way)
--------------------------------------------------------------------------
Write theta(x) = (2*pi/L)*x and, for real coefficients xi_n, the real part of
the sum on the real axis is exactly

    R(t) = xi_0 + sum_{n=1}^{N} (xi_n + xi_{-n}) * (-1)^n * cos(n*theta(t))

(this holds termwise from Re(e^{i*a}) = cos(a) and cos(-a) = cos(a); it does
NOT assume xi_{-n} = xi_n -- any numerical asymmetry in the ledger's
eigenvector is carried through exactly, not discarded). R(x) extends this
formula to complex x via the entire function cos(z); it is therefore an
entire analytic function of x that restricts to the true real part of q_m(t)
on the real line for every t, symmetric or not. |q_m(t)| for real t then
equals R(t) with the sign flipped where R is negative, so on any interval
where R does not change sign, sign(R)*R(x)*e^{sigma*branch(x)*x} (branch
fixed to +1 on the interval if it lies at x>=0, -1 if x<=0) is itself entire,
and acb.integral can be handed a genuinely analytic integrand instead of a
non-analytic |.|. Sign changes of R are located on a fast float64 grid
(numpy, diagnostic only, not a reported number) at density >=64 points per
half-oscillation length L/(2N) of the fastest mode, refined by linear
interpolation to seed the breakpoints; correctness of that density is
checked by doubling the grid and comparing the resulting M_m(sigma) (relative
change must be < 1e-8, else the (m,N,dps,sigma) cell is flagged
QUADRATURE_GRID_UNCONVERGED rather than reported as a clean number). All
arithmetic that becomes a reported number (R itself, the integral, the
imaginary-part check) is done with flint arb/acb balls at the record's dps;
mpmath is not used anywhere (not installed, and excluded by task instructions).

A separate imaginary-part diagnostic I(t) = sum (xi_n - xi_{-n})*(-1)^n*sin(n*theta(t))
is evaluated at real sample points to confirm the ledger's eigenvector is even
to the frozen 1e-30 relative tolerance; a breach is reported but does not by
itself stop the run (no STOP token is named for it in the precommit).

Known performance caveat: the sign-locating pass is O(N) per grid point via a
vectorized numpy matmul (cheap), but the certified acb.integral pass is O(N)
arb operations per quadrature node, per subinterval, per sigma, per record --
this is exact and rigorous but can become slow for the top of the schedule
(m = N = 163). Not tuned further here because no production ledger existed
at the time this script was written; see the SCRIPT_READY_AWAITING_LEDGER
path below.
"""

from __future__ import annotations

import json
import random
import sys
import time
from pathlib import Path
from typing import Any

from flint import acb, arb, ctx

REPO = Path(__file__).resolve().parents[3]
SCRIPT_DIR = REPO / "docs/routeB_bus/phase5_scripts"
OUT_DIR = SCRIPT_DIR / "out"
LEDGER_PATH = OUT_DIR / "edge_ledger.json"
BUILDER_PATH = SCRIPT_DIR / "edge_ledger_build.py"
OUT_JSON = OUT_DIR / "edge_ledger_ratio.json"
OUT_MD = OUT_DIR / "edge_ledger_probe2_probe3.md"
OUT_JSON_TEST = OUT_DIR / "edge_ledger_ratio.TEST.json"
PRECOMMIT_PATH = SCRIPT_DIR / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"

SIGMAS: list[float] = [0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45]
SIGMA_MAIN = 0.40
SCHEDULE_M: list[int] = [13, 23, 43, 83, 163]
NCHECK_PAIRS: list[tuple[int, int]] = [(13, 26), (43, 86)]  # (m, N) N-check partner at fixed m
DPS_SCHEDULE: list[int] = [120, 240]

IMAG_REL_TOL = 1e-30  # frozen, precommit Probe 3 wording ("verify ... < 1e-30 relative")
QUAD_GRID_REL_TOL = 1e-8  # frozen, precommit + task wording ("doubling the grid ... < 1e-8")
FD_HF_SIG_DIGITS = 6  # frozen, precommit Probe 2 wording
GRID_POINTS_PER_HALF_OSC = 64  # frozen, task wording ("... >= 64 points per mode oscillation length L/(2N)")

# Probe 4 (ADDENDUM 2026-09-03, P_CURVATURE_SOURCE_1), all frozen there.
CURVATURE_REF = 0.0231  # Sum_gamma 1/gamma^2 over zeta zeros, descriptive reference scale only
KAPPA_CONFIRMED_RATIO_MAX = 2
KAPPA_REFUTED_RATIO_MIN = 10

# "A result that moves between the two [precisions] is INSUFFICIENT_PRECISION,
# not a verdict" (precommit) is not given a number there. edge_ledger_build.py
# DOES give it one for the fields it produces (lambda1/lambda2/delta/
# lambda2_over_lambda1/edge_sq_*_from_even_basis/dlambda*_dL_fd/hf): its
# `sig_agree(a, b, 8)` = relative difference < 0.5e-7. Probe 3's own derived
# quantity (R_m(sigma), which the builder does not compute) is checked here
# with the SAME convention rather than inventing an unrelated threshold.
CROSS_PRECISION_SIG_DIGITS = 8


def sig_agree(a: float, b: float, sig: int = CROSS_PRECISION_SIG_DIGITS) -> bool:
    """Mirrors edge_ledger_build.py's sig_agree exactly (descriptive, not certified)."""
    if a == 0.0 and b == 0.0:
        return True
    denom = max(abs(a), abs(b))
    if denom == 0.0:
        return True
    rel = abs(a - b) / denom
    return rel < 0.5 * 10 ** (-(sig - 1))


# Fields in edge_ledger_build.py's per-cell schema whose row-level
# `insufficient_precision_flags` bear on Probe 2's c_m / c2_m.
PROBE2_PRECISION_FIELDS_LAMBDA1 = ("lambda1", "edge_sq_1_from_even_basis", "dlambda1_dL_fd", "dlambda1_dL_hf")
PROBE2_PRECISION_FIELDS_LAMBDA2 = ("lambda2", "edge_sq_2_from_even_basis", "dlambda2_dL_fd", "dlambda2_dL_hf")

REQUIRED_CELL_KEYS = {
    "m", "N", "dps", "lambda1", "lambda2", "delta",
    "xi1_pm_index", "xi2_pm_index",
    "edge_sq_1_from_pm_row", "edge_sq_2_from_pm_row",
    "dlambda1_dL_fd", "dlambda1_dL_hf", "dlambda1_dL_hf_fd_agree_6sig",
    "dlambda2_dL_fd", "dlambda2_dL_hf", "dlambda2_dL_hf_fd_agree_6sig",
}


def isatty() -> bool:
    return sys.stdout.isatty()


def progress(msg: str) -> None:
    if isatty():
        print(f"\r{msg[:120]:<120}", end="", flush=True)


def progress_done() -> None:
    if isatty():
        print()


# --------------------------------------------------------------------------
# Ledger loading / schema adapter
#
# edge_ledger_build.py's actual schema (read from that script directly, since
# it now exists on disk -- see module docstring) is NOT the flat per-record
# list this script was originally briefed against. It is:
#
#   {"schema": "EdgeLedgerBuild.v1", ..., "schedule": [ROW, ...]}
#   ROW = {"m", "N", "role" in {"main_schedule","n_check"},
#          "precision": {"120": CELL, "240": CELL},
#          "insufficient_precision_flags": [field_name, ...]}
#   CELL = {"m","N","dps", "lambda1"/"lambda2"/"delta": bounds-dict,
#           "xi1_pm_index"/"xi2_pm_index": {"note", "values": [decimal str, -N..N]},
#           "edge_sq_1_from_pm_row"/"edge_sq_2_from_pm_row": bounds-dict,
#           "dlambda1_dL_fd"/"dlambda1_dL_hf"/"dlambda2_dL_fd"/"dlambda2_dL_hf": bounds-dict,
#           "dlambda1_dL_hf_fd_agree_6sig"/"dlambda2_dL_hf_fd_agree_6sig": bool, ...}
#   bounds-dict = {"ball": str, "lower": str, "upper": str} (arb ball, see
#   phase1_scripts/ccm_control_cell_penalty.py's own `bounds()` helper).
#
# Probe 3's ksi is, per the precommit ("lambda1 = smallest eigenvalue, ksi =
# its unit-l2 even eigenvector"), the lambda1 eigenvector: xi1_pm_index.
# --------------------------------------------------------------------------

def parse_bounds(d: dict[str, Any]) -> float:
    return float(arb(d["ball"]).mid())


def flatten_schedule(schedule_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    flat: list[dict[str, Any]] = []
    for row in schedule_rows:
        m, N, role = row["m"], row["N"], row["role"]
        insuff = row.get("insufficient_precision_flags", [])
        for dps_str, cell in row["precision"].items():
            missing = REQUIRED_CELL_KEYS - set(cell)
            if missing:
                hint = ""
                if BUILDER_PATH.exists():
                    hint = f" (compare against {BUILDER_PATH}'s build_cell() return dict)"
                raise SystemExit(
                    f"edge_ledger.json m={m} N={N} dps={dps_str}: missing keys {sorted(missing)}{hint}"
                )
            flat.append(
                {
                    "m": m,
                    "N": N,
                    "role": role,
                    "dps": int(cell["dps"]),
                    "xi": cell["xi1_pm_index"]["values"],
                    "lambda1": parse_bounds(cell["lambda1"]),
                    "lambda2": parse_bounds(cell["lambda2"]),
                    "delta": parse_bounds(cell["delta"]),
                    "edge_sq": parse_bounds(cell["edge_sq_1_from_pm_row"]),
                    "edge_sq_2": parse_bounds(cell["edge_sq_2_from_pm_row"]),
                    "dlambda1_dL_fd": parse_bounds(cell["dlambda1_dL_fd"]),
                    "dlambda1_dL_hf": parse_bounds(cell["dlambda1_dL_hf"]),
                    "dlambda2_dL_fd": parse_bounds(cell["dlambda2_dL_fd"]),
                    "dlambda2_dL_hf": parse_bounds(cell["dlambda2_dL_hf"]),
                    "hf_fd_agree_1": bool(cell["dlambda1_dL_hf_fd_agree_6sig"]),
                    "hf_fd_agree_2": bool(cell["dlambda2_dL_hf_fd_agree_6sig"]),
                    "insufficient_precision_flags": list(insuff),
                }
            )
    return flat


def load_ledger() -> list[dict[str, Any]] | None:
    if not LEDGER_PATH.exists():
        return None
    payload = json.loads(LEDGER_PATH.read_text(encoding="utf-8"))
    if "schedule" not in payload:
        raise SystemExit(
            f"edge_ledger.json: no top-level 'schedule' key -- schema mismatch vs {BUILDER_PATH}"
        )
    return flatten_schedule(payload["schedule"])


def make_synthetic_schedule_row(m: int = 13, N: int = 13, dps_list: tuple[int, ...] = (120, 240),
                                 seed: int = 20260903) -> dict[str, Any]:
    """Self-made row matching edge_ledger_build.py's ACTUAL nested schema
    (schedule row -> precision -> cell), to prove the schema adapter and the
    rest of the pipeline execute end to end when no production ledger exists
    yet. Random even unit row for xi1/xi2; not a claim about any real matrix."""
    rng = random.Random(seed)

    def make_cell(dps: int) -> dict[str, Any]:
        def unit_row(offset: float, boost_index0: float = 0.0) -> list[str]:
            raw = [rng.uniform(-1.0, 1.0) + offset for _ in range(N + 1)]
            raw[0] += boost_index0  # keeps xi_0 dominant/positive so Probe 4's synthetic
            # smoke test exercises the CONFIRMED-shaped path rather than randomly
            # tripping KAPPA_NEGATIVE; not a claim about any real eigenvector.
            norm_sq = raw[0] ** 2 + 2.0 * sum(v * v for v in raw[1:])
            norm = norm_sq ** 0.5
            half = [v / norm for v in raw]
            return [f"{half[abs(n)]:.20f}" for n in range(-N, N + 1)]

        xi1 = unit_row(0.0, boost_index0=5.0)
        xi2 = unit_row(0.3)
        x1n, x10 = float(xi1[-1]), float(xi1[0])
        x2n, x20 = float(xi2[-1]), float(xi2[0])
        lambda1, lambda2 = 0.5, 0.6
        dlambda1, dlambda2 = -0.01, -0.006

        def bnd(v: float) -> dict[str, str]:
            return {"ball": repr(v), "lower": repr(v), "upper": repr(v)}

        return {
            "m": m, "N": N, "dps": dps,
            "lambda1": bnd(lambda1), "lambda2": bnd(lambda2), "delta": bnd(lambda2 - lambda1),
            "xi1_pm_index": {"note": "synthetic test row", "values": xi1},
            "xi2_pm_index": {"note": "synthetic test row", "values": xi2},
            "edge_sq_1_from_pm_row": bnd(x1n ** 2 + x10 ** 2),
            "edge_sq_2_from_pm_row": bnd(x2n ** 2 + x20 ** 2),
            "dlambda1_dL_fd": bnd(dlambda1), "dlambda1_dL_hf": bnd(dlambda1),
            "dlambda1_dL_hf_fd_agree_6sig": True,
            "dlambda2_dL_fd": bnd(dlambda2), "dlambda2_dL_hf": bnd(dlambda2),
            "dlambda2_dL_hf_fd_agree_6sig": True,
        }

    return {
        "m": m, "N": N, "role": "main_schedule",
        "precision": {str(dps): make_cell(dps) for dps in dps_list},
        "insufficient_precision_flags": [],
    }


# --------------------------------------------------------------------------
# Probe 3 core: R(x) (entire continuation of Re q_m), sign-change breakpoints,
# piecewise integration of |q_m(t)| e^{sigma|t|}.
# --------------------------------------------------------------------------

class RecordArb:
    """Precomputed arb/acb quantities for one (m, N, dps) ledger record."""

    def __init__(self, rec: dict[str, Any]) -> None:
        self.m = int(rec["m"])
        self.N = int(rec["N"])
        self.dps = int(rec["dps"])
        ctx.dps = self.dps + 15  # guard digits, mirrors phase1 convention
        self.pi = arb.pi()
        self.L = arb(self.m).log()
        self.L_float = float(self.L.mid())
        self.invsqrtL = 1 / self.L.sqrt()
        xi_strs = rec["xi"]
        if len(xi_strs) != 2 * self.N + 1:
            raise SystemExit(
                f"record m={self.m} N={self.N}: xi has {len(xi_strs)} entries, expected {2*self.N+1}"
            )
        self.xi = [arb(s) for s in xi_strs]  # index i -> n = i - N
        self.xi0 = self.xi[self.N]
        self.xi_float = [float(v.mid()) for v in self.xi]
        self.two_pi_over_L = (2 * self.pi) / self.L
        self.rec = rec

    def xi_at(self, n: int) -> arb:
        return self.xi[n + self.N]

    def R(self, x: acb | arb) -> acb | arb:
        """Entire continuation of Re[q_m](t); exact for any x, real or complex,
        symmetric xi or not (see module docstring)."""
        theta = self.two_pi_over_L * x
        c1 = theta.cos()
        s1 = theta.sin()
        one = type(x)(1)
        zero = type(x)(0)
        cn, sn = one, zero
        total = self.xi0 * one
        for n in range(1, self.N + 1):
            cn, sn = cn * c1 - sn * s1, sn * c1 + cn * s1
            sgn = -1 if (n % 2) else 1
            coeff = self.xi_at(n) + self.xi_at(-n)
            total += sgn * coeff * cn
        return self.invsqrtL * total

    def imag_check_at(self, t_float: float) -> tuple[float, float]:
        """Return (|I(t)|, |R(t)|) at a real sample point, arb precision."""
        t = arb(repr(t_float))
        theta = self.two_pi_over_L * t
        c1 = theta.cos()
        s1 = theta.sin()
        cn, sn = arb(1), arb(0)
        total_r = self.xi0 * arb(1)
        total_i = arb(0)
        for n in range(1, self.N + 1):
            cn, sn = cn * c1 - sn * s1, sn * c1 + cn * s1
            sgn = -1 if (n % 2) else 1
            coeff_r = self.xi_at(n) + self.xi_at(-n)
            coeff_i = self.xi_at(n) - self.xi_at(-n)
            total_r += sgn * coeff_r * cn
            total_i += sgn * coeff_i * sn
        r_val = float((self.invsqrtL * total_r).mid())
        i_val = float((self.invsqrtL * total_i).mid())
        return abs(i_val), abs(r_val)

    def curvature(self) -> dict[str, Any]:
        """Probe 4 (ADDENDUM, P_CURVATURE_SOURCE_1). All arb, at this
        record's working precision. From the lambda1 eigenvector xi
        (+-N indexing, raw values, no evenness assumed -- same "combine
        the n and -n raw entries" pattern as R() and edge_sq):

          S        = sum_{n=1}^{N} (xi_n + xi_{-n}) / n^2   (represents
                     sum_{n!=0,|n|<=N} xi_n/n^2 exactly, symmetric or not)
          bracket  = xi_0/12 + S/(2*pi^2)          [the F''(0) bracket]
          F(0)     = sqrt(L) * xi_0
          F''(0)   = -L^(5/2) * bracket
          kappa    = -F''(0)/(2*F(0)) = L^2 * bracket / (2*xi_0)
          kappa_forced_lower = (L^2/(4*pi^2)) * sum_{j>N} 1/j^2
                             = (L^2/(4*pi^2)) * (pi^2/6 - sum_{j=1}^{N} 1/j^2)
        """
        pi2 = self.pi * self.pi
        S = arb(0)
        tail_partial = arb(0)  # sum_{j=1}^{N} 1/j^2, reused for kappa_forced_lower
        for n in range(1, self.N + 1):
            inv_n2 = 1 / arb(n * n)
            S += (self.xi_at(n) + self.xi_at(-n)) * inv_n2
            tail_partial += inv_n2
        bracket = self.xi0 / 12 + S / (2 * pi2)
        F0 = self.L.sqrt() * self.xi0
        # L^(5/2) as L^2 * sqrt(L), avoiding a non-integer arb power call.
        Fpp0 = -(self.L * self.L * self.L.sqrt()) * bracket
        kappa = -Fpp0 / (2 * F0)
        zeta2 = pi2 / 6
        tail_sum = zeta2 - tail_partial
        kappa_forced_lower = (self.L * self.L / (4 * pi2)) * tail_sum
        bracket_f = float(bracket.mid())
        kappa_f = float(kappa.mid())
        return {
            "S": float(S.mid()),
            "bracket": bracket_f,
            "bracket_times_12": bracket_f * 12,
            "F0": float(F0.mid()),
            "Fpp0": float(Fpp0.mid()),
            "kappa": kappa_f,
            "kappa_forced_lower": float(kappa_forced_lower.mid()),
            "kappa_over_ref": kappa_f / CURVATURE_REF,
        }


def float_scan_breakpoints(rec: RecordArb, points_per_half_osc: int) -> tuple[list[float], int]:
    """Fast float64 (numpy) pre-scan: locate sign changes of R on
    [-L/2, L/2]. Returns (sorted unique breakpoints incl. endpoints and 0.0,
    number of grid points used). Diagnostic pass only -- no number derived
    here is ever reported as a result; it only seeds where to split the
    rigorous arb/acb integration."""
    import numpy as np

    L = rec.L_float
    N = rec.N
    num_points = max(2048, points_per_half_osc * 2 * N)
    ts = np.linspace(-L / 2, L / 2, num_points + 1)
    theta = (2.0 * np.pi / L) * ts
    n = np.arange(0, N + 1)
    cosmat = np.cos(np.outer(theta, n))
    coeff = np.empty(N + 1)
    coeff[0] = rec.xi_float[N]
    for k in range(1, N + 1):
        coeff[k] = rec.xi_float[N + k] + rec.xi_float[N - k]
    sgn = np.where(n % 2 == 0, 1.0, -1.0)
    weighted = coeff * sgn
    q = (cosmat @ weighted) / np.sqrt(L)

    crossings: list[float] = []
    signs = np.sign(q)
    for i in range(len(ts) - 1):
        if signs[i] == 0.0:
            crossings.append(float(ts[i]))
        elif signs[i] * signs[i + 1] < 0.0:
            t0 = ts[i] - q[i] * (ts[i + 1] - ts[i]) / (q[i + 1] - q[i])
            crossings.append(float(t0))
    bps = sorted(set([-L / 2, 0.0, L / 2] + crossings))
    return bps, num_points


def integrate_M(rec: RecordArb, breakpoints: list[float], sigmas: list[float]) -> dict[float, complex]:
    """Piecewise-analytic acb.integral of |q_m(t)| e^{sigma|t|} for each
    sigma, given a breakpoint set that separates sign-definite (and
    branch-of-|t|-definite, since 0.0 is always a breakpoint) regions."""
    rel_tol = arb(10) ** -(rec.dps + 5)
    abs_tol = arb(10) ** -(rec.dps + 5)
    totals: dict[float, complex] = {s: 0j for s in sigmas}
    bp_arb = [arb(repr(t)) for t in breakpoints]
    for a, b in zip(bp_arb[:-1], bp_arb[1:]):
        if b <= a:
            continue
        mid = (a + b) / 2
        mid_val = rec.R(mid)
        mid_float = float(mid_val.mid())
        if mid_float > 0:
            s = 1
        elif mid_float < 0:
            s = -1
        else:
            continue  # measure-zero degenerate cell, contributes 0
        branch = -1 if float(b.mid()) <= 0.0 else 1  # a,b never straddle 0 (0.0 is a forced breakpoint)
        for sigma in sigmas:
            def integrand(x: acb, _analytic: bool, s=s, branch=branch, sigma=sigma) -> acb:
                return s * rec.R(x) * (arb(sigma) * branch * x).exp()

            val = acb.integral(integrand, a, b, rel_tol=rel_tol, abs_tol=abs_tol)
            totals[sigma] += complex(float(val.real.mid()), float(val.imag.mid()))
    return totals


def probe3_for_record(rec_dict: dict[str, Any]) -> dict[str, Any]:
    rec = RecordArb(rec_dict)
    m, N, dps = rec.m, rec.N, rec.dps

    # imaginary-part sanity check at a handful of real sample points
    sample_ts = [0.0, rec.L_float / 6, rec.L_float / 4, rec.L_float / 3, -rec.L_float / 5, -rec.L_float / 2.5]
    imag_flags = []
    for t in sample_ts:
        i_abs, r_abs = rec.imag_check_at(t)
        rel = i_abs / r_abs if r_abs > 0 else i_abs
        if rel >= IMAG_REL_TOL:
            imag_flags.append({"t": t, "imag_abs": i_abs, "real_abs": r_abs, "relative": rel})

    bps1, npts1 = float_scan_breakpoints(rec, GRID_POINTS_PER_HALF_OSC)
    bps2, npts2 = float_scan_breakpoints(rec, 2 * GRID_POINTS_PER_HALF_OSC)

    M1 = integrate_M(rec, bps1, SIGMAS)
    M2 = integrate_M(rec, bps2, SIGMAS)

    denom = float(rec.L.sqrt().mid()) * abs(float(rec.xi0.mid()))
    sigma_table = {}
    grid_flags = []
    for sigma in SIGMAS:
        m1 = M1[sigma].real
        m2 = M2[sigma].real
        rel_change = abs(m2 - m1) / abs(m2) if m2 != 0 else abs(m2 - m1)
        converged = rel_change < QUAD_GRID_REL_TOL
        if not converged:
            grid_flags.append({"sigma": sigma, "relative_change": rel_change})
        numerator = m2 if converged else max(m1, m2, key=abs)
        ratio = numerator / denom if denom != 0 else float("nan")
        sigma_table[str(sigma)] = {
            "numerator_grid1": m1,
            "numerator_grid1_imag": M1[sigma].imag,
            "numerator_grid2": m2,
            "numerator_grid2_imag": M2[sigma].imag,
            "grid1_points": npts1,
            "grid2_points": npts2,
            "grid_converged": converged,
            "grid_relative_change": rel_change,
            "denominator": denom,
            "ratio": ratio,
        }

    return {
        "m": m,
        "N": N,
        "dps": dps,
        "L": rec.L_float,
        "xi0": float(rec.xi0.mid()),
        "imag_check_flags": imag_flags,
        "quadrature_grid_flags": grid_flags,
        "sigma_table": sigma_table,
    }


# --------------------------------------------------------------------------
# Probe 4 (ADDENDUM, P_CURVATURE_SOURCE_1): normalized curvature kappa from
# the lambda1 eigenvector. See RecordArb.curvature() for the arb-precision
# arithmetic; this wraps it with (m, N, dps) bookkeeping.
# --------------------------------------------------------------------------

def probe4_for_record(rec_dict: dict[str, Any]) -> dict[str, Any]:
    rec = RecordArb(rec_dict)
    curv = rec.curvature()
    return {
        "m": rec.m,
        "N": rec.N,
        "dps": rec.dps,
        "L": rec.L_float,
        **curv,
    }


# --------------------------------------------------------------------------
# Probe 2: verdict computation from ledger-provided derivative fields only.
# --------------------------------------------------------------------------

def sig_digits_agree(a: float, b: float, digits: int) -> bool:
    if a == b:
        return True
    if a == 0 or b == 0:
        return abs(a - b) < 10 ** (-digits)
    rel = abs(a - b) / max(abs(a), abs(b))
    return rel < 10 ** (-digits)


def probe2_for_record(rec: dict[str, Any]) -> dict[str, Any]:
    m, N, dps = rec["m"], rec["N"], rec["dps"]
    edge_sq = rec["edge_sq"]
    edge_sq2 = rec["edge_sq_2"]
    d1_fd, d1_hf = rec["dlambda1_dL_fd"], rec["dlambda1_dL_hf"]
    d2_fd, d2_hf = rec["dlambda2_dL_fd"], rec["dlambda2_dL_hf"]

    # Primary source of truth: the producer's own frozen 6-sig-digit check
    # (computed on full arb precision before rounding to float here).
    # Cross-checked (not overridden) by an independent recompute on the
    # rounded floats this script has to hand.
    mismatch1 = (not rec["hf_fd_agree_1"]) or (not sig_digits_agree(d1_fd, d1_hf, FD_HF_SIG_DIGITS))
    mismatch2 = (not rec["hf_fd_agree_2"]) or (not sig_digits_agree(d2_fd, d2_hf, FD_HF_SIG_DIGITS))

    c_m = -d1_hf / edge_sq if edge_sq else float("nan")
    c_m_fd = -d1_fd / edge_sq if edge_sq else float("nan")
    c2_m = -d2_hf / edge_sq2 if edge_sq2 else float("nan")
    c2_m_fd = -d2_fd / edge_sq2 if edge_sq2 else float("nan")

    dgap_dL_hf = d2_hf - d1_hf
    dgap_dL_fd = d2_fd - d1_fd

    insuff = rec.get("insufficient_precision_flags", [])
    insuff_lambda1 = any(f in insuff for f in PROBE2_PRECISION_FIELDS_LAMBDA1)
    insuff_lambda2 = any(f in insuff for f in PROBE2_PRECISION_FIELDS_LAMBDA2)

    return {
        "m": m,
        "N": N,
        "dps": dps,
        "edge_sq": edge_sq,
        "edge_sq_2": edge_sq2,
        "c_m_hf": c_m,
        "c_m_fd": c_m_fd,
        "c2_m_hf": c2_m,
        "c2_m_fd": c2_m_fd,
        "hf_fd_mismatch_lambda1": mismatch1,
        "hf_fd_mismatch_lambda2": mismatch2,
        "insufficient_precision_lambda1": insuff_lambda1,
        "insufficient_precision_lambda2": insuff_lambda2,
        "insufficient_precision_flags": insuff,
        "sign_dgap_dL_hf": (1 if dgap_dL_hf > 0 else (-1 if dgap_dL_hf < 0 else 0)),
        "sign_dgap_dL_fd": (1 if dgap_dL_fd > 0 else (-1 if dgap_dL_fd < 0 else 0)),
    }


def probe2_verdict(records: list[dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    hi_dps = max(DPS_SCHEDULE)
    schedule = [r for r in records if r["N"] == r["m"] and r["m"] in SCHEDULE_M and r["dps"] == hi_dps]

    if any(r["hf_fd_mismatch_lambda1"] or r["hf_fd_mismatch_lambda2"] for r in schedule):
        bad = [r["m"] for r in schedule if r["hf_fd_mismatch_lambda1"] or r["hf_fd_mismatch_lambda2"]]
        return "HF_FD_MISMATCH", {"mismatched_m": bad}

    insufficient_m = [r["m"] for r in schedule if r["insufficient_precision_lambda1"]]
    detail: dict[str, Any] = {
        "dps_used": hi_dps,
        "schedule_c_m": {r["m"]: r["c_m_hf"] for r in schedule},
        "insufficient_precision_m": insufficient_m,
    }
    usable = [r for r in schedule if not r["insufficient_precision_lambda1"]]
    have_all = {r["m"] for r in usable} == set(SCHEDULE_M)
    detail["have_full_schedule"] = have_all
    if not usable:
        return "UNRESOLVED", detail

    c_values = [r["c_m_hf"] for r in usable]
    signs = [1 if c > 0 else (-1 if c < 0 else 0) for c in c_values]
    all_positive = all(s > 0 for s in signs)
    sign_changes = len(set(signs)) > 1
    abs_c = [abs(c) for c in c_values]
    ratio = max(abs_c) / min(abs_c) if min(abs_c) > 0 else float("inf")
    detail["ratio_max_over_min"] = ratio
    detail["all_positive"] = all_positive
    detail["sign_changes"] = sign_changes

    if have_all and all_positive and ratio <= 3:
        return "CONFIRMED", detail
    if sign_changes or ratio >= 100:
        return "REFUTED", detail
    return "UNRESOLVED", detail


def probe3_verdict(sigma40_by_mn: dict[tuple[int, int], dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    """sigma40_by_mn maps (m, N) -> the sigma=0.40 cell at the higher of the
    two precisions, with an added "insufficient_precision" bool (True if the
    dps=120 vs dps=240 ratio moved beyond the frozen 8-sig-digit convention;
    None if only one precision was available to compare). Per the precommit
    ("a result that moves between the two is INSUFFICIENT_PRECISION, not a
    verdict"), flagged entries are excluded from have_full_schedule."""
    all_entries = {(m, N): v for (m, N), v in sigma40_by_mn.items() if N == m and m in SCHEDULE_M}
    insufficient = {mn: v for mn, v in all_entries.items() if v.get("insufficient_precision") is True}
    schedule_entries = {mn: v for mn, v in all_entries.items() if v.get("insufficient_precision") is not True}
    detail: dict[str, Any] = {
        "insufficient_precision_mn": sorted(insufficient),
    }

    have_all = {m for (m, N) in schedule_entries} == set(SCHEDULE_M)
    detail["have_full_schedule"] = have_all

    if have_all:
        ratios_ordered = [schedule_entries[(m, m)]["ratio"] for m in SCHEDULE_M]
        monotone = all(ratios_ordered[i] <= ratios_ordered[i + 1] for i in range(len(ratios_ordered) - 1))
        growth = ratios_ordered[-1] / ratios_ordered[0] if ratios_ordered[0] != 0 else float("inf")
        detail["ratios_by_m"] = dict(zip(SCHEDULE_M, ratios_ordered))
        detail["monotone_nondecreasing"] = monotone
        detail["ratio_163_over_13"] = growth
        if monotone and growth >= 3:
            return "GROWS", detail
        max_r = max(ratios_ordered)
        min_r = min(ratios_ordered)
        bounded_ratio = max_r / min_r if min_r != 0 else float("inf")
        detail["bounded_max_over_min"] = bounded_ratio
        if bounded_ratio <= 1.5:
            return "BOUNDED", detail

    geometry_first_hits = []
    for (m, n2) in NCHECK_PAIRS:
        r_m = sigma40_by_mn.get((m, m))
        r_n2 = sigma40_by_mn.get((m, n2))
        if r_m is None or r_n2 is None:
            continue
        a, b = r_m["ratio"], r_n2["ratio"]
        if min(a, b) <= 0:
            continue
        factor = max(a, b) / min(a, b)
        geometry_first_hits.append({"m": m, "N_pair": (m, n2), "factor": factor})
        if factor >= 2:
            detail["geometry_first_hits"] = geometry_first_hits
            return "GEOMETRY_FIRST", detail
    detail["geometry_first_hits"] = geometry_first_hits
    return "UNRESOLVED", detail


def probe4_verdict(records4: list[dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    """P_CURVATURE_SOURCE_1, frozen in the precommit ADDENDUM:
    - CONFIRMED: kappa_m > 0 for every m and max/min <= 2 over the schedule.
    - REFUTED: kappa_m grows monotonically with kappa_163/kappa_13 >= 10,
      or kappa_m < 0 for some m (implemented as the KAPPA_NEGATIVE stop below,
      per the addendum's own parenthetical).
    - else UNRESOLVED.
    A dps=120 vs dps=240 move on kappa_m (same 8-sig-digit sig_agree()
    convention used throughout this script) excludes that m from the
    schedule, exactly as Probe 2/3 do."""
    lo_dps, hi_dps = min(DPS_SCHEDULE), max(DPS_SCHEDULE)

    negative_hits = [
        {"m": r["m"], "dps": r["dps"], "kappa": r["kappa"]}
        for r in records4
        if r["N"] == r["m"] and r["m"] in SCHEDULE_M and r["kappa"] < 0
    ]
    if negative_hits:
        return "KAPPA_NEGATIVE", {"negative_hits": negative_hits}

    by_mn_dps = {(r["m"], r["N"], r["dps"]): r for r in records4}
    schedule = [
        r for r in records4
        if r["N"] == r["m"] and r["m"] in SCHEDULE_M and r["dps"] == hi_dps
    ]

    insufficient_m = []
    kept = []
    for r in schedule:
        m = r["m"]
        lo = by_mn_dps.get((m, m, lo_dps))
        if lo is not None and not sig_agree(lo["kappa"], r["kappa"]):
            insufficient_m.append(m)
            continue
        kept.append(r)

    have_all = {r["m"] for r in kept} == set(SCHEDULE_M)
    detail: dict[str, Any] = {
        "dps_used": hi_dps,
        "schedule_kappa_m": {r["m"]: r["kappa"] for r in schedule},
        "insufficient_precision_m": insufficient_m,
        "have_full_schedule": have_all,
    }
    if not kept:
        return "UNRESOLVED", detail

    kappa_by_m = {r["m"]: r["kappa"] for r in kept}
    kappa_values = list(kappa_by_m.values())
    ratio = max(kappa_values) / min(kappa_values) if min(kappa_values) > 0 else float("inf")
    detail["ratio_max_over_min"] = ratio

    if have_all and ratio <= KAPPA_CONFIRMED_RATIO_MAX:
        return "CONFIRMED", detail

    if 13 in kappa_by_m and 163 in kappa_by_m:
        ms_ordered = sorted(kappa_by_m)
        kappa_ordered = [kappa_by_m[m] for m in ms_ordered]
        monotone_increasing = all(kappa_ordered[i] <= kappa_ordered[i + 1] for i in range(len(kappa_ordered) - 1))
        growth = kappa_by_m[163] / kappa_by_m[13]
        detail["monotone_increasing"] = monotone_increasing
        detail["kappa_163_over_13"] = growth
        if monotone_increasing and growth >= KAPPA_REFUTED_RATIO_MIN:
            return "REFUTED", detail

    return "UNRESOLVED", detail


# --------------------------------------------------------------------------
# TOOLS.yaml-facing report writer
# --------------------------------------------------------------------------

PRECOMMIT_PROBE2_LINES = (
    "- CONFIRMED: c_m > 0 for every m in the schedule and max c_m / min c_m <= 3.\n"
    "- REFUTED: sign of c_m changes across the schedule, or max/min >= 100.\n"
    "- else UNRESOLVED."
)
PRECOMMIT_PROBE3_LINES = (
    "- GROWS (confirmed): R_m(0.40) monotone increasing over the schedule and "
    "R_163(0.40)/R_13(0.40) >= 3.\n"
    "- BOUNDED: max/min of R_m(0.40) over the schedule <= 1.5.\n"
    "- GEOMETRY_FIRST: at fixed m the N-check changes R_m(0.40) by a factor >= 2.\n"
    "- else UNRESOLVED."
)
PRECOMMIT_PROBE4_LINES = (
    "- CONFIRMED: kappa_m > 0 for every m and max kappa_m / min kappa_m <= 2 over the schedule.\n"
    "- REFUTED: kappa_m grows monotonically with kappa_163/kappa_13 >= 10, or kappa_m < 0 for "
    "some m (a negative kappa contradicts the real-zero product and is a STOP: KAPPA_NEGATIVE).\n"
    "- else UNRESOLVED. N-check pairs are descriptive."
)


def write_report(
    probe3_records: list[dict[str, Any]],
    probe2_records: list[dict[str, Any]],
    probe4_records: list[dict[str, Any]],
    probe3_verdict_tuple: tuple[str, dict[str, Any]],
    probe2_verdict_tuple: tuple[str, dict[str, Any]],
    probe4_verdict_tuple: tuple[str, dict[str, Any]],
    out_md: Path,
    test_mode: bool,
    incomplete_schedule: bool = False,
) -> None:
    v3, d3 = probe3_verdict_tuple
    v2, d2 = probe2_verdict_tuple
    v4, d4 = probe4_verdict_tuple
    lines = []
    lines.append("# Edge ledger Probe 2 / Probe 3 / Probe 4 report")
    lines.append("")
    if test_mode:
        lines.append("**TEST RUN on a self-made synthetic record -- NOT the production ledger.**")
        lines.append("")
    if incomplete_schedule:
        lines.append(
            "**INCOMPLETE SCHEDULE: run on partial ledger data (not all of m in "
            f"{list(SCHEDULE_M)} present); schedule-wide verdicts below are marked "
            "UNRESOLVED_INCOMPLETE_SCHEDULE rather than a real CONFIRMED/REFUTED/BOUNDED/GROWS.**"
        )
        lines.append("")
    lines.append(f"Generated: {time.strftime('%Y-%m-%d %H:%M:%S %Z')}")
    lines.append(f"Precommit: `{PRECOMMIT_PATH.relative_to(REPO)}` (frozen before any run; ADDENDUM adds Probe 4)")
    lines.append("")
    lines.append("DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE.")
    lines.append("")
    lines.append("## Probe 3 verdict (quoted rule)")
    lines.append("")
    lines.append(PRECOMMIT_PROBE3_LINES)
    lines.append("")
    lines.append(f"**VERDICT: {v3}**")
    lines.append("")
    lines.append(f"Detail: `{json.dumps(d3, default=str)}`")
    lines.append("")
    lines.append("## Probe 2 verdict (quoted rule)")
    lines.append("")
    lines.append(PRECOMMIT_PROBE2_LINES)
    lines.append("")
    lines.append(f"**VERDICT: {v2}**")
    lines.append("")
    lines.append(f"Detail: `{json.dumps(d2, default=str)}`")
    lines.append("")
    lines.append("## Probe 4 verdict (quoted rule, ADDENDUM P_CURVATURE_SOURCE_1)")
    lines.append("")
    lines.append(PRECOMMIT_PROBE4_LINES)
    lines.append("")
    lines.append(f"**VERDICT: {v4}**")
    lines.append("")
    lines.append(f"Detail: `{json.dumps(d4, default=str)}`")
    lines.append("")
    lines.append("## sigma-table (Probe 3), all records")
    lines.append("")
    lines.append("| m | N | dps | sigma | numerator | denominator | ratio | grid_converged |")
    lines.append("|---|---|-----|-------|-----------|-------------|-------|-----------------|")
    for rec in probe3_records:
        for sigma_str, cell in rec["sigma_table"].items():
            lines.append(
                f"| {rec['m']} | {rec['N']} | {rec['dps']} | {sigma_str} | "
                f"{cell['numerator_grid2']:.10g} | {cell['denominator']:.10g} | "
                f"{cell['ratio']:.10g} | {cell['grid_converged']} |"
            )
    lines.append("")
    lines.append("## Probe 2 per-record")
    lines.append("")
    lines.append("| m | N | dps | c_m (HF) | c2_m (HF) | sign dGap/dL (HF) | HF/FD mismatch |")
    lines.append("|---|---|-----|----------|-----------|-------------------|-----------------|")
    for rec in probe2_records:
        mismatch = rec["hf_fd_mismatch_lambda1"] or rec["hf_fd_mismatch_lambda2"]
        lines.append(
            f"| {rec['m']} | {rec['N']} | {rec['dps']} | {rec['c_m_hf']:.10g} | "
            f"{rec['c2_m_hf']:.10g} | {rec['sign_dgap_dL_hf']} | {mismatch} |"
        )
    lines.append("")
    lines.append("## Probe 4 (kappa) per-record")
    lines.append("")
    lines.append(
        "| m | N | dps | bracket | bracket*12 | kappa | kappa_forced_lower | kappa/0.0231 |"
    )
    lines.append("|---|---|-----|---------|------------|-------|---------------------|--------------|")
    for rec in probe4_records:
        lines.append(
            f"| {rec['m']} | {rec['N']} | {rec['dps']} | {rec['bracket']:.10g} | "
            f"{rec['bracket_times_12']:.10g} | {rec['kappa']:.10g} | "
            f"{rec['kappa_forced_lower']:.10g} | {rec['kappa_over_ref']:.10g} |"
        )
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def relabel_if_incomplete(verdict_tuple: tuple[str, dict[str, Any]]) -> tuple[str, dict[str, Any]]:
    """UNRESOLVED purely because the main schedule isn't fully present is a
    different situation from UNRESOLVED on complete, computed-but-ambiguous
    numbers; label the former UNRESOLVED_INCOMPLETE_SCHEDULE so it's never
    mistaken for the latter (coordinator instruction, 2026-09-03)."""
    label, detail = verdict_tuple
    if label == "UNRESOLVED" and detail.get("have_full_schedule") is False:
        return "UNRESOLVED_INCOMPLETE_SCHEDULE", detail
    return label, detail


def run(records: list[dict[str, Any]], test_mode: bool) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    probe3_records = []
    for i, rec in enumerate(records):
        progress(f"probe3 record {i+1}/{len(records)} m={rec['m']} N={rec['N']} dps={rec['dps']}")
        probe3_records.append(probe3_for_record(rec))
    progress_done()

    probe2_records = [probe2_for_record(rec) for rec in records]

    probe4_records = []
    for i, rec in enumerate(records):
        progress(f"probe4 record {i+1}/{len(records)} m={rec['m']} N={rec['N']} dps={rec['dps']}")
        probe4_records.append(probe4_for_record(rec))
    progress_done()

    if any(r["hf_fd_mismatch_lambda1"] or r["hf_fd_mismatch_lambda2"] for r in probe2_records):
        bad = [r["m"] for r in probe2_records if r["hf_fd_mismatch_lambda1"] or r["hf_fd_mismatch_lambda2"]]
        print(f"\nHF_FD_MISMATCH at m={bad}: FD and HF derivatives disagree beyond "
              f"{FD_HF_SIG_DIGITS} significant digits.")
        sys.exit("HF_FD_MISMATCH")

    v4 = probe4_verdict(probe4_records)
    if v4[0] == "KAPPA_NEGATIVE":
        print(f"\nKAPPA_NEGATIVE: {v4[1]}")
        print("A negative curvature contradicts the real-zero product (precommit ADDENDUM). Stopping.")
        sys.exit("KAPPA_NEGATIVE")

    hi_dps = max(DPS_SCHEDULE)
    by_mn_dps = {(r["m"], r["N"], r["dps"]): r for r in probe3_records}
    mn_pairs = sorted({(r["m"], r["N"]) for r in probe3_records})
    sigma40_by_mn: dict[tuple[int, int], dict[str, Any]] = {}
    for (m, N) in mn_pairs:
        available_dps = sorted(dps for dps in DPS_SCHEDULE if (m, N, dps) in by_mn_dps)
        if hi_dps not in available_dps:
            continue  # no high-precision cell for this (m,N); nothing to report at sigma=0.40
        cell = dict(by_mn_dps[(m, N, hi_dps)]["sigma_table"][str(SIGMA_MAIN)])
        if len(available_dps) >= 2:
            lo_dps = available_dps[0]
            lo_ratio = by_mn_dps[(m, N, lo_dps)]["sigma_table"][str(SIGMA_MAIN)]["ratio"]
            hi_ratio = cell["ratio"]
            cell["insufficient_precision"] = not sig_agree(lo_ratio, hi_ratio)
            cell["dps_compared"] = [lo_dps, hi_dps]
        else:
            cell["insufficient_precision"] = None  # only one precision available; not comparable
            cell["dps_compared"] = available_dps
        sigma40_by_mn[(m, N)] = cell
    v3 = relabel_if_incomplete(probe3_verdict(sigma40_by_mn))
    v2 = relabel_if_incomplete(probe2_verdict(probe2_records))
    v4 = relabel_if_incomplete(v4)

    out_json_path = OUT_JSON_TEST if test_mode else OUT_JSON
    out_json_path.write_text(
        json.dumps(
            {
                "test_mode": test_mode,
                "probe3_records": probe3_records,
                "probe2_records": probe2_records,
                "probe4_records": probe4_records,
                "probe3_verdict": {"verdict": v3[0], "detail": v3[1]},
                "probe2_verdict": {"verdict": v2[0], "detail": v2[1]},
                "probe4_verdict": {"verdict": v4[0], "detail": v4[1]},
            },
            indent=2,
            default=str,
        ),
        encoding="utf-8",
    )

    out_md_path = OUT_MD  # always write the human report at the canonical path; test runs are labeled inline
    write_report(
        probe3_records, probe2_records, probe4_records, v3, v2, v4, out_md_path, test_mode,
        incomplete_schedule=any(v[0] == "UNRESOLVED_INCOMPLETE_SCHEDULE" for v in (v2, v3, v4)),
    )

    print(f"\nProbe 3 verdict: {v3[0]}  detail={v3[1]}")
    print(f"Probe 2 verdict: {v2[0]}  detail={v2[1]}")
    print(f"Probe 4 verdict: {v4[0]}  detail={v4[1]}")
    print(f"\nsigma=0.40 table:")
    for rec in probe3_records:
        cell = rec["sigma_table"][str(SIGMA_MAIN)]
        print(f"  m={rec['m']:<4} N={rec['N']:<4} dps={rec['dps']:<4} ratio={cell['ratio']:.10g} "
              f"converged={cell['grid_converged']}")
    print(f"\nsigma=0.20 table:")
    for rec in probe3_records:
        cell = rec["sigma_table"]["0.2"]
        print(f"  m={rec['m']:<4} N={rec['N']:<4} dps={rec['dps']:<4} ratio={cell['ratio']:.10g} "
              f"converged={cell['grid_converged']}")
    print(f"\nkappa table (Probe 4):")
    for rec in probe4_records:
        print(f"  m={rec['m']:<4} N={rec['N']:<4} dps={rec['dps']:<4} kappa={rec['kappa']:.10g} "
              f"bracket*12={rec['bracket_times_12']:.10g} kappa/0.0231={rec['kappa_over_ref']:.10g}")
    for rec in probe3_records:
        if rec["imag_check_flags"]:
            print(f"  WARNING imag-part check flagged for m={rec['m']} N={rec['N']}: {rec['imag_check_flags']}")
        if rec["quadrature_grid_flags"]:
            print(f"  WARNING quadrature-grid check flagged for m={rec['m']} N={rec['N']}: "
                  f"{rec['quadrature_grid_flags']}")
    print(f"\nWrote {out_json_path} and {out_md_path}")


def main() -> None:
    records = load_ledger()
    if records is not None:
        run(records, test_mode=False)
        return

    print(f"{LEDGER_PATH} not found.")
    if BUILDER_PATH.exists():
        print(f"Producer script present at {BUILDER_PATH}; its schema was consulted for this reader.")
    else:
        print(f"Producer script {BUILDER_PATH} also absent; reading the schema from the task spec only.")
    print("Running on one self-made synthetic schedule row (random even unit row, m=13, N=13, "
          "matching edge_ledger_build.py's actual nested schema) to prove the schema adapter "
          "and the rest of the pipeline execute...")
    synthetic_row = make_synthetic_schedule_row()
    test_records = flatten_schedule([synthetic_row])
    run(test_records, test_mode=True)
    print("\nSCRIPT_READY_AWAITING_LEDGER")
    print(f"Run later with: {sys.executable} {Path(__file__).resolve()}")
    print(f"(after {LEDGER_PATH} exists with the schema in the task spec)")


if __name__ == "__main__":
    main()
