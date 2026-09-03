#!/usr/bin/env python3
"""Relative-Ritz supplier columns for the Goal 058 edge ledger.

Judge source: `docs/routeB_bus/proshka/
PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md`,
CHEAPEST_NEXT_ACTION (code HARVEST_PRECOMMITTED_EDGE_LEDGER_WITH_RELATIVE_RITZ_COLUMNS)
and section 3 (the exact relative-Ritz theorem). This script reads
`docs/routeB_bus/phase5_scripts/out/edge_ledger.json` (produced by
`edge_ledger_build.py`, not touched here) and, for every schedule cell,
computes the DESCRIPTIVE columns the verdict asks for:

    lambda1, lambda2, g = lambda2/lambda1, Rayleigh(q) = q^T K q,
    epsilon = Rayleigh(q)/lambda1 - 1, eta = epsilon/(g-1),
    p = 1 - |<xi,q>|^2 (direct, from the ledger's own lambda1 eigenvector),
    the mathematical relation p <= eta (the verdict's own boxed inequality,
    not a pass/fail threshold on the underlying physics), and L = log(m).

DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE.
This script does not add any post-hoc verdict on top of these numbers.

--------------------------------------------------------------------------
The trial vector q -- what it is, and why it is only available for five of
the seven ledger cells plus one bonus (non-ledger) cell
--------------------------------------------------------------------------
q is the projected prolate ("k1"/"g04") trial row used by Phase 1
(`docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py`): it reads
`q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/
portable_k_coeffs_lambda_sq_13_N_120.json`, takes the exact-decimal complex
coefficients c_n (n = -N..N), forms the exact J-even projection
(c_n + c_{-n})/2 (discarding the imaginary part, which the source file
itself records as a small residual, not exactly zero), and normalizes by
the exact Euclidean norm over n = -N..N (== the even-basis l2 norm, by the
same c_0 / sqrt(2)*c_i isometry edge_ledger_build.py documents for xi).

The generator of that file is
`q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/
portable_k_channel_v1.py`'s `build_coeff_cache(lambda_sq, n_bound)`, which
calls `true_precision_packet_gate_v1.build_prolate_model` (an angular
prolate-spheroidal eigenproblem, Legendre-Galerkin truncated at degree
`MAX_DEGREE`) and `.integrate_coefficients` (breakpoint-split Gaussian
quadrature). Its *callable signature* accepts arbitrary (lambda_sq, N):
lambda_sq is the CCM window parameter m (L = log(lambda_sq)), N is the
number of Fourier-mode coefficients returned, and neither one is
hard-coded in `build_coeff_cache` itself.

But `true_precision_packet_gate_v1.py` has one module-level constant that
IS hard-coded and is NOT exposed by `build_coeff_cache`'s signature:

    MAX_DEGREE = 180

This is the truncation degree of the Legendre expansion used to compute the
angular prolate eigenfunctions themselves (independent of N; it depends
only on lambda_sq via c = 2*pi*lambda_sq). A degree-180 truncation is
adequate near lambda_sq = 13 (c ~ 81.7, the value the constant was
evidently tuned/verified for) but is a genuine, measurable, growing
under-resolution at the top of the production schedule. This was checked
directly (double-precision numpy replica of the exact same Legendre-Galerkin
matrix, comparing MAX_DEGREE=180 against MAX_DEGREE=400+ for the same
lambda_sq; see PARAMETRIZABILITY_CHECK below and the .md report):

    lambda_sq =  13 (c ~   81.7): MAX_DEGREE=180 already at the converged
                                    value (identical eigenvalue/eigenvector
                                    tail across 180..900); FAITHFUL.
    lambda_sq =  23 (c ~  144.5): converged the same way; FAITHFUL.
    lambda_sq =  43 (c ~  270.2): converged to noise floor (~1e-18); FAITHFUL.
    lambda_sq =  83 (c ~  521.5): relative truncation error ~8e-9 at
                                    MAX_DEGREE=180 (only ~8-9 correct
                                    digits); NOT faithful at the ledger's
                                    own working precision (120/240 dps).
    lambda_sq = 163 (c ~ 1024.2): relative truncation error ~5e-4 at
                                    MAX_DEGREE=180 (only ~3-4 correct
                                    digits); NOT faithful at all.

So the generator is genuinely parametrizable (same construction, no
modification, just different (lambda_sq, N) arguments) for the three
smaller schedule members -- lambda_sq in {13, 23, 43} -- covering five of
the seven ledger cells: (13,13), (13,26), (23,23), (43,43), (43,86). It is
NOT faithfully parametrizable for the top two: (83,83) and (163,163). This
script therefore:

  * generates fresh trial-coefficient caches at (13,13), (13,26), (23,23),
    (43,43), (43,86) by calling the SAME unmodified generator
    (`portable_k_channel_v1.build_coeff_cache`, no MAX_DEGREE change, no
    substitute construction) -- done once, out-of-band, via system
    python3+mpmath (this script's own runtime is .venv/bin/python,
    python-flint only, no mpmath, per the task boundary; the generator
    itself needs mpmath and was run separately as a one-line invocation of
    `portable_k_channel_v1.build_coeff_cache(m, n)` for each of the five
    (m, n) pairs -- no code in that generator was modified). The
    resulting JSON files live next to the pinned (13,120) cache, in
    `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/`,
    following that generator's own existing naming convention
    (`portable_k_coeffs_lambda_sq_{m}_N_{n}.json`) -- nothing under
    `docs/routeB_bus/phase5_scripts/out/` other than this script's three
    named outputs is touched;
  * reports TRIAL_GENERATOR_NOT_PARAMETRIZABLE for (83,83) and (163,163),
    with the measured truncation error as the exact reason, and computes
    only the q-independent columns (lambda1, lambda2, g, L) for those two;
  * additionally computes one BONUS row outside the ledger schedule,
    (m=13, N=120), using the literal SHA-256-pinned Phase 1 trial file and
    a freshly built (m=13, N=120) CCM matrix (via
    `edge_ledger_build.CCMArbBuilder`, imported, and
    `edge_ledger_build.robust_eig`, imported, for lambda1/lambda2/xi at
    240 dps) -- this is the exact object Phase 1 already certified, kept
    as an independent cross-check of this script's own arithmetic.

The matrix K is always `edge_ledger_build.CCMArbBuilder(m, N).even_block()`
(imported, never copied), rebuilt fresh at the record's own dps -- the same
even-sector block `edge_ledger_build.py` used to obtain lambda1/lambda2/xi
for that ledger cell. q is mapped into the SAME even basis as xi
(xi_even[0] = c_0, xi_even[i] = sqrt(2)*c_i for i=1..N; the c_n's are
already the exact J-even-projected, Euclidean-normalized trial
coefficients), so <xi,q> and q^T K q are both computed in the one
orthonormal even basis edge_ledger_build.py documents, and ||q|| = 1 in
that same norm by construction (checked and stored per cell as
q_norm_sq_minus_1).
"""

from __future__ import annotations

import importlib.util
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any

from flint import arb, ctx

REPO = Path(__file__).resolve().parents[3]
SCRIPT_DIR = REPO / "docs/routeB_bus/phase5_scripts"
OUT_DIR = SCRIPT_DIR / "out"
LEDGER_PATH = OUT_DIR / "edge_ledger.json"
BUILDER_PATH = SCRIPT_DIR / "edge_ledger_build.py"
OUT_JSON = OUT_DIR / "edge_ledger_relritz.json"
OUT_MD = OUT_DIR / "edge_ledger_relritz.md"
VERDICT_PATH = REPO / (
    "docs/routeB_bus/proshka/"
    "PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md"
)

TRIAL_SOURCE_DIR = REPO / "q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder"
TRIAL_GENERATOR_PATH = TRIAL_SOURCE_DIR / "portable_k_channel_v1.py"
TRIAL_OUT_DIR = TRIAL_SOURCE_DIR / "out"
PINNED_TRIAL_JSON = TRIAL_OUT_DIR / "portable_k_coeffs_lambda_sq_13_N_120.json"
PINNED_TRIAL_SHA256 = "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88"

DPS_SCHEDULE = (120, 240)
BONUS_M, BONUS_N = 13, 120

# (m, N) cells where the SAME unmodified trial generator (MAX_DEGREE=180,
# no substitute) was checked and found faithful; the coefficient cache was
# freshly generated at each of these via portable_k_channel_v1.build_coeff_cache.
FAITHFUL_MN = ((13, 13), (13, 26), (23, 23), (43, 43), (43, 86))
# (m, N) main-schedule cells where MAX_DEGREE=180 is demonstrably NOT
# converged (see module docstring / PARAMETRIZABILITY_CHECK below).
NOT_PARAMETRIZABLE_MN = ((83, 83), (163, 163))

PARAMETRIZABILITY_CHECK = {
    "method": (
        "Reproduced true_precision_packet_gate_v1.build_prolate_model's exact "
        "Legendre-Galerkin matrix (legendre_x2_matrix_mp -> A = diag(k(k+1)) + "
        "c^2*X2, c = 2*pi*lambda_sq) independently in double-precision numpy, "
        "diagonalized it at MAX_DEGREE in {180, 260, 360, 400, 520, 700, 900}, "
        "and measured (a) stability of the lowest eigenvalue chi_0 across "
        "cutoffs and (b) the fraction of the 3rd-lowest eigenvector's l2 mass "
        "(the 'which=4' component entering the g04 = k1 combo) lying in the "
        "top 10% of degrees at MAX_DEGREE=180, versus the same eigenvector "
        "re-expressed at a much larger cutoff. This is a diagnostic "
        "convergence check on the generator's OWN construction, not a new "
        "trial or a new object."
    ),
    "measured_relative_truncation_error_at_MAX_DEGREE_180": {
        13: "~0 (identical to >=400-degree reference at double-precision resolution)",
        23: "~0 (identical to >=400-degree reference at double-precision resolution)",
        43: "~4e-18 (at the double-precision noise floor)",
        83: "~8.2e-9 (measured, real, not a rounding artifact: 8-9 correct digits)",
        163: "~4.9e-4 (measured, real: only 3-4 correct digits)",
    },
    "conclusion": (
        "MAX_DEGREE=180 is a hard-coded module constant in "
        "true_precision_packet_gate_v1.py, not exposed by "
        "build_coeff_cache(lambda_sq, n_bound)'s public signature, and not "
        "scaled with lambda_sq. It is adequate (faithful, same construction) "
        "for lambda_sq in {13, 23, 43}. For lambda_sq in {83, 163} it leaves "
        "a growing, non-negligible truncation error that swamps any of the "
        "requested descriptive columns at the ledger's own 120/240/900 dps "
        "working precision. Raising MAX_DEGREE for those two cells would "
        "require inventing a new degree-cutoff rule not present in or "
        "implied by the generator as written -- exactly the substitute this "
        "task instructs against -- so those two cells are reported as "
        "TRIAL_GENERATOR_NOT_PARAMETRIZABLE instead."
    ),
}


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


def _import_edge_ledger_build():
    """Import edge_ledger_build.py by path (sibling script, not a package,
    never copied or modified)."""
    spec = importlib.util.spec_from_file_location("edge_ledger_build", BUILDER_PATH)
    if spec is None or spec.loader is None:
        raise SystemExit(f"cannot import {BUILDER_PATH}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


elb = _import_edge_ledger_build()


def bounds(value: arb) -> dict[str, str]:
    return {"ball": str(value), "lower": str(value.lower()), "upper": str(value.upper())}


def sha256_file(path: Path) -> str:
    import hashlib

    return hashlib.sha256(path.read_bytes()).hexdigest()


# --------------------------------------------------------------------------
# Ledger loading (schema per edge_ledger_build.py; see edge_ledger_ratio.py's
# own adapter comment for the same schema description)
# --------------------------------------------------------------------------

def load_ledger_schedule() -> list[dict[str, Any]]:
    if not LEDGER_PATH.exists():
        raise SystemExit(f"{LEDGER_PATH} not found -- run edge_ledger_build.py first")
    payload = json.loads(LEDGER_PATH.read_text(encoding="utf-8"))
    if "schedule" not in payload:
        raise SystemExit(f"{LEDGER_PATH}: no top-level 'schedule' key")
    return payload["schedule"]


# --------------------------------------------------------------------------
# Trial vector q: exact J-even projection + Euclidean normalization of a
# portable_k_coeffs_lambda_sq_{m}_N_{N}.json cache, mirroring
# docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py's
# q_source_exact_even() byte-for-byte (Fraction exact rationals; the only
# difference is this reads whichever (m,N) cache file is relevant, not only
# the pinned 13/120 one, and does not enforce the pinned SHA on the freshly
# generated files -- their own sha256 is recorded instead, see below).
# --------------------------------------------------------------------------

def trial_cache_path(m: int, N: int) -> Path:
    return TRIAL_OUT_DIR / f"portable_k_coeffs_lambda_sq_{m}_N_{N}.json"


def q_projected_exact_even(m: int, N: int, *, expected_sha256: str | None = None) -> tuple[list[Fraction], dict[str, Any]]:
    path = trial_cache_path(m, N)
    if not path.exists():
        raise SystemExit(f"trial cache {path} not found")
    actual_sha = sha256_file(path)
    if expected_sha256 is not None and actual_sha != expected_sha256:
        raise SystemExit(f"trial cache {path} sha256 mismatch: {actual_sha} != {expected_sha256}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("lambda_sq") != m or payload.get("N") != N or payload.get("logical_vector") != "k1":
        raise SystemExit(f"trial cache {path}: object mismatch {payload.get('lambda_sq')},{payload.get('N')}")
    rows = payload["coefficients"]
    if [row["n"] for row in rows] != list(range(-N, N + 1)):
        raise SystemExit(f"trial cache {path}: mode ordering mismatch")

    real = {row["n"]: Fraction(row["re"]) for row in rows}
    imag = {row["n"]: Fraction(row["im"]) for row in rows}
    projected = [(real[n] + real[-n]) / 2 for n in range(-N, N + 1)]
    if any(projected[n + N] != projected[-n + N] for n in range(-N, N + 1)):
        raise SystemExit(f"trial cache {path}: exact J-even projection failed")
    norm_sq = sum((x * x for x in projected), Fraction(0))
    if norm_sq <= 0:
        raise SystemExit(f"trial cache {path}: projected q is zero")

    max_real_asym = max(abs(real[n] - real[-n]) for n in range(-N, N + 1))
    max_conj_err = max(abs(imag[n] + imag[-n]) for n in range(-N, N + 1))
    discarded_imag_norm_sq = sum((x * x for x in imag.values()), Fraction(0))
    meta = {
        "source": str(path.relative_to(REPO)) if path.is_relative_to(REPO) else str(path),
        "sha256": actual_sha,
        "construction": "exact_decimal_rationals_then_(q+Jq)/2_then_Euclidean_normalize",
        "generator": str(TRIAL_GENERATOR_PATH.relative_to(REPO)) + "::build_coeff_cache(lambda_sq, n_bound)",
        "cache_dps": payload.get("dps"),
        "quad_order": payload.get("quad_order"),
        "coeff_max_abs_diff_vs_half_quad_order": payload.get("coeff_max_abs_diff_vs_half_q"),
        "max_real_J_asymmetry_before_projection": str(max_real_asym),
        "max_conjugacy_error_before_projection": str(max_conj_err),
        "discarded_imag_norm_sq": str(discarded_imag_norm_sq),
    }
    return projected, meta


def q_even_from_projected(projected: list[Fraction], N: int) -> list[Fraction]:
    """c_0 = projected[N]; c_i = projected[N+i] for i=1..N (already J-even,
    i.e. projected[N+i] == projected[N-i]); UNNORMALIZED even-basis vector
    (the sqrt(2) factor and final unit-normalization are applied by the
    caller with arb at the working dps, since sqrt is not exact in Q)."""
    return [projected[N + i] for i in range(0, N + 1)]


# --------------------------------------------------------------------------
# Per-cell computation
# --------------------------------------------------------------------------

def compute_columns(
    m: int,
    N: int,
    dps: int,
    lambda1_ball: str,
    lambda2_ball: str,
    xi_even_strs: list[str],
    q_even_exact: list[Fraction],
    q_meta: dict[str, Any],
) -> dict[str, Any]:
    ctx.dps = dps + 20  # guard digits, mirrors phase1/phase5 convention
    ctx.threads = 1
    lambda1 = arb(lambda1_ball)
    lambda2 = arb(lambda2_ball)
    xi_even = [arb(s) for s in xi_even_strs]
    if len(xi_even) != N + 1:
        raise SystemExit(f"m={m} N={N} dps={dps}: xi_even_basis length {len(xi_even)} != N+1={N+1}")

    sqrt2 = arb(2).sqrt()
    # q_even_exact is indexed [c_0, c_1, ..., c_N] (the pm-indexed trial's
    # n=0..N half, already J-even so c_i == c_{-i}). The norm in the even
    # basis -- the SAME norm xi is unit in -- is c_0^2 + 2*sum_{i=1}^N c_i^2
    # (the isometry edge_ledger_build.py documents: xi_even[0]=c_0,
    # xi_even[i]=sqrt(2)*c_i), NOT a plain sum of squares over this half-range.
    norm_sq_exact = q_even_exact[0] * q_even_exact[0] + 2 * sum(
        (q_even_exact[i] * q_even_exact[i] for i in range(1, N + 1)), Fraction(0)
    )
    norm = (arb(norm_sq_exact.numerator) / norm_sq_exact.denominator).sqrt()
    q_even = [arb(q_even_exact[0].numerator) / q_even_exact[0].denominator / norm]
    for i in range(1, N + 1):
        c_i = q_even_exact[i]
        q_even.append(sqrt2 * (arb(c_i.numerator) / c_i.denominator) / norm)
    q_norm_sq = sum((x * x for x in q_even), arb(0))

    K = elb.CCMArbBuilder(m, N).even_block()
    Kq = [sum((K[i, j] * q_even[j] for j in range(N + 1)), arb(0)) for i in range(N + 1)]
    rayleigh_q = sum((q_even[i] * Kq[i] for i in range(N + 1)), arb(0))

    inner_xi_q = sum((xi_even[i] * q_even[i] for i in range(N + 1)), arb(0))
    p_direct = 1 - inner_xi_q * inner_xi_q

    g = lambda2 / lambda1
    epsilon = rayleigh_q / lambda1 - 1
    eta = epsilon / (g - 1)

    L = arb(m).log()

    p_mid = float(p_direct.mid())
    eta_mid = float(eta.mid())
    check_mid = p_mid <= eta_mid
    # Certified check via the arb balls themselves (rigorous interval
    # comparison), separate from the descriptive midpoint check above.
    if bool(p_direct <= eta):
        check_certified = True
    elif bool(p_direct > eta):
        check_certified = False
    else:
        check_certified = None  # balls overlap; not certified either way

    return {
        "m": m,
        "N": N,
        "dps": dps,
        "L": bounds(L),
        "L_mid": float(L.mid()),
        "lambda1": bounds(lambda1),
        "lambda2": bounds(lambda2),
        "g_lambda2_over_lambda1": bounds(g),
        "rayleigh_q": bounds(rayleigh_q),
        "epsilon": bounds(epsilon),
        "eta": bounds(eta),
        "inner_xi_q": bounds(inner_xi_q),
        "p_direct": bounds(p_direct),
        "p_mid": p_mid,
        "eta_mid": eta_mid,
        "check_p_le_eta_mid": check_mid,
        "check_p_le_eta_certified": check_certified,
        "q_norm_sq_minus_1_mid": float((q_norm_sq - 1).mid()),
        "lambda1_positive": bool(lambda1 > 0),
        "g_greater_than_1": bool(g > 1),
        "q_source": q_meta,
        "trial_available": True,
    }


def unavailable_row(m: int, N: int, dps: int, lambda1_ball: str, lambda2_ball: str, reason: str) -> dict[str, Any]:
    ctx.dps = dps + 20
    ctx.threads = 1
    lambda1 = arb(lambda1_ball)
    lambda2 = arb(lambda2_ball)
    g = lambda2 / lambda1
    L = arb(m).log()
    return {
        "m": m,
        "N": N,
        "dps": dps,
        "L": bounds(L),
        "L_mid": float(L.mid()),
        "lambda1": bounds(lambda1),
        "lambda2": bounds(lambda2),
        "g_lambda2_over_lambda1": bounds(g),
        "rayleigh_q": None,
        "epsilon": None,
        "eta": None,
        "inner_xi_q": None,
        "p_direct": None,
        "p_mid": None,
        "eta_mid": None,
        "check_p_le_eta_mid": None,
        "check_p_le_eta_certified": None,
        "q_norm_sq_minus_1_mid": None,
        "lambda1_positive": bool(lambda1 > 0),
        "g_greater_than_1": bool(g > 1),
        "q_source": None,
        "trial_available": False,
        "unavailable_reason": reason,
    }


def best_precision(cell_precisions: dict[str, Any]) -> tuple[int, dict[str, Any]]:
    dps_list = sorted(int(k) for k in cell_precisions)
    hi = dps_list[-1]
    return hi, cell_precisions[str(hi)]


def run() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    schedule = load_ledger_schedule()
    by_mn = {(row["m"], row["N"]): row for row in schedule}

    rows_out: list[dict[str, Any]] = []
    all_precisions_out: dict[str, list[dict[str, Any]]] = {}

    total = len(schedule) + 1  # +1 for the bonus (13,120) cell
    done = 0

    for row in schedule:
        m, N, role = row["m"], row["N"], row.get("role", "main_schedule")
        precisions = row["precision"]
        cell_rows = []
        for dps_str, cell in sorted(precisions.items(), key=lambda kv: int(kv[0])):
            dps = int(dps_str)
            done_msg = f"cell m={m} N={N} dps={dps} ({done+1}/{total})"
            progress(done_msg)
            if (m, N) in FAITHFUL_MN:
                q_exact, q_meta = q_projected_exact_even(m, N)
                q_even_exact = q_even_from_projected(q_exact, N)
                out = compute_columns(
                    m, N, dps,
                    cell["lambda1"]["ball"], cell["lambda2"]["ball"],
                    cell["xi1_even_basis"], q_even_exact, q_meta,
                )
            elif (m, N) in NOT_PARAMETRIZABLE_MN:
                out = unavailable_row(
                    m, N, dps, cell["lambda1"]["ball"], cell["lambda2"]["ball"],
                    reason=(
                        "TRIAL_GENERATOR_NOT_PARAMETRIZABLE: true_precision_packet_gate_v1.py's "
                        "module-level MAX_DEGREE=180 (Legendre-Galerkin truncation of the angular "
                        "prolate eigenproblem, c=2*pi*lambda_sq) is not exposed by "
                        "build_coeff_cache(lambda_sq, n_bound)'s signature and is not scaled with "
                        "lambda_sq; measured relative truncation error at this lambda_sq is "
                        f"{PARAMETRIZABILITY_CHECK['measured_relative_truncation_error_at_MAX_DEGREE_180'][m]}"
                        " -- see PARAMETRIZABILITY_CHECK in this script and the .md report."
                    ),
                )
            else:
                raise SystemExit(f"unclassified ledger cell (m={m}, N={N}); update FAITHFUL_MN/NOT_PARAMETRIZABLE_MN")
            out["role"] = role
            cell_rows.append(out)
        all_precisions_out[f"{m}_{N}"] = cell_rows
        hi_dps, hi_cell = best_precision(precisions)
        rows_out.append(next(r for r in cell_rows if r["dps"] == hi_dps))
        done += 1
    progress_done()

    # Bonus row: (m=13, N=120), the literal Phase 1 pinned object -- not
    # part of the ledger schedule, freshly built here at 120 and 240 dps
    # via edge_ledger_build.CCMArbBuilder/robust_eig (imported), for an
    # independent cross-check.
    bonus_rows = []
    q_exact_bonus, q_meta_bonus = q_projected_exact_even(BONUS_M, BONUS_N, expected_sha256=PINNED_TRIAL_SHA256)
    q_even_exact_bonus = q_even_from_projected(q_exact_bonus, BONUS_N)
    dim = BONUS_N + 1
    for dps in DPS_SCHEDULE:
        progress(f"bonus cell m={BONUS_M} N={BONUS_N} dps={dps} ({done+1}/{total})")

        def build_Q0(_m=BONUS_M, _n=BONUS_N) -> Any:
            return elb.CCMArbBuilder(_m, _n).even_block()

        started = time.time()
        lam1, lam2, vec1, _vec2, algo, bump = elb.robust_eig(build_Q0, dps, want_vectors=True)
        # robust_eig itself sets ctx.dps back to `dps` on return; the vector
        # returned is in the even basis exactly like edge_ledger_build.py's
        # own build_cell (xi1_even_basis).
        xi_even_strs = [elb.decimal_str(x) for x in vec1]
        out = compute_columns(
            BONUS_M, BONUS_N, dps,
            str(lam1), str(lam2), xi_even_strs, q_even_exact_bonus, q_meta_bonus,
        )
        out["role"] = "bonus_phase1_exact_match_not_in_ledger_schedule"
        out["eigen_algorithm"] = algo
        out["precision_bump"] = bump
        out["elapsed_seconds"] = time.time() - started
        bonus_rows.append(out)
    progress_done()
    done += 1

    payload = {
        "schema": "EdgeLedgerRelRitz.v1",
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "judge_source": str(VERDICT_PATH.relative_to(REPO)),
        "ledger_source": str(LEDGER_PATH.relative_to(REPO)),
        "builder_source": str(BUILDER_PATH.relative_to(REPO)),
        "semantic_boundary": "finite_CCM_even_sector_relative_Ritz_diagnostic_only; DIAGNOSTIC_NEVER_A_PROOF",
        "px_rh_claim": "NOT_MADE",
        "promotion": "FORBIDDEN",
        "faithful_mn": list(FAITHFUL_MN),
        "not_parametrizable_mn": list(NOT_PARAMETRIZABLE_MN),
        "parametrizability_check": PARAMETRIZABILITY_CHECK,
        "best_precision_rows": rows_out,
        "all_precisions": all_precisions_out,
        "bonus_13_120_all_precisions": bonus_rows,
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2, default=str), encoding="utf-8")

    write_report(rows_out, bonus_rows)
    print(f"\nWrote {OUT_JSON} and {OUT_MD}")


def fmt_ball_mid(ball_dict: dict[str, str] | None) -> str:
    if ball_dict is None:
        return "n/a"
    return f"{float(arb(ball_dict['ball']).mid()):.8g}"


def write_report(rows_out: list[dict[str, Any]], bonus_rows: list[dict[str, Any]]) -> None:
    lines: list[str] = []
    lines.append("# Edge ledger relative-Ritz columns (DESCRIPTIVE -- DIAGNOSTIC_NEVER_A_PROOF)")
    lines.append("")
    lines.append(f"Generated: {time.strftime('%Y-%m-%d %H:%M:%S %Z')}")
    lines.append(f"Judge source: `{VERDICT_PATH.relative_to(REPO)}` (CHEAPEST_NEXT_ACTION, section 3)")
    lines.append("")
    lines.append(
        "DESCRIPTIVE ONLY. No thresholds, no pass/fail verdicts on the physics are applied "
        "here (per the judge's explicit prohibition on post-hoc thresholds). The only boolean "
        "columns are the mathematical relation p <= eta the judge's own theorem states, computed "
        "two ways (midpoint float, and a certified arb-ball comparison), and elementary sanity "
        "checks (lambda1 > 0, g > 1) that flag a cell where the relative-Ritz denominator would "
        "be invalid. DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE."
    )
    lines.append("")
    lines.append("## Trial-generator parametrizability finding")
    lines.append("")
    lines.append(
        "The k1/g04 trial generator (`portable_k_channel_v1.build_coeff_cache`, calling "
        "`true_precision_packet_gate_v1.build_prolate_model`/`integrate_coefficients`) accepts "
        "arbitrary (lambda_sq, N) in its public signature, but "
        "`true_precision_packet_gate_v1.py`'s module-level `MAX_DEGREE = 180` (the Legendre "
        "truncation degree of the angular prolate eigenproblem) is hard-coded and not scaled "
        "with lambda_sq. Measured relative truncation error at MAX_DEGREE=180 "
        "(double-precision numpy replica of the exact same Legendre-Galerkin matrix, compared "
        "against MAX_DEGREE up to 900):"
    )
    lines.append("")
    lines.append("| lambda_sq (=m) | c = 2*pi*m | measured relative truncation error at MAX_DEGREE=180 | faithful? |")
    lines.append("|---|---|---|---|")

    for mval, err in PARAMETRIZABILITY_CHECK["measured_relative_truncation_error_at_MAX_DEGREE_180"].items():
        c_val = 2 * math.pi * mval
        faithful = "YES" if (mval, mval) in FAITHFUL_MN or any(mn[0] == mval for mn in FAITHFUL_MN) else "NO -- TRIAL_GENERATOR_NOT_PARAMETRIZABLE"
        lines.append(f"| {mval} | {c_val:.6g} | {err} | {faithful} |")
    lines.append("")
    lines.append(
        "Cells (83,83) and (163,163) are therefore reported as "
        "TRIAL_GENERATOR_NOT_PARAMETRIZABLE (columns depending on q are `null`); cells at "
        f"lambda_sq in {{13, 23, 43}} -- {', '.join(f'({m},{n})' for m, n in FAITHFUL_MN)} -- use "
        "a freshly generated trial cache from the SAME unmodified generator (no substitute "
        "construction). One bonus row, (m=13, N=120), reuses the literal SHA-256-pinned Phase 1 "
        "trial file against a freshly built (13,120) CCM matrix, as an independent cross-check "
        "outside the ledger schedule."
    )
    lines.append("")
    lines.append("## Main schedule + N-checks (best available precision per cell)")
    lines.append("")
    lines.append(
        "| m | N | role | dps | L=log(m) | lambda1 | lambda2 | g=lambda2/lambda1 | "
        "Rayleigh(q) | epsilon | eta | p=1-\\|<xi,q>\\|^2 | p<=eta (mid) | p<=eta (certified) | note |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in rows_out:
        note = "" if r["trial_available"] else r.get("unavailable_reason", "")
        lines.append(
            f"| {r['m']} | {r['N']} | {r['role']} | {r['dps']} | {r['L_mid']:.6g} | "
            f"{fmt_ball_mid(r['lambda1'])} | {fmt_ball_mid(r['lambda2'])} | "
            f"{fmt_ball_mid(r['g_lambda2_over_lambda1'])} | {fmt_ball_mid(r['rayleigh_q'])} | "
            f"{fmt_ball_mid(r['epsilon'])} | {fmt_ball_mid(r['eta'])} | {fmt_ball_mid(r['p_direct'])} | "
            f"{r['check_p_le_eta_mid']} | {r['check_p_le_eta_certified']} | {note} |"
        )
    lines.append("")
    lines.append("## Bonus row: (m=13, N=120), literal Phase 1 pinned trial, both precisions")
    lines.append("")
    lines.append(
        "| dps | L=log(13) | lambda1 | lambda2 | g | Rayleigh(q) | epsilon | eta | p | "
        "p<=eta (mid) | p<=eta (certified) | q_norm_sq-1 | eigen algo | elapsed_s |"
    )
    lines.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in bonus_rows:
        lines.append(
            f"| {r['dps']} | {r['L_mid']:.6g} | {fmt_ball_mid(r['lambda1'])} | {fmt_ball_mid(r['lambda2'])} | "
            f"{fmt_ball_mid(r['g_lambda2_over_lambda1'])} | {fmt_ball_mid(r['rayleigh_q'])} | "
            f"{fmt_ball_mid(r['epsilon'])} | {fmt_ball_mid(r['eta'])} | {fmt_ball_mid(r['p_direct'])} | "
            f"{r['check_p_le_eta_mid']} | {r['check_p_le_eta_certified']} | "
            f"{r['q_norm_sq_minus_1_mid']:.3e} | {r.get('eigen_algorithm')} | {r.get('elapsed_seconds'):.3g} |"
        )
    lines.append("")
    lines.append(
        "DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE. "
        "This report contains no interpretation beyond the columns the judge's "
        "CHEAPEST_NEXT_ACTION named."
    )
    OUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    run()


if __name__ == "__main__":
    main()
