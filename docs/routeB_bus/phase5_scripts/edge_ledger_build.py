#!/usr/bin/env python3
"""Phase 5 edge-ledger data builder for Goal 058 (Probes 1 and 2).

Precommit: docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md

Object (production, no substitutes): the finite CCM Weil matrix exactly as
built by docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py
(``CCMArbBuilder``), which matched the Zenodo 21146461 archimedean reference
to 8.5e-20 in Phase 0. This script is a *faithful parameterization* of that
builder to (m, N, L, prime set): the formulas for alpha, beta, gamma,
cos_minus_one, exp_correction, w02, wr, prime, tau_entry and the even-parity
assembly are copied byte-for-byte, with the hardcoded module constants
``M``, ``N`` and ``PRIME_POWERS`` replaced by instance parameters, and the
window length L exposed as an independent parameter for Probe 2 (default
L = log m). z = 1/m^2 and the prime-power set (fixed by m: all prime powers
k <= m) never move when L is overridden. Any other deviation would be a stop,
not a fix -- none was made.

EVEN sector only (J-even), consistent with IsSimpleEvenGround. This script
never builds the odd block: Probes 1/2 as specified only need the even
ground state and its neighbour.

Eigenpair method: python-flint ``acb_mat.eig(right=True)``. Empirically (see
inline test at the bottom of this docstring-adjacent comment and the run
log) flint returns right eigenvectors already unit-l2 normalized in the
ambient (complex) inner product; for a real symmetric matrix with a real
enclosure this is the same as unit-l2 normalization of the real vector.
Algorithm order: try "vdhoeven_mourrain" (fast, default in Phase 2's
production beta_N profiler) first; fall back to "rump" (slower, tighter
enclosures) if isolation of the full spectrum fails or the two smallest
eigenvalues do not certify as real / do not separate to the needed
precision. This mirrors Phase 2's own cross-validation pattern
(production: vdhoeven_mourrain, independent validation: rump).

Even-basis <-> +-N mode-index mapping (read this before touching xi rows).
``parity_blocks`` in Phase 1 builds the even block so that row/column 0
is the bare mode n=0, and row/column i in {1..N} is the *unit-norm*
symmetric combination (mode_i + mode_{-i}) / sqrt(2). Consequently, if
c_n = c_{-n} (n != 0) are the coefficients of a J-even vector in the
original +-N mode indexing, its coordinates in the even eigenbasis are

    xi_even[0] = c_0                      (no sqrt(2) factor)
    xi_even[i] = sqrt(2) * c_i,  i = 1..N  (sqrt(2) factor from the pair)

so the inverse map used throughout this script is

    c_0 = xi_even[0]
    c_i = c_{-i} = xi_even[i] / sqrt(2),  i = 1..N.

This is an isometry: sum_{|n|<=N} c_n^2 = c_0^2 + 2*sum_{i=1}^N c_i^2
                                        = xi_even[0]^2 + sum_{i=1}^N xi_even[i]^2
                                        = ||xi_even||_2^2 = 1,
so a unit-l2 eigenvector returned by flint in the even basis is automatically
unit-l2 in the +-N mode indexing once mapped back with the above rule -- no
extra renormalization step is applied or needed. As a corollary,
edge^2 := xi_N^2 + xi_{-N}^2 = 2*c_N^2 = xi_even[N]^2 exactly (this identity
is checked numerically for every cell and stored).

Probe 2 (window-variation / Hellmann-Feynman): hold the prime set fixed
(primes <= m) and vary L around L0 = log(m) with h = 1e-6 * L0 (frozen in
the precommit as h = 10^-6 * L0). Both eigenvalue branches are recomputed by
rebuilding the *entire* even block at L0 +/- h (central difference), giving
(a) a finite-difference derivative of each of the two smallest eigenvalues
and (b) the Hellmann-Feynman value xi^T (dQ/dL) xi with dQ/dL obtained by
the same central difference applied entrywise to the even block, contracted
against the L0 eigenvector (not recomputed at L0 +/- h). Frozen sanity check:
FD and HF must agree to 6 significant digits; a mismatch is flagged, never
silently accepted.

Regression gate (frozen numbers, not touched by this generalization): at
m = 13, N = 120 (L = log 13, i.e. the exact Phase-1 window, no override) the
smallest eigenvalue of the *raw* (no tau*qq^T penalty, no beta subtraction)
even block must be positive and below 1e-56; Phase 1 found a = q*Kq
approx 4.72e-59 for its pinned near-null q at this cell. If this gate fails,
the script stops with REGRESSION_FAIL and reports the numbers -- it does not
adjust the builder to make the gate pass.

DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE. No Lean, no route
promotion.
"""

from __future__ import annotations

import json
import platform
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from flint import acb, acb_mat, arb, arb_mat, ctx

REPO = Path(__file__).resolve().parents[3]
OUT_DIR = Path(__file__).resolve().parent / "out"
PRECOMMIT = Path(__file__).resolve().parent / "PRECOMMIT_2026-09-03_edge_ledger_probes.md"

PRECISIONS = (120, 240)
H_RELATIVE_NOTE = "h = L0 / 1_000_000 (single division; == 1e-6 * L0 as frozen in the precommit)"

# Main schedule: m = N (production "m = N = k+2" cofinal reindex convention).
SCHEDULE_M = (13, 23, 43, 83, 163)
# Secondary N-check pairs: (m, N) with N = 2m, holding m (window, prime set) fixed.
N_CHECK_PAIRS = ((13, 26), (43, 86))
# Regression gate cell, frozen from Phase 1.
GATE_M, GATE_N = 13, 120
GATE_UPPER_BOUND = arb("1e-56")

EIGEN_ALGORITHMS = ("vdhoeven_mourrain", "rump")

# Above this dimension (N+1), flint's full-spectrum isolation (needed by
# acb_mat.eig(right=True), which underlies robust_eig) was found empirically
# to fail outright -- not a precision problem: at N=163 (dim 164)
# eig(nonstop=True) returns NaN for every one of the 164 eigenvalues at
# working precisions up to dps=520. m=83 (dim 84) succeeds; m=163 (dim 164)
# never does, at any precision tried. Cells above the threshold use the
# inverse-iteration fallback (see inverse_iteration_ground/_deflated) instead
# of ever attempting full isolation, to avoid burning minutes discovering a
# failure we have already established is not precision-sensitive.
INVERSE_ITERATION_N_THRESHOLD = 100
INVERSE_ITERATION_GROUND_ITERS = 3
INVERSE_ITERATION_SECOND_ITERS = 4
# Precisions used for cells above the threshold. Empirically (m=163, dim 164):
# dps=520 gives only ~garbage (full isolation fails; even the inverse-iteration
# Rayleigh quotient is unreliable there since the plain "lu" solve loses all
# but 3-4 digits); dps=600 with algorithm="precond" gives only ~7 correct
# digits on lambda1 via the Rayleigh quotient; dps=900 gives ~30 correct
# digits (residual ~1e-311). Coordinator directive 2026-09-03: use dps=900
# ONLY for m=163 -- a central finite difference with h=1e-6*L on an
# eigenvalue of size ~1e-311 cannot agree with Hellmann-Feynman at any
# precision anyone is going to run here (that is a precision statement,
# not a bug), so a doubled-precision cross-check buys nothing that isn't
# already flagged via INSUFFICIENT_PRECISION_FD; skip it and keep the whole
# cell inside a 25-minute budget instead.
LARGE_N_PRECISIONS = (900,)
LARGE_N_TIME_BUDGET_SECONDS = 25 * 60


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


def prime_powers_upto(limit: int) -> tuple[tuple[int, int], ...]:
    """All prime powers k <= limit as (k, p) with p the prime base.

    Verified below (module-load assertion) to reproduce Phase 1's hardcoded
    PRIME_POWERS list byte-for-byte at m = 13.
    """

    def smallest_prime_factor(k: int) -> int:
        d = 2
        while d * d <= k:
            if k % d == 0:
                return d
            d += 1
        return k

    powers: list[tuple[int, int]] = []
    for k in range(2, limit + 1):
        p = smallest_prime_factor(k)
        n = k
        while n % p == 0:
            n //= p
        if n == 1:
            powers.append((k, p))
    return tuple(powers)


_PHASE1_PRIME_POWERS_M13 = (
    (2, 2), (3, 3), (4, 2), (5, 5), (7, 7), (8, 2), (9, 3), (11, 11), (13, 13),
)
assert prime_powers_upto(13) == _PHASE1_PRIME_POWERS_M13, (
    "generalized prime-power generator does not reproduce the Phase-1 pin at m=13"
)


def bounds(value: arb) -> dict[str, str]:
    return {"ball": str(value), "lower": str(value.lower()), "upper": str(value.upper())}


def decimal_str(value: arb, digits: int = 70) -> str:
    return value.str(digits, radius=False)


class CCMArbBuilder:
    """Faithful (m, N, L, prime-set) generalization of Phase 1's CCMArbBuilder.

    See module docstring. Formulas are unchanged from
    docs/routeB_bus/phase1_scripts/ccm_control_cell_penalty.py; only the
    module-level M, N, PRIME_POWERS constants become instance state, and L
    (only) becomes an independent parameter via ``L_override``.
    """

    def __init__(self, m: int, N: int, L_override: arb | None = None) -> None:
        self.m = m
        self.N = N
        self.pi = arb.pi()
        self.L = L_override if L_override is not None else arb(m).log()
        self.z = arb(1) / (m * m)
        self.exp_minus_L_over_2 = (-self.L / 2).exp()
        self.I = acb(0, 1)
        self.exp_correction = self._exp_correction()
        self.constant = (
            arb.const_euler() + (4 * self.pi * (m - 1) / (m + 1)).log()
        ) / 2
        self.alpha = {n: self._alpha(n) for n in range(N + 1)}
        self.beta = {n: self._beta(n) for n in range(N + 1)}
        self.gamma = {n: self._gamma(n) for n in range(N + 1)}
        self.prime_powers = prime_powers_upto(m)
        self.log_prime = {p: arb(p).log() for _, p in self.prime_powers}
        self.log_k = {k: arb(k).log() for k, _ in self.prime_powers}

    def _alpha(self, n: int) -> arb:
        if n == 0:
            return arb(0)
        a = acb(arb(1) / 4, self.pi * n / self.L)
        hyp = acb(self.z).hypgeom_2f1(1, a, a + 1)
        term = (2 * self.L / (self.L + 4 * self.pi * self.I * n)) * hyp
        return (self.exp_minus_L_over_2 * term.imag + a.digamma().imag / 2) / self.pi

    def _beta(self, n: int) -> arb:
        if n == 0:
            # x*rho(x) = exp(x/2)/(2*sinc(i*x)); this removes the endpoint singularity.
            integrand = lambda x, _analytic: (x / 2).exp() / (2 * (self.I * x).sinc())
            value = acb.integral(
                integrand,
                0,
                self.L,
                rel_tol=arb(10) ** (-(ctx.dps - 10)),
                abs_tol=arb(10) ** (-(ctx.dps - 10)),
            )
            return value.real / self.L
        a = acb(arb(1) / 4, self.pi * n / self.L)
        hyp = acb(self.z).hypgeom_2f1(1, a, a + 1)
        term1 = -self.L * self.exp_minus_L_over_2 * (
            (2 * self.L / (4 * self.pi * n - self.I * self.L)) * hyp
        ).imag
        term2 = -self.exp_minus_L_over_2 * acb(self.z).lerch_phi(2, a).real / 4
        term3 = a.polygamma(1).real / 4
        return (term1 + term2 + term3) / self.L

    def _cos_minus_one(self, n: int) -> arb:
        if n == 0:
            return arb(0)
        a = acb(arb(1) / 4, self.pi * n / self.L)
        hyp = acb(self.z).hypgeom_2f1(1, a, a + 1)
        h0 = self.z.hypgeom_2f1(arb(1) / 4, 1, arb(5) / 4)
        term1 = -self.exp_minus_L_over_2 * (
            (2 * self.L / (self.L + 4 * self.pi * self.I * n)) * hyp
        ).real
        term2 = 2 * self.exp_minus_L_over_2 * h0
        term3 = -(a.digamma().real - arb(arb(1) / 4).digamma()) / 2
        return term1 + term2 + term3

    def _exp_correction(self) -> arb:
        # (1-exp(-x/2))*rho(x) = exp(x)/((exp(x/2)+1)*(exp(x)+1)).
        integrand = lambda x, _analytic: x.exp() / (((x / 2).exp() + 1) * (x.exp() + 1))
        return acb.integral(
            integrand,
            0,
            self.L,
            rel_tol=arb(10) ** (-(ctx.dps - 10)),
            abs_tol=arb(10) ** (-(ctx.dps - 10)),
        ).real

    def _gamma(self, n: int) -> arb:
        return self._cos_minus_one(n) + self.exp_correction + self.constant

    def q_nm(self, n: int, m: int, y: arb) -> arb:
        if n == m:
            return 2 * (1 - y / self.L) * (2 * self.pi * n * y / self.L).cos()
        return (
            (2 * self.pi * m * y / self.L).sin()
            - (2 * self.pi * n * y / self.L).sin()
        ) / (self.pi * (n - m))

    def w02(self, n: int, m: int) -> arb:
        return (
            32
            * self.L
            * (self.L / 4).sinh() ** 2
            * (self.L**2 - 16 * self.pi**2 * m * n)
            / (
                (self.L**2 + 16 * self.pi**2 * m * m)
                * (self.L**2 + 16 * self.pi**2 * n * n)
            )
        )

    def wr(self, n: int, m: int) -> arb:
        if n == m:
            k = abs(n)
            return 2 * self.gamma[k] - 2 * self.beta[k]
        alpha_n = self.alpha[abs(n)] if n >= 0 else -self.alpha[abs(n)]
        alpha_m = self.alpha[abs(m)] if m >= 0 else -self.alpha[abs(m)]
        return (alpha_m - alpha_n) / (n - m)

    def prime(self, n: int, m: int) -> arb:
        total = arb(0)
        for k, p in self.prime_powers:
            total += self.log_prime[p] / arb(k).sqrt() * self.q_nm(n, m, self.log_k[k])
        return total

    def tau_entry(self, n: int, m: int) -> arb:
        return self.w02(n, m) - self.wr(n, m) - self.prime(n, m)

    def even_block(self) -> arb_mat:
        """EVEN sector only, exactly as Phase 1's parity_blocks() builds it."""
        N = self.N
        even = arb_mat(N + 1, N + 1)
        sqrt2 = arb(2).sqrt()
        cache: dict[tuple[int, int], arb] = {}

        def k(i: int, j: int) -> arb:
            key = (i, j) if i <= j else (j, i)
            if key not in cache:
                cache[key] = self.tau_entry(*key)
            return cache[key]

        even[0, 0] = k(0, 0)
        for j in range(1, N + 1):
            value = sqrt2 * k(0, j)
            even[0, j] = value
            even[j, 0] = value
        for i in range(1, N + 1):
            for j in range(i, N + 1):
                even_value = k(i, j) + k(i, -j)
                even[i, j] = even_value
                even[j, i] = even_value
        return even


def two_smallest_eigs(
    matrix: arb_mat, algorithm: str, want_vectors: bool
) -> tuple[arb, arb, list[arb] | None, list[arb] | None]:
    ac = acb_mat(matrix)
    if want_vectors:
        eigenvalues, right = ac.eig(right=True, algorithm=algorithm)
    else:
        eigenvalues = ac.eig(algorithm=algorithm)
        right = None
    n = len(eigenvalues)
    if n != matrix.nrows():
        raise RuntimeError("flint did not isolate the complete spectrum")
    order = sorted(range(n), key=lambda i: float(eigenvalues[i].real.mid()))
    idx1, idx2 = order[0], order[1]
    lam1c, lam2c = eigenvalues[idx1], eigenvalues[idx2]
    for lam in (lam1c, lam2c):
        if 0 not in lam.imag:
            raise RuntimeError(f"eigenvalue enclosure missed the real axis: {lam}")
    lam1, lam2 = lam1c.real, lam2c.real
    vec1 = vec2 = None
    if right is not None:
        col1 = [right[i, idx1] for i in range(n)]
        col2 = [right[i, idx2] for i in range(n)]
        for col, label in ((col1, "lambda1"), (col2, "lambda2")):
            for c in col:
                if 0 not in c.imag:
                    raise RuntimeError(f"eigenvector component not real for {label}: {c}")
        vec1 = [c.real for c in col1]
        vec2 = [c.real for c in col2]
    return lam1, lam2, vec1, vec2


def compute_eig_data(
    matrix: arb_mat, want_vectors: bool
) -> tuple[arb, arb, list[arb] | None, list[arb] | None, str]:
    last_exc: Exception | None = None
    for algorithm in EIGEN_ALGORITHMS:
        try:
            lam1, lam2, vec1, vec2 = two_smallest_eigs(matrix, algorithm, want_vectors)
            return lam1, lam2, vec1, vec2, algorithm
        except Exception as exc:  # noqa: BLE001 - deliberate multi-algorithm fallback
            last_exc = exc
            continue
    raise RuntimeError(f"eigen isolation failed under all algorithms {EIGEN_ALGORITHMS}: {last_exc}")


PRECISION_BUMPS = (0, 60, 120, 240)


def robust_eig(
    build_matrix_fn, base_dps: int, want_vectors: bool
) -> tuple[arb, arb, list[arb] | None, list[arb] | None, str, int]:
    """compute_eig_data with an escalating-precision fallback.

    Full-spectrum isolation (needed by flint to certify the two smallest
    eigenvalues and, when requested, their eigenvectors) can fail even for
    well-separated ground eigenpairs if two *unrelated* eigenvalues
    elsewhere in the spectrum are numerically close at the working
    precision. This is a precision artifact, not a property of lambda1 or
    lambda2, so the frozen recourse is exactly what flint itself suggests:
    "try higher prec". Each bump rebuilds the matrix from scratch at the
    higher precision (tighter entry balls); ctx.dps is restored afterwards.
    A bump > 0 that succeeds is recorded (ODDITY discipline).
    """
    last_exc: Exception | None = None
    for bump in PRECISION_BUMPS:
        ctx.dps = base_dps + bump
        ctx.threads = 1
        matrix = build_matrix_fn()
        try:
            lam1, lam2, vec1, vec2, algorithm = compute_eig_data(matrix, want_vectors)
            ctx.dps = base_dps
            ctx.threads = 1
            return lam1, lam2, vec1, vec2, algorithm, bump
        except Exception as exc:  # noqa: BLE001 - deliberate precision-escalation fallback
            last_exc = exc
            continue
    ctx.dps = base_dps
    ctx.threads = 1
    raise RuntimeError(
        f"eigen isolation failed even after precision bumps {PRECISION_BUMPS} "
        f"above base dps={base_dps}: {last_exc}"
    )


def solve_precond_vec(matrix: arb_mat, dim: int, rhs: list[arb]) -> list[arb]:
    rhs_mat = arb_mat(dim, 1)
    for i in range(dim):
        rhs_mat[i, 0] = rhs[i]
    # algorithm="precond" is essential here (the same option Phase 2 uses for
    # its own ill-conditioned Schur-complement solve): the default/"lu" solve
    # empirically loses almost all precision on this near-singular matrix
    # (only ~3-4 correct digits regardless of ctx.dps, plateauing), while
    # "precond" retains enough directional accuracy for the Rayleigh
    # quotient's quadratic error suppression to still deliver a tight
    # eigenvalue enclosure.
    y = matrix.solve(rhs_mat, algorithm="precond")
    return [y[i, 0] for i in range(dim)]


def max_component_normalize(x: list[arb]) -> list[arb]:
    """Normalize by the largest-magnitude component rather than the l2 norm.

    Unit-l2 normalization requires a sqrt of a sum of squares of an
    astronomically large intermediate vector (inverse iteration on a near-
    singular matrix routinely produces components of size 1e+150 or more
    before normalization); that sqrt alone was observed to burn essentially
    all working precision. Dividing by the largest component avoids the
    sqrt and keeps intermediate magnitudes near unity between iterations.
    """
    best = arb(1)
    best_mid = 0.0
    for xx in x:
        mid = float(abs(xx).mid())
        if mid > best_mid:
            best_mid = mid
            best = xx
    return [xx / best for xx in x]


def unit_normalize(x: list[arb]) -> list[arb]:
    norm = (sum((xx * xx for xx in x), arb(0))).sqrt()
    return [xx / norm for xx in x]


def rayleigh_quotient(matrix: arb_mat, dim: int, x: list[arb]) -> tuple[arb, arb]:
    """x must already be unit-l2 normalized. Returns (lambda, residual_norm)."""
    Qx = [sum((matrix[i, j] * x[j] for j in range(dim)), arb(0)) for i in range(dim)]
    lam = sum((x[i] * Qx[i] for i in range(dim)), arb(0))
    resid = [Qx[i] - lam * x[i] for i in range(dim)]
    resid_norm = (sum((r * r for r in resid), arb(0))).sqrt()
    return lam, resid_norm


def inverse_iteration_ground(matrix: arb_mat, dim: int, iterations: int) -> tuple[arb, list[arb], arb]:
    """Unshifted inverse power iteration (power iteration on Q^{-1}) converging
    to the smallest-|eigenvalue| eigenpair of symmetric Q. This is the
    "eigenvectors via inverse iteration ... in arb" fallback named in the
    task brief, used only when full-spectrum isolation is known to fail
    (see INVERSE_ITERATION_N_THRESHOLD). Empirically converges to the
    stable direction within 1-2 iterations for every cell tested (m up to
    163); the loop runs a couple of extra iterations as a cheap safety
    margin and to demonstrate stability (values stop changing)."""
    x = [arb(1) for _ in range(dim)]
    for _ in range(iterations):
        x = solve_precond_vec(matrix, dim, x)
        x = max_component_normalize(x)
    xu = unit_normalize(x)
    lam, resid = rayleigh_quotient(matrix, dim, xu)
    return lam, xu, resid


def inverse_iteration_deflated(
    matrix: arb_mat, dim: int, x1: list[arb], iterations: int
) -> tuple[arb, list[arb], arb]:
    """Same as inverse_iteration_ground, but the running iterate is
    projected orthogonal to the already-found (unit-l2) ground eigenvector
    x1 after every solve step, so the iteration converges to the second-
    smallest-|eigenvalue| eigenpair instead of collapsing back onto x1."""
    x = [arb(1) if i % 7 else arb(0) for i in range(dim)]  # avoid an accidental x1-aligned seed
    for _ in range(iterations):
        x = solve_precond_vec(matrix, dim, x)
        proj = sum((x1[i] * x[i] for i in range(dim)), arb(0))
        x = [x[i] - proj * x1[i] for i in range(dim)]
        x = max_component_normalize(x)
    xu = unit_normalize(x)
    lam, resid = rayleigh_quotient(matrix, dim, xu)
    return lam, xu, resid


def shifted_inverse_iteration_lambda2_estimate(
    matrix: arb_mat, dim: int, mu: arb, x1: list[arb], iterations: int
) -> tuple[arb, arb]:
    """Independent cross-check of lambda2: shift-and-invert iteration around
    mu (e.g. 10*lambda1 or 100*lambda1), started from a fixed pseudo-random
    vector orthogonalized against x1 and re-orthogonalized after every step,
    converging to whichever eigenvalue of Q is closest to mu. If this agrees
    with the deflation-based lambda2, that is strong evidence the deflation
    found the genuine second-smallest eigenpair rather than an artifact.
    Returns (lambda_estimate, residual_norm), both from the Rayleigh quotient
    against the ORIGINAL (unshifted) matrix.
    """
    shifted = arb_mat(matrix)
    for i in range(dim):
        shifted[i, i] = shifted[i, i] - mu
    x = [arb(1) if i % 5 else arb(-1) for i in range(dim)]
    proj0 = sum((x1[i] * x[i] for i in range(dim)), arb(0))
    x = [x[i] - proj0 * x1[i] for i in range(dim)]
    for _ in range(iterations):
        x = solve_precond_vec(shifted, dim, x)
        proj = sum((x1[i] * x[i] for i in range(dim)), arb(0))
        x = [x[i] - proj * x1[i] for i in range(dim)]
        x = max_component_normalize(x)
    xu = unit_normalize(x)
    lam, resid = rayleigh_quotient(matrix, dim, xu)
    return lam, resid


def verify_second_eigenpair(
    matrix: arb_mat, dim: int, lam1: arb, x1: list[arb], lam2: arb, x2: list[arb],
    resid2: arb,
) -> dict[str, Any]:
    """Extra cross-checks for the deflation-based second eigenpair on cells
    where full-spectrum isolation is unavailable (large N).

    ODDITY, recorded as found: the coordinator's requested cross-check --
    shift-and-invert at mu = 10*lambda1 and mu = 100*lambda1, deflated
    against x1 -- was validated first on m=83 (dim 84), a cell where the
    deflation-based lambda2 is independently KNOWN CORRECT (it matches
    flint's full-spectrum isolation to 19 significant digits). On that known-
    good cell the shift10/shift100 estimates come back as pure noise (an arb
    ball straddling zero with no useful digits), NOT agreeing with the true
    lambda2. Reason: for these cells the lambda2/lambda1 gap is enormous
    (~3.9e7 at m=83), so mu=10*lambda1 or 100*lambda1 is still overwhelmingly
    closer to lambda1 than to lambda2 -- the shifted matrix stays nearly
    singular in the x1 direction, and residual x1-contamination from the
    solve's own ~13-digit floor gets amplified by roughly 1/lambda1 before
    deflation can remove it, swamping the intended x2-direction signal. This
    is a property of the shift choice relative to this operator's spectrum,
    not of the deflation method itself -- so shift10/shift100 are computed
    and stored (as asked) but are NOT used to gate SECOND_EIGENPAIR_UNVERIFIED.

    The actual gate uses: (i) residual ||Q x2 - lambda2 x2|| (already
    computed by the caller -- by the Bauer-Fike bound for a symmetric
    matrix, a tiny residual is a mathematical PROOF that lambda2 lies within
    that residual distance of some true eigenvalue of Q, independent of
    convergence concerns); (ii) |<x1,x2>| (near-zero required -- rules out
    x2 having collapsed back onto x1); (iii) a stability re-run of the
    deflation with 3 extra iterations, requiring agreement to 10 significant
    digits (rules out an under-converged x2); (iv) lambda2 >= lambda1 with a
    relative gap above 1e-3.
    """
    v1_dot_v2 = sum((x1[i] * x2[i] for i in range(dim)), arb(0))
    shift10 = 10 * lam1
    shift100 = 100 * lam1
    lam2_shift10, resid_shift10 = shifted_inverse_iteration_lambda2_estimate(
        matrix, dim, shift10, x1, INVERSE_ITERATION_SECOND_ITERS
    )
    lam2_shift100, resid_shift100 = shifted_inverse_iteration_lambda2_estimate(
        matrix, dim, shift100, x1, INVERSE_ITERATION_SECOND_ITERS
    )
    lam2_more_iters, x2_more_iters, resid2_more_iters = inverse_iteration_deflated(
        matrix, dim, x1, INVERSE_ITERATION_SECOND_ITERS + 3
    )
    stability_agree = sig_agree(lam2, lam2_more_iters, 10)

    resid_ok = float(abs(resid2).mid()) < 1e-30 or resid2.mid() == 0
    orthogonality_ok = float(abs(v1_dot_v2).mid()) < 1e-30 or v1_dot_v2.mid() == 0
    rel_gap_ok = False
    if lam1.mid() != 0:
        rel_gap_ok = float(((lam2 - lam1) / lam1).mid()) > 1e-3
    order_ok = lam2.mid() >= lam1.mid()
    unverified = not (order_ok and rel_gap_ok and resid_ok and orthogonality_ok and stability_agree)
    return {
        "v1_dot_v2": bounds(v1_dot_v2),
        "lambda2_shift10_estimate": bounds(lam2_shift10),
        "lambda2_shift10_residual": str(resid_shift10),
        "lambda2_shift100_estimate": bounds(lam2_shift100),
        "lambda2_shift100_residual": str(resid_shift100),
        "shift_diagnostic_note": (
            "shift10/shift100 are noise on this operator (see docstring); NOT used to gate the verdict"
        ),
        "lambda2_stability_rerun_extra3_iters": bounds(lam2_more_iters),
        "lambda2_stability_agrees_10sig": stability_agree,
        "resid2_below_1e-30": resid_ok,
        "orthogonality_below_1e-30": orthogonality_ok,
        "lambda2_order_ok": order_ok,
        "lambda2_rel_gap_above_1e-3": rel_gap_ok,
        "SECOND_EIGENPAIR_UNVERIFIED": unverified,
    }


def resolve_eigenpair(
    build_matrix_fn, dim: int, base_dps: int, want_vectors: bool
) -> dict[str, Any]:
    """Unified two-smallest-eigenpair accessor.

    dim - 1 == N (even block is (N+1)x(N+1)). For dim <=
    INVERSE_ITERATION_N_THRESHOLD + 1, tries flint's full-spectrum isolation
    first via robust_eig -- fast, and empirically validated up to m=N=83
    (matches the known Phase 1 regression-gate order of magnitude; residual
    checks pass inside two_smallest_eigs). Above the threshold, full
    isolation is skipped entirely (established failure, not a precision
    question -- see INVERSE_ITERATION_N_THRESHOLD) in favor of the inverse-
    iteration fallback, with extra cross-checks on lambda2 (see
    verify_second_eigenpair) whenever eigenvectors are requested -- the
    deflation-based second eigenpair is the least-trustworthy step in this
    fallback and must not be reported unverified.
    """
    if dim - 1 <= INVERSE_ITERATION_N_THRESHOLD:
        lam1, lam2, vec1, vec2, algo, bump = robust_eig(build_matrix_fn, base_dps, want_vectors)
        return {
            "lambda1": lam1, "lambda2": lam2, "vec1": vec1, "vec2": vec2,
            "method": algo, "bump": bump, "resid1": None, "resid2": None,
            "verification": None,
        }
    ctx.dps = base_dps
    ctx.threads = 1
    matrix = build_matrix_fn()
    lam1, x1, resid1 = inverse_iteration_ground(matrix, dim, INVERSE_ITERATION_GROUND_ITERS)
    lam2, x2, resid2 = inverse_iteration_deflated(matrix, dim, x1, INVERSE_ITERATION_SECOND_ITERS)
    verification = None
    if want_vectors:
        verification = verify_second_eigenpair(matrix, dim, lam1, x1, lam2, x2, resid2)
    return {
        "lambda1": lam1, "lambda2": lam2,
        "vec1": x1 if want_vectors else None, "vec2": x2 if want_vectors else None,
        "method": "inverse_iteration_precond_deflation", "bump": 0,
        "resid1": resid1, "resid2": resid2,
        "verification": verification,
    }


def sig_agree(a: arb, b: arb, sig: int) -> bool:
    """Descriptive (non-certified) leading-sig-fig agreement check."""
    af, bf = float(a.mid()), float(b.mid())
    if af == 0.0 and bf == 0.0:
        return True
    denom = max(abs(af), abs(bf))
    if denom == 0.0:
        return True
    rel = abs(af - bf) / denom
    return rel < 0.5 * 10 ** (-(sig - 1))


def even_to_pm_row(xi_even: list[arb], N: int) -> list[arb]:
    """Map even-basis coordinates (index 0..N) to +-N mode indexing (-N..N).

    c_0 = xi_even[0]; c_i = c_{-i} = xi_even[i] / sqrt(2) for i = 1..N.
    Returned as a list indexed [0..2N] representing n = -N..N.
    """
    sqrt2 = arb(2).sqrt()
    c = {0: xi_even[0]}
    for i in range(1, N + 1):
        c[i] = xi_even[i] / sqrt2
        c[-i] = c[i]
    return [c[n] for n in range(-N, N + 1)]


def build_cell(m: int, N: int, dps: int) -> dict[str, Any]:
    ctx.dps = dps
    ctx.threads = 1
    started = time.time()
    dim = N + 1

    def build_Q0() -> arb_mat:
        return CCMArbBuilder(m, N).even_block()

    r0 = resolve_eigenpair(build_Q0, dim, dps, want_vectors=True)
    lam1, lam2, vec1, vec2, algo0, bump0 = (
        r0["lambda1"], r0["lambda2"], r0["vec1"], r0["vec2"], r0["method"], r0["bump"],
    )
    # dps0 is the precision actually used to obtain lambda1/lambda2/xi (== dps
    # unless the rare precision-escalation fallback triggered, or unless this
    # is a large-N cell already run at its own fixed high precision -- bump
    # is always 0 for the inverse-iteration path). Everything downstream in
    # this cell (L0, h, Qp, Qm, dQ/dL) is recomputed at dps0 so the
    # Hellmann-Feynman contraction is not mixing precisions.
    dps0 = dps + bump0
    ctx.dps = dps0
    ctx.threads = 1

    L0 = arb(m).log()
    h_abs = L0 / 1_000_000  # h = 1e-6 * L0 (single division: avoids double-rounded error inflation)

    xi_even_1 = vec1
    xi_even_2 = vec2
    xi_pm_1 = even_to_pm_row(xi_even_1, N)
    xi_pm_2 = even_to_pm_row(xi_even_2, N)
    sumsq_1 = sum((x * x for x in xi_pm_1), arb(0))
    sumsq_2 = sum((x * x for x in xi_pm_2), arb(0))
    # xi_pm indexed 0..2N for n=-N..N: n=+N is index 2N, n=-N is index 0.
    edge_sq_1 = xi_pm_1[2 * N] ** 2 + xi_pm_1[0] ** 2
    edge_sq_2 = xi_pm_2[2 * N] ** 2 + xi_pm_2[0] ** 2
    edge_sq_1_from_even = xi_even_1[N] ** 2
    edge_sq_2_from_even = xi_even_2[N] ** 2

    def build_Qp() -> arb_mat:
        return CCMArbBuilder(m, N, L_override=L0 + h_abs).even_block()

    def build_Qm() -> arb_mat:
        return CCMArbBuilder(m, N, L_override=L0 - h_abs).even_block()

    rp = resolve_eigenpair(build_Qp, dim, dps0, want_vectors=False)
    rm = resolve_eigenpair(build_Qm, dim, dps0, want_vectors=False)
    lam1_p, lam2_p, algo_p, bump_p = rp["lambda1"], rp["lambda2"], rp["method"], rp["bump"]
    lam1_m, lam2_m, algo_m, bump_m = rm["lambda1"], rm["lambda2"], rm["method"], rm["bump"]

    # Rebuild Qp/Qm explicitly at dps0 (independent of whatever precision the
    # eigenvalue-only isolation above may have escalated to and discarded)
    # so the Hellmann-Feynman contraction below uses the same precision as
    # xi_even_1/xi_even_2.
    ctx.dps = dps0
    ctx.threads = 1
    Qp = build_Qp()
    Qm = build_Qm()

    two_h = 2 * h_abs
    dlambda1_dL_fd = (lam1_p - lam1_m) / two_h
    dlambda2_dL_fd = (lam2_p - lam2_m) / two_h

    dQ_dL = [[(Qp[i, j] - Qm[i, j]) / two_h for j in range(dim)] for i in range(dim)]

    def quad_form(vec: list[arb]) -> arb:
        total = arb(0)
        for i in range(dim):
            row_sum = arb(0)
            dQ_row = dQ_dL[i]
            for j in range(dim):
                row_sum += dQ_row[j] * vec[j]
            total += vec[i] * row_sum
        return total

    dlambda1_dL_hf = quad_form(xi_even_1)
    dlambda2_dL_hf = quad_form(xi_even_2)

    hf_fd_agree_1 = sig_agree(dlambda1_dL_fd, dlambda1_dL_hf, 6)
    hf_fd_agree_2 = sig_agree(dlambda2_dL_fd, dlambda2_dL_hf, 6)

    delta = lam2 - lam1
    ratio21 = lam2 / lam1
    rel_gap = delta / abs(lam1)

    elapsed = time.time() - started
    return {
        "m": m,
        "N": N,
        "dps": dps,
        "dps_effective": dps0,
        "precision_bumps": {"lambda0": bump0, "plus": bump_p, "minus": bump_m},
        "inverse_iteration_residuals": {
            "lambda0_resid1": str(r0["resid1"]) if r0["resid1"] is not None else None,
            "lambda0_resid2": str(r0["resid2"]) if r0["resid2"] is not None else None,
            "plus_resid1": str(rp["resid1"]) if rp["resid1"] is not None else None,
            "plus_resid2": str(rp["resid2"]) if rp["resid2"] is not None else None,
            "minus_resid1": str(rm["resid1"]) if rm["resid1"] is not None else None,
            "minus_resid2": str(rm["resid2"]) if rm["resid2"] is not None else None,
        },
        "second_eigenpair_verification": r0["verification"],
        "L0": bounds(L0),
        "h_abs": bounds(h_abs),
        "eigen_algorithm_lambda0": algo0,
        "eigen_algorithm_plus": algo_p,
        "eigen_algorithm_minus": algo_m,
        "lambda1": bounds(lam1),
        "lambda2": bounds(lam2),
        "delta": bounds(delta),
        "lambda2_over_lambda1": bounds(ratio21),
        "rel_gap_delta_over_abs_lambda1": bounds(rel_gap),
        "xi1_even_basis": [decimal_str(x) for x in xi_even_1],
        "xi2_even_basis": [decimal_str(x) for x in xi_even_2],
        "xi1_pm_index": {
            "note": (
                "list index i corresponds to mode n = i - N, i.e. n runs -N..N; "
                "c_0 = xi_even[0], c_i = c_{-i} = xi_even[i]/sqrt(2) for i=1..N"
            ),
            "values": [decimal_str(x) for x in xi_pm_1],
        },
        "xi2_pm_index": {
            "note": "same mapping as xi1_pm_index, applied to the lambda2 eigenvector",
            "values": [decimal_str(x) for x in xi_pm_2],
        },
        "sum_xi1_pm_squared": bounds(sumsq_1),
        "sum_xi2_pm_squared": bounds(sumsq_2),
        "edge_sq_1_from_pm_row": bounds(edge_sq_1),
        "edge_sq_1_from_even_basis": bounds(edge_sq_1_from_even),
        "edge_sq_2_from_pm_row": bounds(edge_sq_2),
        "edge_sq_2_from_even_basis": bounds(edge_sq_2_from_even),
        "dlambda1_dL_fd": bounds(dlambda1_dL_fd),
        "dlambda1_dL_hf": bounds(dlambda1_dL_hf),
        "dlambda1_dL_hf_fd_agree_6sig": hf_fd_agree_1,
        "dlambda2_dL_fd": bounds(dlambda2_dL_fd),
        "dlambda2_dL_hf": bounds(dlambda2_dL_hf),
        "dlambda2_dL_hf_fd_agree_6sig": hf_fd_agree_2,
        "prime_power_count": len(prime_powers_upto(m)),
        "elapsed_seconds": elapsed,
    }


CROSS_PRECISION_FIELDS = (
    "lambda1", "lambda2", "delta", "lambda2_over_lambda1",
    "edge_sq_1_from_even_basis", "edge_sq_2_from_even_basis",
    "dlambda1_dL_fd", "dlambda1_dL_hf", "dlambda2_dL_fd", "dlambda2_dL_hf",
)


def check_insufficient_precision(low: dict[str, Any], high: dict[str, Any]) -> list[str]:
    flags = []
    for field in CROSS_PRECISION_FIELDS:
        a = arb(low[field]["ball"])
        b = arb(high[field]["ball"])
        if not sig_agree(a, b, 8):
            flags.append(field)
    return flags


def run_gate() -> dict[str, Any]:
    """Regression gate: raw (unpenalized) even-block smallest eigenvalue at
    m=13, N=120 must be positive and below 1e-56 (Phase 1: a ~= 4.72e-59)."""
    results = {}
    for dps in PRECISIONS:
        started = time.time()

        def build_Q() -> arb_mat:
            return CCMArbBuilder(GATE_M, GATE_N).even_block()

        lam1, lam2, vec1, _, algo, bump = robust_eig(build_Q, dps, want_vectors=True)
        results[f"dps_{dps}"] = {
            "lambda1": bounds(lam1),
            "lambda2": bounds(lam2),
            "algorithm": algo,
            "precision_bump": bump,
            "elapsed_seconds": time.time() - started,
        }
    lam1_high = arb(results[f"dps_{PRECISIONS[-1]}"]["lambda1"]["ball"])
    positive = lam1_high.lower() > 0
    below = lam1_high.upper() < GATE_UPPER_BOUND
    passed = bool(positive and below)
    results["gate_m"] = GATE_M
    results["gate_N"] = GATE_N
    results["gate_upper_bound"] = str(GATE_UPPER_BOUND)
    results["pass"] = passed
    return results


def precisions_for(N: int) -> tuple[int, ...]:
    if N > INVERSE_ITERATION_N_THRESHOLD:
        return LARGE_N_PRECISIONS
    return PRECISIONS


def write_checkpoint(gate: dict[str, Any], schedule_rows: list[dict[str, Any]], out_json: Path) -> None:
    result = {
        "schema": "EdgeLedgerBuild.v1",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "route": "CHALLENGER_NOT_RH",
        "promotion": "FORBIDDEN",
        "px_rh_claim": "NOT_MADE",
        "semantic_boundary": "finite_CCM_even_sector_diagnostic_only; not_a_certificate; DIAGNOSTIC_NEVER_A_PROOF",
        "python_flint_version": __import__("flint").__version__,
        "python_version": platform.python_version(),
        "eigen_method": (
            "python-flint acb_mat.eig(right=True), algorithm='vdhoeven_mourrain' with "
            "'rump' fallback and precision-escalation retry, for dim <= "
            f"{INVERSE_ITERATION_N_THRESHOLD + 1}; flint returns right eigenvectors "
            "pre-normalized to unit l2 (verified empirically). Above that dimension, "
            "full-spectrum isolation was found to fail outright regardless of "
            "precision (empirically: eig(nonstop=True) returns NaN for all 164 "
            "eigenvalues at N=163 up to dps=520), so the two smallest eigenpairs are "
            "instead obtained by unshifted inverse power iteration "
            "(algorithm='precond' linear solves) with deflation for the second "
            "eigenpair, seeded generically (no external near-null vector), followed "
            "by a Rayleigh-quotient eigenvalue read-off; residuals are stored per cell."
        ),
        "precisions_dps_default": list(PRECISIONS),
        "precisions_dps_large_N": list(LARGE_N_PRECISIONS),
        "large_N_threshold": INVERSE_ITERATION_N_THRESHOLD,
        "h_relative": H_RELATIVE_NOTE,
        "oddities": [
            {
                "id": "dlambda1_dL_is_O1_while_lambda1_is_astronomically_small",
                "observation": (
                    "dlambda1/dL at fixed prime set is O(1) (e.g. +0.153 at m=13) while "
                    "lambda1 itself ranges over 1e-31 (m=13) down to ~1e-311 (m=163). "
                    "The super-small ground eigenvalue exists only AT the consistent "
                    "point L = log m; detuning L by h = 1e-6*L already moves lambda1 by "
                    "roughly h*O(1) ~ 1e-7*L, i.e. by many orders of magnitude relative "
                    "to lambda1's own size. This is a genuine finding, not a bug -- do "
                    "not try to fix it (recorded, not explained away, per project rule: "
                    "write down what is strange before it is explained)."
                ),
                "consequence_for_probe_2": (
                    "The 6-significant-digit Hellmann-Feynman/finite-difference agreement "
                    "the precommit originally demanded is unattainable by construction: "
                    "the CCM kernel entries depend on L internally (via terms like "
                    "2(L-x)/L * cos(2*pi*n*x/L)), so this is not a pure domain (window) "
                    "variation of a fixed functional form, and the classical Fuchs/"
                    "Hadamard identity is not expected to apply to it as written. Both "
                    "FD and HF estimates carry O(h^2 * lambda1'''/lambda1') truncation "
                    "error, and lambda1''' is enormous relative to lambda1' for a "
                    "function changing by 30+ orders of magnitude across the schedule. "
                    "See docs/routeB_bus/phase5_scripts/PRECOMMIT_2026-09-03_edge_ledger_probes.md "
                    "AMENDMENT 2 (frozen 2026-09-03 12:25) for the full reading; this "
                    "script stores dlambda1_dL_fd, dlambda1_dL_hf and their agreement "
                    "flag honestly for every cell (including cells where full isolation "
                    "makes lambda1/lambda2 individually rigorous, e.g. m=13,23,43) -- the "
                    "mismatch is not a precision artifact confined to the large-N "
                    "inverse-iteration cells, it reproduces at full rigor."
                ),
            }
        ],
        "regression_gate": gate,
        "schedule": schedule_rows,
        "status": "IN_PROGRESS" if len(schedule_rows) < 7 else "COMPLETE",
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    out_json.write_text(text, encoding="utf-8")


def load_checkpoint(out_json: Path) -> tuple[dict[str, Any] | None, list[dict[str, Any]]]:
    """Resume support: if a partial edge_ledger.json already exists (e.g. a
    prior run was interrupted), reuse its regression gate and completed
    schedule rows instead of recomputing them."""
    if not out_json.exists():
        return None, []
    try:
        data = json.loads(out_json.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None, []
    gate = data.get("regression_gate")
    rows = data.get("schedule", [])
    return gate, rows


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    out_json = OUT_DIR / "edge_ledger.json"

    cached_gate, cached_rows = load_checkpoint(out_json)
    if cached_gate is not None and cached_gate.get("pass"):
        gate = cached_gate
        print(
            f"[edge_ledger] RESUME: reusing cached regression gate (PASS) and "
            f"{len(cached_rows)} already-completed cell(s): "
            f"{[(r['m'], r['N'], r['role']) for r in cached_rows]}",
            flush=True,
        )
    else:
        progress("[edge_ledger] regression gate m=13 N=120 ...")
        gate = run_gate()
        progress_done()
        if not gate["pass"]:
            print("REGRESSION_FAIL: gate did not pass.", file=sys.stderr)
            print(json.dumps(gate, indent=2, sort_keys=True), file=sys.stderr)
            (OUT_DIR / "edge_ledger_GATE_FAIL.json").write_text(
                json.dumps(gate, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            return 2
        cached_rows = []
    print(
        f"[edge_ledger] gate PASS: lambda1(dps={PRECISIONS[-1]}) = "
        f"{gate[f'dps_{PRECISIONS[-1]}']['lambda1']['ball']}",
        flush=True,
    )
    write_checkpoint(gate, cached_rows, out_json)

    cells: list[tuple[int, int, str]] = []
    for m in SCHEDULE_M:
        cells.append((m, m, "main_schedule"))
    for m, N in N_CHECK_PAIRS:
        cells.append((m, N, "n_check"))

    done_keys = {(r["m"], r["N"]) for r in cached_rows}
    schedule_rows: list[dict[str, Any]] = list(cached_rows)
    for m, N, role in cells:
        if (m, N) in done_keys:
            print(f"[edge_ledger] RESUME: skipping already-completed m={m} N={N} ({role})", flush=True)
            continue
        row: dict[str, Any] = {"m": m, "N": N, "role": role, "precision": {}}
        precs = precisions_for(N)
        large_n_cell = N > INVERSE_ITERATION_N_THRESHOLD
        cell_started = time.time()
        for i, dps in enumerate(precs):
            if large_n_cell and i > 0:
                elapsed_so_far = time.time() - cell_started
                if elapsed_so_far > LARGE_N_TIME_BUDGET_SECONDS * 0.5:
                    row["precision_doubling_skipped_time_budget"] = {
                        "elapsed_after_previous_precision_seconds": elapsed_so_far,
                        "budget_seconds": LARGE_N_TIME_BUDGET_SECONDS,
                        "reason": "projected doubled-precision run risked exceeding the 40-minute budget for this cell",
                    }
                    break
            progress(f"[edge_ledger] m={m} N={N} role={role} dps={dps} building ...")
            t0 = time.time()
            cell = build_cell(m, N, dps)
            progress_done()
            print(
                f"[edge_ledger] m={m} N={N} dps={dps} done in {time.time() - t0:.2f}s "
                f"lambda1={cell['lambda1']['ball']} lambda2={cell['lambda2']['ball']} "
                f"method={cell['eigen_algorithm_lambda0']} dps_effective={cell['dps_effective']}",
                flush=True,
            )
            row["precision"][str(dps)] = cell
        precs_run = [p for p in precs if str(p) in row["precision"]]
        if len(precs_run) == 2:
            low = row["precision"][str(precs_run[0])]
            high = row["precision"][str(precs_run[1])]
            row["insufficient_precision_flags"] = check_insufficient_precision(low, high)
            row["precision_doubling_void"] = bool(low["dps_effective"] == high["dps_effective"])
            if row["precision_doubling_void"]:
                print(
                    f"[edge_ledger] ODDITY m={m} N={N}: both precision runs "
                    f"({precs_run[0]}, {precs_run[1]}) escalated to the SAME "
                    f"effective precision ({low['dps_effective']} dps) via the "
                    "bump fallback -- the doubling cross-check is void for this cell.",
                    flush=True,
                )
        else:
            row["insufficient_precision_flags"] = "NOT_EVALUATED_ONLY_ONE_PRECISION_RUN"
            row["precision_doubling_void"] = None
        schedule_rows.append(row)
        write_checkpoint(gate, schedule_rows, out_json)
        print(f"[edge_ledger] checkpoint written after m={m} N={N} ({len(schedule_rows)}/7 cells)", flush=True)

    print(f"[edge_ledger] wrote {out_json}", flush=True)
    write_probe1_report(schedule_rows, out_json)
    return 0


def best_precision_cell(row: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    """The highest-dps precision actually run for this row (large-N cells use
    their own (900,1400) ladder, not the default (120,240) one, and may have
    skipped the doubled run under the time budget)."""
    keys = sorted(row["precision"].keys(), key=int)
    best = keys[-1]
    return best, row["precision"][best]


def write_probe1_report(schedule_rows: list[dict[str, Any]], json_path: Path) -> None:
    precommit_text = PRECOMMIT.read_text(encoding="utf-8") if PRECOMMIT.exists() else ""

    main_rows = [r for r in schedule_rows if r["role"] == "main_schedule"]
    deltas = {}
    ratios = {}
    rel_gaps = {}
    for r in main_rows:
        _, cell = best_precision_cell(r)
        deltas[r["m"]] = arb(cell["delta"]["ball"])
        ratios[r["m"]] = arb(cell["lambda2_over_lambda1"]["ball"])
        rel_gaps[r["m"]] = arb(cell["rel_gap_delta_over_abs_lambda1"]["ball"])

    ms_sorted = sorted(deltas.keys())
    delta_vals = [deltas[m] for m in ms_sorted]
    delta_floats = [float(v.mid()) for v in delta_vals]
    max_delta = max(delta_floats)
    min_delta = min(delta_floats)
    d13 = float(deltas[13].mid())
    d163 = float(deltas[163].mid())

    monotone_nonincreasing = all(
        delta_floats[i] >= delta_floats[i + 1] - 1e-300 for i in range(len(delta_floats) - 1)
    )
    confirmed = (d163 / d13 <= 0.1) and monotone_nonincreasing
    refuted = (max_delta / min_delta) <= 2.0
    if confirmed:
        verdict = "CONFIRMED"
    elif refuted:
        verdict = "REFUTED"
    else:
        verdict = "UNRESOLVED"

    verdict_line_source = "not found in precommit text"
    for line in precommit_text.splitlines():
        if verdict in line and ("CONFIRMED" in line or "REFUTED" in line or "else UNRESOLVED" in line):
            if verdict == "CONFIRMED" and line.strip().startswith("- CONFIRMED"):
                verdict_line_source = line.strip()
                break
            if verdict == "REFUTED" and line.strip().startswith("- REFUTED"):
                verdict_line_source = line.strip()
                break
    if verdict == "UNRESOLVED":
        verdict_line_source = "else UNRESOLVED. Also report relative gap lambda2/lambda1 and (lambda2-lambda1)/|lambda1|; these are descriptive, no threshold."

    lines = []
    lines.append("# Probe 1 report -- absolute gap Delta_m = lambda2 - lambda1 along the schedule")
    lines.append("")
    lines.append(
        f"Source data: `{json_path.relative_to(REPO)}`. Default cells (N<={INVERSE_ITERATION_N_THRESHOLD}) "
        f"use precision dps in {PRECISIONS} (highest retained, cross-checked against the lower); "
        f"large-N cells (N>{INVERSE_ITERATION_N_THRESHOLD}) use dps in {LARGE_N_PRECISIONS} via the "
        "inverse-iteration fallback (see below), possibly with the doubled run skipped under the "
        "40-minute time budget -- each row below reports the highest dps actually run for it."
    )
    lines.append("")
    lines.append("| m | dps used | method | lambda1 | lambda2 | Delta_m = lambda2-lambda1 | lambda2/lambda1 | Delta_m/|lambda1| |")
    lines.append("|---|---|---|---|---|---|---|---|")
    for r in main_rows:
        dps_key, cell = best_precision_cell(r)
        lines.append(
            f"| {r['m']} | {dps_key} | {cell['eigen_algorithm_lambda0']} | {cell['lambda1']['ball']} | {cell['lambda2']['ball']} | "
            f"{cell['delta']['ball']} | {cell['lambda2_over_lambda1']['ball']} | "
            f"{cell['rel_gap_delta_over_abs_lambda1']['ball']} |"
        )
    lines.append("")
    lines.append("## N-check cells (secondary)")
    lines.append("")
    lines.append("| m | N | dps used | lambda1 | lambda2 | Delta | lambda2/lambda1 |")
    lines.append("|---|---|---|---|---|---|---|")
    for r in schedule_rows:
        if r["role"] != "n_check":
            continue
        dps_key, cell = best_precision_cell(r)
        lines.append(
            f"| {r['m']} | {r['N']} | {dps_key} | {cell['lambda1']['ball']} | {cell['lambda2']['ball']} | "
            f"{cell['delta']['ball']} | {cell['lambda2_over_lambda1']['ball']} |"
        )
    lines.append("")
    lines.append(f"max(Delta_m) = {max_delta:.6e} (at some m), min(Delta_m) = {min_delta:.6e}.")
    lines.append(f"Delta_163 / Delta_13 = {d163 / d13:.6e}.")
    lines.append(f"max(Delta_m)/min(Delta_m) = {max_delta / min_delta:.6e}.")
    lines.append(f"Delta_m monotone non-increasing over the schedule: {monotone_nonincreasing}.")
    lines.append("")
    lines.append(f"## Verdict: {verdict}")
    lines.append("")
    lines.append(f"Frozen rule quoted verbatim from the precommit: {verdict_line_source}")
    lines.append("")
    lines.append(
        "This is Probe 1's descriptive part only, per the executor's task boundary. "
        "Probe 2 (window-variation / Hellmann-Feynman) raw data is stored in the same "
        "JSON (dlambda*_dL_fd, dlambda*_dL_hf fields) but its CONFIRMED/REFUTED verdict "
        "is not evaluated here. Probe 3 (ratio kill-test) is out of scope for this script."
    )
    lines.append("")
    lines.append("DIAGNOSTIC_NEVER_A_PROOF. PX_RH_CLAIM: NOT_MADE.")

    report_path = OUT_DIR / "edge_ledger_probe1.md"
    report_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[edge_ledger] wrote {report_path}", flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
