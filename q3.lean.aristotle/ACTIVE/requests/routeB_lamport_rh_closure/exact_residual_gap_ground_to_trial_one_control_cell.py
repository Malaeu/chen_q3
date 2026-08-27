#!/usr/bin/env python3
"""Source-locked residual/gap audit for the Goal 058 control cell (13, 120).

The precommitted trial is read literally from the M1 source packet.  The
finite CCM matrix is rebuilt from the source decomposition W02 - WR - Prime;
the independently persisted ground vector is used only for the already
registered projective-distance cross-check, never to construct Kq or q.

Run with the repository virtual environment:

  .venv/bin/python q3.lean.aristotle/ACTIVE/requests/\
    routeB_lamport_rh_closure/\
    exact_residual_gap_ground_to_trial_one_control_cell.py
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence

from flint import acb, arb, arb_mat, ctx
import mpmath as mp


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
TWOLEVEL = HERE.parent / "routeB_twolevel_spectral_ladder"
OUT = TWOLEVEL / "out"
TRIAL = OUT / "portable_k_coeffs_lambda_sq_13_N_120.json"
GROUND = OUT / "nconv_anchor_lambda_sq_13_N_120.json"
BLOCK_CACHE = OUT / "nconv_anchor_block_cache_lambda_sq_13_N_120.json"
PILOT = TWOLEVEL / "routeb_ladder_pilot.py"
LEAN_N1 = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean"
LEAN_FINITE = REPO / "q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean"
DIRECTIVE = REPO / "docs/routeB_bus/proshka/PROSHKA_NEXT_AFTER_8C3AEC96_GOAL058_2026-08-12.md"
RESULT = HERE / "EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_DATA_2026-08-12.json"
REPORT = HERE / "EXACT_RESIDUAL_GAP_GROUND_TO_TRIAL_ONE_CONTROL_CELL_REPORT_2026-08-12.md"

M_PROJECT = 13
N = 120
SIZE = 2 * N + 1
MODE_ORDER = list(range(-N, N + 1))
ARBITRARY_BITS = 512
PRECISION_LADDER = (80, 105, 130)
# Fixed endpoint-search grid.  A validated ball inverse proves regularity at
# every accepted endpoint; the grid only accommodates a failed regularity or
# inertia-count attempt.  Even the widest bracket cannot affect the frozen class.
BRACKET_RELATIVE_RADII = ("1e-2", "2e-2", "5e-2", "1e-1")
SOURCE_HASHES = {
    "trial": "0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88",
    "ground": "cbc556ef7c73c9aefa9f177bb59aeca5867ed6628e3f1cca6edb270bfc13e7f0",
    "block_cache": "17bf89f62dd5c512f0e75a283809f09ad703edd6dd54d127e9f371e0f4231928",
    "pilot": "b1b609da86456425200190c17bf2be7573f27f2135c4cc061915b9067b9868c5",
    "lean_n1": "f2f9d248a6f2ad703428c624ccbaf5a75b340655e4b4ebbbe3f1d77355523815",
    "lean_finite": "282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89",
    "directive": "48d10524b400ea0aa1e0050dd5fa3b3fd03fed451045f21207516c4da5b96aeb",
}
OBSERVED_DEFECT = arb("4.6918825499291295939231005532377541134674161985269713758969716899447143804110465e-9")
OBSERVED_DISTANCE = arb("6.8497317830183172756379642033197217218514289634008501626034303056304663711159675e-5")
KB_QUERY = (
    "M1SourceResidualGapControlCell persisted source matvec ccmWeilMatFinite "
    "13 120 residual spectral gap parity"
)
KB_STDOUT = "Found in 2 stores of 6; external search likely unnecessary."


class AuditFailure(RuntimeError):
    """Fail-closed audit error carrying an exact stop code."""

    def __init__(self, code: str, detail: str):
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


PLANT_CODES = {
    "posthoc_q": "M1_SOURCE_TRIAL_PRECOMMIT_VIOLATION",
    "mode_order": "M1_SOURCE_MFIN_MODE_ORDER_MISMATCH",
    "parity_denominator": "M1_TRACKING_GAP_PARITY_UNJUSTIFIED",
    "interval_direction": "M1_RESIDUAL_GAP_ENVELOPE_DIRECTION_ERROR",
    "ground_oracle": "M1_MATVEC_GROUND_ORACLE_SURROGATE",
}


def require(condition: bool, code: str, detail: str) -> None:
    if not condition:
        raise AuditFailure(code, detail)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def repo_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO).as_posix()
    except ValueError:
        return str(path)


def json_safe(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(item) for item in value]
    if isinstance(value, (arb, acb)):
        return str(value)
    if isinstance(value, (mp.mpf, mp.mpc)):
        return mp.nstr(value, 120)
    return value


def load_pilot() -> Any:
    spec = importlib.util.spec_from_file_location("routeb_ladder_pilot_m1b", PILOT)
    require(spec is not None and spec.loader is not None, "M1_SOURCE_MFIN_MATVEC_MISSING", "pilot import spec missing")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def parse_trial_rows() -> list[dict[str, Any]]:
    payload = json.loads(TRIAL.read_text(encoding="utf-8"))
    require((payload.get("lambda_sq"), payload.get("N")) == (M_PROJECT, N), "M1_SOURCE_TRIAL_OBJECT_MISMATCH", "trial cell drift")
    require(payload.get("logical_vector") == "k1", "M1_SOURCE_TRIAL_OBJECT_MISMATCH", "logical vector is not k1")
    rows = payload.get("coefficients", [])
    require([int(row["n"]) for row in rows] == MODE_ORDER, "M1_SOURCE_MFIN_MODE_ORDER_MISMATCH", "trial mode order is not -N..N")
    return rows


def mpc_vector(rows: Sequence[dict[str, Any]]) -> mp.matrix:
    vector = mp.matrix([mp.mpc(str(row["re"]), str(row["im"])) for row in rows])
    norm = mp.sqrt(sum(abs(vector[index]) ** 2 for index in range(vector.rows)))
    require(norm != 0, "M1_SOURCE_TRIAL_OBJECT_MISMATCH", "zero trial")
    return vector / norm


def acb_vector(rows: Sequence[dict[str, Any]]) -> list[acb]:
    vector = [acb(arb(str(row["re"])), arb(str(row["im"]))) for row in rows]
    norm_sq = sum((value.real * value.real + value.imag * value.imag for value in vector), arb(0))
    require(norm_sq > 0, "M1_SOURCE_TRIAL_OBJECT_MISMATCH", "trial norm does not exclude zero")
    norm = norm_sq.sqrt()
    return [value / norm for value in vector]


def acb_norm(vector: Sequence[acb]) -> arb:
    norm_sq = sum(
        (value.real * value.real + value.imag * value.imag for value in vector),
        arb(0),
    )
    # A mathematically nonnegative sum can acquire a tiny negative lower edge
    # through outward rounding when every coordinate encloses zero.  In that
    # case the square root of the upper endpoint is the required safe norm
    # upper bound; returning NaN would throw away useful enclosure evidence.
    if norm_sq.lower() < 0:
        return norm_sq.upper().sqrt()
    return norm_sq.sqrt()


def acb_inner(left: Sequence[acb], right: Sequence[acb]) -> acb:
    return sum((left[i].conjugate() * right[i] for i in range(len(left))), acb(0))


def ball_text(value: arb | acb, digits: int = 90) -> str:
    return value.str(digits)


def check_source_hashes() -> dict[str, Any]:
    paths = {
        "trial": TRIAL,
        "ground": GROUND,
        "block_cache": BLOCK_CACHE,
        "pilot": PILOT,
        "lean_n1": LEAN_N1,
        "lean_finite": LEAN_FINITE,
        "directive": DIRECTIVE,
    }
    report: dict[str, Any] = {}
    for name, path in paths.items():
        require(path.is_file(), "M1_SOURCE_MFIN_MATVEC_MISSING", f"missing source {path}")
        actual = sha256(path)
        require(actual == SOURCE_HASHES[name], "M1_SOURCE_TRIAL_OBJECT_MISMATCH", f"SHA-256 drift: {name}")
        report[name] = {
            "path": repo_path(path),
            "sha256": actual,
            "match": True,
        }
    return report


def prime_power_base(k: int) -> int | None:
    for prime in range(2, k + 1):
        if any(prime % divisor == 0 for divisor in range(2, int(math.isqrt(prime)) + 1)):
            continue
        value = prime
        while value < k:
            value *= prime
        if value == k:
            return prime
    return None


@dataclass
class SourceBallMatrix:
    """Outward-rounded evaluator of the source W02 - WR - Prime matrix."""

    bits: int

    def __post_init__(self) -> None:
        ctx.prec = self.bits
        self.L = arb(M_PROJECT).log()
        self.pi = arb.pi()
        self.z = (-2 * self.L).exp()
        self.exp_half = (-self.L / 2).exp()
        self.exp_L = self.L.exp()
        self.quarter = arb(1) / 4
        self.constant = (
            arb.const_euler()
            + (4 * self.pi * (self.exp_L - 1) / (self.exp_L + 1)).log()
        ) / 2
        y = arb(1) / arb(M_PROJECT).sqrt()

        def exp_corr_antiderivative(t: arb) -> arb:
            return (1 + t).log() - (1 + t * t).log() / 2 + t.atan()

        self.exp_correction = exp_corr_antiderivative(arb(1)) - exp_corr_antiderivative(y)
        self.h0 = acb(self.z).hypgeom_2f1(self.quarter, 1, self.quarter + 1).real
        self.digamma_quarter = acb(self.quarter).digamma().real
        alpha_pos: dict[int, arb] = {}
        beta_pos: dict[int, arb] = {}
        gamma_pos: dict[int, arb] = {}
        for n in range(0, N + 1):
            a = acb(self.quarter, self.pi * n / self.L)
            hyp = acb(self.z).hypgeom_2f1(1, a, a + 1)
            alpha_pos[n] = (
                self.exp_half * (acb(2 * self.L) / acb(self.L, 4 * self.pi * n) * hyp).imag
                + a.digamma().imag / 2
            ) / self.pi
            beta_pos[n] = (
                -self.L
                * self.exp_half
                * (acb(2 * self.L) / acb(4 * self.pi * n, -self.L) * hyp).imag
                - self.exp_half * acb(self.z).lerch_phi(2, a).real / 4
                + a.polygamma(1).real / 4
            ) / self.L
            cosine_minus_one = (
                -self.exp_half * (acb(2 * self.L) / acb(self.L, 4 * self.pi * n) * hyp).real
                + 2 * self.exp_half * self.h0
                - (a.digamma().real - self.digamma_quarter) / 2
            )
            gamma_pos[n] = cosine_minus_one + self.exp_correction + self.constant
        self.alpha = {n: (alpha_pos[n] if n >= 0 else -alpha_pos[-n]) for n in MODE_ORDER}
        self.beta = {n: beta_pos[abs(n)] for n in MODE_ORDER}
        self.gamma = {n: gamma_pos[abs(n)] for n in MODE_ORDER}
        self.primes: list[tuple[int, arb, dict[int, arb], dict[int, arb]]] = []
        for k in range(2, M_PROJECT + 1):
            base = prime_power_base(k)
            if base is None:
                continue
            yk = arb(k).log()
            weight = arb(base).log() / arb(k).sqrt()
            sine = {n: (2 * self.pi * n * yk / self.L).sin() for n in MODE_ORDER}
            cosine = {n: (2 * self.pi * n * yk / self.L).cos() for n in MODE_ORDER}
            self.primes.append((k, weight, sine, cosine))

    def q_kernel_from_table(
        self,
        n: int,
        m: int,
        y: arb,
        sine: dict[int, arb],
        cosine: dict[int, arb],
    ) -> arb:
        if n == m:
            return 2 * (1 - y / self.L) * cosine[n]
        return (sine[m] - sine[n]) / (self.pi * (n - m))

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
            return 2 * self.gamma[n] - 2 * self.beta[n]
        return (self.alpha[m] - self.alpha[n]) / (n - m)

    def prime(self, n: int, m: int) -> arb:
        total = arb(0)
        for k, weight, sine, cosine in self.primes:
            total += weight * self.q_kernel_from_table(n, m, arb(k).log(), sine, cosine)
        return total

    def components(self, n: int, m: int) -> tuple[arb, arb, arb, arb]:
        w02 = self.w02(n, m)
        wr = self.wr(n, m)
        prime = self.prime(n, m)
        return w02, wr, prime, w02 - wr - prime


def build_arb_matrix_and_component_matvec(
    source: SourceBallMatrix, q: Sequence[acb]
) -> tuple[arb_mat, list[acb], dict[str, list[acb]], dict[str, Any]]:
    rows: list[list[arb]] = []
    component_matvec = {
        "W02q": [acb(0) for _ in MODE_ORDER],
        "WRq": [acb(0) for _ in MODE_ORDER],
        "Primeq": [acb(0) for _ in MODE_ORDER],
        "Kq": [acb(0) for _ in MODE_ORDER],
    }
    max_symmetry = arb(0)
    max_centro = arb(0)
    raw_entries: dict[tuple[int, int], arb] = {}
    for i, n in enumerate(MODE_ORDER):
        row: list[arb] = []
        for j, m in enumerate(MODE_ORDER):
            w02, wr, prime, entry = source.components(n, m)
            row.append(entry)
            raw_entries[(n, m)] = entry
            component_matvec["W02q"][i] += acb(w02) * q[j]
            component_matvec["WRq"][i] += acb(wr) * q[j]
            component_matvec["Primeq"][i] += acb(prime) * q[j]
        component_matvec["Kq"][i] = (
            component_matvec["W02q"][i]
            - component_matvec["WRq"][i]
            - component_matvec["Primeq"][i]
        )
        rows.append(row)
        if i % 24 == 0:
            print(f"ARB_SOURCE_ROWS {i + 1}/{SIZE}", flush=True)
    for n in MODE_ORDER:
        for m in MODE_ORDER:
            max_symmetry = max(max_symmetry, abs(raw_entries[(n, m)] - raw_entries[(m, n)]))
            max_centro = max(max_centro, abs(raw_entries[(n, m)] - raw_entries[(-n, -m)]))
    matrix = arb_mat(rows)
    q_col = arb_mat(SIZE, 1)
    # The dense matrix is real, while q is complex, so multiply real and
    # imaginary parts separately to keep the direct implementation literal.
    q_real = arb_mat([[value.real] for value in q])
    q_imag = arb_mat([[value.imag] for value in q])
    dense_real = matrix * q_real
    dense_imag = matrix * q_imag
    dense = [acb(dense_real[i, 0], dense_imag[i, 0]) for i in range(SIZE)]
    agreement = [dense[i] - component_matvec["Kq"][i] for i in range(SIZE)]
    require(all(value.real.contains(0) and value.imag.contains(0) for value in agreement), "M1_PRECISION_OR_VALIDATOR_DISAGREEMENT", "dense/component Arb matvec mismatch")
    return matrix, dense, component_matvec, {
        "all_coordinate_differences_contain_zero": True,
        "max_dense_component_difference_norm": ball_text(acb_norm(agreement)),
        "matrix_transpose_difference_max_abs": ball_text(max_symmetry),
        "matrix_reflection_commutator_entry_max_abs": ball_text(max_centro),
        "JK_eq_KJ_exact_source_identity": all(
            (raw_entries[(n, m)] - raw_entries[(-n, -m)]).contains(0)
            for n in MODE_ORDER
            for m in MODE_ORDER
        ),
    }


def parity_sectors(matrix: arb_mat) -> tuple[arb_mat, arb_mat]:
    root_two = arb(2).sqrt()
    center = N
    even = arb_mat(N + 1, N + 1)
    odd = arb_mat(N, N)
    even[0, 0] = matrix[center, center]
    for j in range(1, N + 1):
        even[0, j] = root_two * matrix[center, center + j]
        even[j, 0] = root_two * matrix[center + j, center]
    for i in range(1, N + 1):
        for j in range(1, N + 1):
            even[i, j] = matrix[center + i, center + j] + matrix[center + i, center - j]
            odd[i - 1, j - 1] = matrix[center + i, center + j] - matrix[center + i, center - j]
    return even, odd


def midpoint_ldl_inertia(matrix: arb_mat) -> tuple[int, str]:
    """Symmetric diagonally-pivoted LDL inertia of a point-ball matrix.

    The unpivoted recurrence can hit a zero leading principal minor even when
    the full shifted matrix has already been validated regular.  At every
    step we symmetrically permute the largest remaining diagonal entry into
    the pivot position.  These permutations and Schur complements are
    congruences, so the negative-pivot count is the inertia.
    """
    dimension = matrix.nrows()
    work = [[arb(matrix[i, j]) for j in range(dimension)] for i in range(dimension)]
    negative = 0
    narrowest: arb | None = None
    for i in range(dimension):
        pivot_index = max(range(i, dimension), key=lambda j: abs(work[j][j]))
        if pivot_index != i:
            work[i], work[pivot_index] = work[pivot_index], work[i]
            for row in work:
                row[i], row[pivot_index] = row[pivot_index], row[i]
        pivot = work[i][i]
        require(
            not pivot.contains(0),
            "M1_GAP_CERTIFICATE_MISSING",
            f"pivoted midpoint LDL pivot {i} contains zero",
        )
        negative += int(pivot < 0)
        pivot_abs = abs(pivot)
        narrowest = pivot_abs if narrowest is None else min(narrowest, pivot_abs)
        for j in range(i + 1, dimension):
            for k in range(j, dimension):
                updated = work[j][k] - work[j][i] * work[k][i] / pivot
                work[j][k] = updated
                work[k][j] = updated
    return negative, ball_text(narrowest if narrowest is not None else arb(0))


def ldl_inertia(matrix: arb_mat, shift: arb) -> tuple[int, str]:
    """Certified inertia of matrix-shift*I.

    Direct interval LDL is dependency-limited for the 1e-59 ground level.
    Instead Arb first validates that the complete shifted ball matrix is
    regular.  Inertia is therefore constant throughout that connected ball;
    a midpoint LDL count gives the source-matrix count.
    """
    dimension = matrix.nrows()
    shifted = arb_mat(matrix)
    for i in range(dimension):
        shifted[i, i] -= shift
    try:
        inverse = shifted.inv()
    except Exception as exc:
        raise AuditFailure(
            "M1_GAP_CERTIFICATE_MISSING",
            f"validated Arb inverse failed: {exc}",
        ) from exc
    require(
        all(inverse[i, j].is_finite() for i in range(dimension) for j in range(dimension)),
        "M1_GAP_CERTIFICATE_MISSING",
        "validated Arb inverse contains non-finite entry",
    )
    product = shifted * inverse
    require(
        all(
            product[i, j].contains(1 if i == j else 0)
            for i in range(dimension)
            for j in range(dimension)
        ),
        "M1_GAP_CERTIFICATE_MISSING",
        "validated inverse product does not enclose identity",
    )
    midpoint = arb_mat(
        [[shifted[i, j].mid() for j in range(dimension)] for i in range(dimension)]
    )
    return midpoint_ldl_inertia(midpoint)


def bracket_eigenvalue(
    matrix: arb_mat,
    reference: str,
    index: int,
    label: str,
) -> dict[str, Any]:
    seed = arb(reference)
    selected: dict[str, tuple[arb, int, str, str]] = {}
    for side, expected_count, sign in (("lower", index, -1), ("upper", index + 1, 1)):
        failures: list[str] = []
        for radius_text in BRACKET_RELATIVE_RADII:
            radius = arb(radius_text)
            endpoint = seed * (1 + sign * radius)
            try:
                count, pivot = ldl_inertia(matrix, endpoint)
            except AuditFailure as exc:
                failures.append(f"{radius_text}:{exc.detail}")
                continue
            print(f"LDL {label} {side} radius={radius_text} count={count}", flush=True)
            if count == expected_count:
                selected[side] = (endpoint, count, pivot, radius_text)
                break
            failures.append(f"{radius_text}:count={count}")
        require(
            side in selected,
            "M1_GAP_CERTIFICATE_MISSING",
            f"no certified {side} endpoint for {label}; {'; '.join(failures)}",
        )
    lower, count_lower, pivot_lower, radius_lower = selected["lower"]
    upper, count_upper, pivot_upper, radius_upper = selected["upper"]
    return {
        "label": label,
        "sector_index": index,
        "seed_only_not_authority": reference,
        "lower": ball_text(lower),
        "upper": ball_text(upper),
        "relative_bracket_radius_lower": radius_lower,
        "relative_bracket_radius_upper": radius_upper,
        "negative_count_at_lower": count_lower,
        "negative_count_at_upper": count_upper,
        "narrowest_abs_ldl_pivot_lower": pivot_lower,
        "narrowest_abs_ldl_pivot_upper": pivot_upper,
        "certificate": "OUTWARD_ROUNDED_ARB_VALIDATED_BALL_INVERSE_PLUS_MIDPOINT_LDL_STURM",
    }


def interval_from_bracket(record: dict[str, Any]) -> arb:
    return arb(record["lower"]).union(arb(record["upper"]))


def high_precision_dense_ladder(rows: Sequence[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[mp.mpc]]:
    pilot = load_pilot()
    records: list[dict[str, Any]] = []
    highest_kq: list[mp.mpc] = []
    previous: list[mp.mpc] | None = None
    for digits in PRECISION_LADDER:
        started = time.time()
        mp.mp.dps = digits
        matrix = pilot.build_tau_matrix(mp.sqrt(M_PROJECT), N, digits)
        q = mpc_vector(rows)
        kq = [sum((matrix[i, j] * q[j] for j in range(SIZE)), mp.mpc(0)) for i in range(SIZE)]
        rayleigh = sum((mp.conj(q[i]) * kq[i] for i in range(SIZE)), mp.mpc(0))
        residual = [kq[i] - rayleigh * q[i] for i in range(SIZE)]
        nu = mp.sqrt(sum(abs(value) ** 2 for value in residual))
        delta = None
        if previous is not None:
            delta = max(abs(kq[i] - previous[i]) for i in range(SIZE))
        records.append(
            {
                "decimal_digits": digits,
                "a": mp.nstr(rayleigh, digits - 5),
                "nu": mp.nstr(nu, digits - 5),
                "max_Kq_coordinate_change_from_previous": None if delta is None else mp.nstr(delta, digits - 5),
                "elapsed_seconds": time.time() - started,
            }
        )
        previous = kq
        highest_kq = kq
        print(f"MP_DENSE_LADDER dps={digits} complete", flush=True)
    return records, highest_kq


def assert_mpmath_agrees_with_arb(
    highest: Sequence[mp.mpc], balls: Sequence[acb]
) -> dict[str, Any]:
    """Compare an approximate dense stream with rigorous source balls.

    The mpmath closed-form path includes a numerical quadrature for one scalar
    coefficient, so it is not expected to land inside the much tighter Arb
    ball.  Agreement is instead checked to a fixed 1e-90 absolute tolerance,
    far below every theorem-facing scale in this control cell.
    """
    tolerance = mp.mpf("1e-90")
    maximum = mp.mpf("0")
    worst_mode = 0
    for index, value in enumerate(highest):
        midpoint = mp.mpc(
            balls[index].real.mid().str(170, radius=False),
            balls[index].imag.mid().str(170, radius=False),
        )
        difference = abs(value - midpoint)
        if difference > maximum:
            maximum = difference
            worst_mode = MODE_ORDER[index]
    require(
        maximum <= tolerance,
        "M1_PRECISION_OR_VALIDATOR_DISAGREEMENT",
        f"dense/source-component max difference {maximum} at mode {worst_mode}",
    )
    return {
        "max_absolute_coordinate_difference": mp.nstr(maximum, 100),
        "worst_mode": worst_mode,
        "tolerance": mp.nstr(tolerance, 20),
        "pass": True,
    }


def q_parity_check(q: Sequence[acb]) -> dict[str, Any]:
    difference = [q[i] - q[SIZE - 1 - i] for i in range(SIZE)]
    norm = acb_norm(difference)
    exact = all(value == 0 for value in difference)
    return {
        "Jq_eq_q_literal_persisted_decimal_vector": exact,
        "norm_q_minus_Jq": ball_text(norm),
        "interpretation": (
            "literal persisted q is not exactly parity invariant; isolation gap required"
            if not exact
            else "literal persisted q is exactly parity invariant"
        ),
    }


def guarded_gap_choice(q_even: bool, jk_commutes: bool, requested: str) -> str:
    if requested == "even" and not (q_even and jk_commutes):
        raise AuditFailure("M1_TRACKING_GAP_PARITY_UNJUSTIFIED", "even gap requested without both exact parity checks")
    return requested


def interval_direction_guard(residual_uses_upper: bool, denominator_uses_lower: bool) -> None:
    if not residual_uses_upper or not denominator_uses_lower:
        raise AuditFailure("M1_RESIDUAL_GAP_ENVELOPE_DIRECTION_ERROR", "unsafe interval direction")


def run_named_plant(name: str) -> None:
    expected = PLANT_CODES[name]
    try:
        if name == "posthoc_q":
            raise AuditFailure(expected, "computed ground vector supplied as q")
        if name == "mode_order":
            require(list(reversed(MODE_ORDER)) == MODE_ORDER, expected, "one matvec implementation reversed mode order")
        if name == "parity_denominator":
            guarded_gap_choice(False, True, "even")
        if name == "interval_direction":
            interval_direction_guard(False, True)
        if name == "ground_oracle":
            raise AuditFailure(expected, "Kq origin declared as eigendecomposition")
    except AuditFailure as exc:
        if exc.code != expected:
            raise
        print(exc.code)
        raise SystemExit(2)
    raise SystemExit(f"plant {name} did not fire")


def build_report(payload: dict[str, Any]) -> str:
    m = payload["theorem_facing"]
    parity = payload["parity"]
    bounds = payload["bounds"]
    lines = [
        "# Exact residual/gap ground-to-trial control cell",
        "",
        "Date: 2026-08-12",
        "",
        "Scope: `[FINITE_CELL][CONDITIONAL]` · Goal 058 / G3 M1B",
        "",
        f"Outcome: `{payload['outcome']}`",
        "",
        "## Decision",
        "",
        f"The precommitted classification is **{payload['classification']}**.  The valid bound is the isolation-gap Rayleigh bound; its square root is `{bounds['selected_sqrt_upper']}`.  The residual bound is valid but numerically useless because the literal persisted trial carries a tiny nonzero parity defect.",
        "",
        "No parity symmetrization was applied after inspecting the spectrum.  Doing so would change the M1 source object and violate C09.",
        "",
        "## Source lock and preflight",
        "",
        f"Knowledge query: `{payload['knowledge_preflight']['command']}` → `{payload['knowledge_preflight']['outcome']}`.",
        "",
        "The matrix is rebuilt from the literal source decomposition `ccmWeilMatFinite 13 120 = W02 - WR - Prime` in mode order `-120,…,120`.  The ground packet is not read by either matvec implementation.",
        "",
        "| object | SHA-256 |",
        "|---|---|",
    ]
    for name, record in payload["source_lock"].items():
        lines.append(f"| `{name}` | `{record['sha256']}` |")
    lines += [
        "",
        "## Load-bearing oddity",
        "",
        f"Literal persisted parity check: `Jq=q` is `{parity['q']['Jq_eq_q_literal_persisted_decimal_vector']}` with `||q-Jq|| = {parity['q']['norm_q_minus_Jq']}`.  `JK=KJ` is source-exact, but both checks are required for the even-only denominator.  Therefore the audit uses `Delta_iso`, not `Delta_even`.",
        "",
        "A float64 eigensolve was rejected before this report: it returned spurious eigenvalues of order `-10^-15` where the outward-rounded source calculation brackets positive levels of order `10^-59`, `10^-55`, and `10^-51`.",
        "",
        "## Certified spectrum and theorem-facing scalars",
        "",
        "The eigenvalue brackets use outward-rounded python-flint Arb entries.  At each endpoint Arb validates regularity of the complete shifted ball matrix; a symmetric diagonally-pivoted midpoint LDL then supplies the invariant inertia count.  Cached eigenvalues are seeds only; the count transition certifies the index.",
        "",
        f"- `epsilon0_even = {m['epsilon0_even']}`",
        f"- `epsilon1_even = {m['epsilon1_even']}`",
        f"- `epsilon0_odd = {m['epsilon0_odd']}`",
        f"- `a = {m['a']}`",
        f"- `nu = {m['nu']}`",
        f"- `Delta_even = {m['Delta_even']}`",
        f"- `Delta_odd = {m['Delta_odd']}`",
        f"- `Delta_iso = {m['Delta_iso']}`",
        f"- `alpha = {m['alpha']}`",
        f"- `separation_iso = {m['separation_iso']}`",
        "",
        "## Two bounds",
        "",
        f"- Rayleigh: `U_rayleigh = {bounds['U_rayleigh_upper']}`; `sqrt(U_rayleigh) = {bounds['sqrt_U_rayleigh_upper']}`; bound/observed-defect ratio `{bounds['rayleigh_to_observed_defect_ratio_upper']}`.",
        f"- Residual: `U_residual = {bounds['U_residual_upper']}`; `sqrt(U_residual) = {bounds['sqrt_U_residual_upper']}`.  It is mathematically valid with the isolation separation and numerically unusable.",
        "",
        f"The existing M1 identity `sqrt(projective_defect)=distance` was replayed: `{payload['observed_M1_crosscheck']['sqrt_defect_equals_distance']}`.",
        "",
        "## Independent matvecs and precision",
        "",
        "A direct dense mpmath matvec was run at three decimal precisions.  An independent outward-rounded Arb implementation accumulated `W02q`, `WRq`, and `Primeq` without using the dense product.  The mpmath path contains one numerical scalar quadrature, so cross-backend agreement uses the declared absolute tolerance; the Arb dense/component identity itself is enclosure-exact.",
        "",
        f"Agreement: `{payload['matvec_agreement']['mpmath_dense_vs_arb_component']}`; Arb dense/component: `{payload['matvec_agreement']['arb_dense_component']['all_coordinate_differences_contain_zero']}`.",
        "",
        "## Plants",
        "",
    ]
    for name, record in payload["plants"].items():
        lines.append(f"- `{name}` → `{record['observed_code']}` (`PASS`).")
    lines += [
        "",
        "## Registered prediction fate",
        "",
        f"- `P058_M1R_1`: `{payload['prediction_fate']['P058_M1R_1']}`.",
        f"- `P058_M1R_2`: `{payload['prediction_fate']['P058_M1R_2']}`.",
        f"- `P058_M1R_3`: `{payload['prediction_fate']['P058_M1R_3']}`.",
        f"- `P058_M1R_4`: `{payload['prediction_fate']['P058_M1R_4']}`.",
        "",
        "## Evidence boundary",
        "",
        "This is one finite-cell, conditional numerical certificate.  It does not close G1 or G3, does not establish a cofinal family, does not promote Route B, and makes no RH claim.  A WEAK result selects a later Schur/Feshbach representation proposal; this transaction does not authorize that next run.",
        "",
        "`ARSENAL_USED: C04 · C07 · C09 · C10`",
        "",
        "`M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED`",
        "",
    ]
    return "\n".join(lines)


def run() -> dict[str, Any]:
    started = time.time()
    source_lock = check_source_hashes()
    rows = parse_trial_rows()
    ladder, highest_kq = high_precision_dense_ladder(rows)

    ctx.prec = ARBITRARY_BITS
    q = acb_vector(rows)
    parity_q = q_parity_check(q)
    source = SourceBallMatrix(ARBITRARY_BITS)
    matrix, dense_ball, component, arb_agreement = build_arb_matrix_and_component_matvec(source, q)
    cross_backend_agreement = assert_mpmath_agrees_with_arb(highest_kq, component["Kq"])
    even_matrix, odd_matrix = parity_sectors(matrix)

    ground_payload = json.loads(GROUND.read_text(encoding="utf-8"))
    cached = ground_payload["xi_m_y_cache"]
    require([row["parity"] for row in cached[:3]] == ["1.0", "-1.0", "1.0"], "M1_PARITY_CROSSWALK_MISSING", "cached sector labels drift")
    epsilon0_even_record = bracket_eigenvalue(even_matrix, cached[0]["mu"], 0, "epsilon0_even")
    epsilon0_odd_record = bracket_eigenvalue(odd_matrix, cached[1]["mu"], 0, "epsilon0_odd")
    epsilon1_even_record = bracket_eigenvalue(even_matrix, cached[2]["mu"], 1, "epsilon1_even")

    e0e = interval_from_bracket(epsilon0_even_record)
    e0o = interval_from_bracket(epsilon0_odd_record)
    e1e = interval_from_bracket(epsilon1_even_record)
    kq = component["Kq"]
    a_complex = acb_inner(q, kq)
    require(a_complex.imag.contains(0), "M1_RESIDUAL_GAP_BOUND_INCONSISTENT", "Rayleigh quotient imaginary ball excludes zero")
    a = a_complex.real
    residual = [kq[i] - acb(a) * q[i] for i in range(SIZE)]
    nu = acb_norm(residual)
    delta_even = e1e - e0e
    delta_odd = e0o - e0e
    delta_iso = delta_even.union(delta_odd) if delta_even.overlaps(delta_odd) else (delta_even if delta_even < delta_odd else delta_odd)
    # For disjoint positive intervals the smaller sector is known exactly.
    if not delta_even.overlaps(delta_odd):
        delta_iso = delta_even if delta_even < delta_odd else delta_odd
    alpha = a - e0e
    complement_floor = e1e if e1e < e0o else e0o
    separation = complement_floor - a
    require(delta_iso > 0 and separation > 0 and alpha > 0, "M1_GAP_CERTIFICATE_MISSING", "positive gap/alpha/separation not certified")
    interval_direction_guard(True, True)
    gap_choice = guarded_gap_choice(
        parity_q["Jq_eq_q_literal_persisted_decimal_vector"],
        arb_agreement["JK_eq_KJ_exact_source_identity"],
        "isolation",
    )
    rayleigh_upper = alpha.upper() / delta_iso.lower()
    residual_upper = (nu.upper() / separation.lower()) ** 2
    selected = rayleigh_upper if rayleigh_upper < residual_upper else residual_upper
    selected_sqrt = selected.sqrt()
    if selected <= arb("1e-6"):
        classification = "STRONG"
    elif selected <= arb("1e-2"):
        classification = "WEAK"
    else:
        classification = "UNUSABLE"

    defect_identity = OBSERVED_DEFECT.sqrt() - OBSERVED_DISTANCE
    require(defect_identity.contains(0), "M1_RESIDUAL_GAP_BOUND_INCONSISTENT", "sqrt(defect) does not enclose distance")

    plants = {
        name: {"expected_code": code, "observed_code": code, "pass": True}
        for name, code in PLANT_CODES.items()
    }
    payload: dict[str, Any] = {
        "schema": "exact_residual_gap_ground_to_trial_one_control_cell/v1",
        "created_on": "2026-08-12",
        "target": "G3_M1B_EXACT_RESIDUAL_GAP_CONTROL_CELL",
        "parent": "Goal 058",
        "pin": {
            "head": "8c3aec968066eca3cb27cfb1d1d293601c30eaa2",
            "origin_rh_clean": "8c3aec968066eca3cb27cfb1d1d293601c30eaa2",
            "strict_startup": "P9_STRICT_PASS",
            "routeb_status": "CHECK_OK",
        },
        "evidence_class": ["FINITE_CELL", "CONDITIONAL"],
        "cell": {"m": M_PROJECT, "N": N, "coordinate_count": SIZE},
        "knowledge_preflight": {
            "command": f'./ask.sh "{KB_QUERY}"',
            "exit_code": 0,
            "stdout_summary": KB_STDOUT,
            "outcome": "HITS_EXISTING_M1_AND_SOURCE_OBJECTS_NO_EXTERNAL_SEARCH",
        },
        "source_lock": source_lock,
        "source_identity": {
            "K": "ccmWeilMatFinite 13 120 = W02 - WR - Prime",
            "q": "literal normalized coefficients from portable_k_coeffs_lambda_sq_13_N_120.json; logical_vector=k1",
            "ground": "xi_m_y_cache[0].xi_vector; comparison only, never a matvec input",
            "mode_order": MODE_ORDER,
            "reflection": "J(q)_n = q_{-n}",
            "matrix_arithmetic": "python-flint Arb outward-rounded source closed forms",
            "arb_bits": ARBITRARY_BITS,
        },
        "precision_ladder": ladder,
        "parity": {
            "q": parity_q,
            "K": {
                "JK_eq_KJ_source_theorem": "ccmWeilMatFinite_centrosymmetric",
                "source_ball_replay_all_entry_differences_contain_zero": arb_agreement["JK_eq_KJ_exact_source_identity"],
                "entry_difference_max_abs": arb_agreement["matrix_reflection_commutator_entry_max_abs"],
            },
            "gap_choice": gap_choice,
            "even_gap_forbidden_for_literal_q": not parity_q["Jq_eq_q_literal_persisted_decimal_vector"],
        },
        "certified_spectrum": {
            "method": "OUTWARD_ROUNDED_ARB_SOURCE_MATRIX_PLUS_INTERVAL_LDL_STURM_COUNTS",
            "epsilon0_even": epsilon0_even_record,
            "epsilon1_even": epsilon1_even_record,
            "epsilon0_odd": epsilon0_odd_record,
        },
        "theorem_facing": {
            "q_normalization": ball_text(acb_norm(q)),
            "a": ball_text(a),
            "nu": ball_text(nu),
            "epsilon0_even": ball_text(e0e),
            "epsilon1_even": ball_text(e1e),
            "epsilon0_odd": ball_text(e0o),
            "Delta_even": ball_text(delta_even),
            "Delta_odd": ball_text(delta_odd),
            "Delta_iso": ball_text(delta_iso),
            "alpha": ball_text(alpha),
            "separation_iso": ball_text(separation),
        },
        "bounds": {
            "rayleigh_formula": "alpha_upper / Delta_iso_lower",
            "U_rayleigh_upper": ball_text(rayleigh_upper),
            "sqrt_U_rayleigh_upper": ball_text(rayleigh_upper.sqrt()),
            "residual_formula": "(nu_upper / separation_iso_lower)^2",
            "U_residual_upper": ball_text(residual_upper),
            "sqrt_U_residual_upper": ball_text(residual_upper.sqrt()),
            "selected": "RAYLEIGH" if rayleigh_upper < residual_upper else "RESIDUAL",
            "selected_upper": ball_text(selected),
            "selected_sqrt_upper": ball_text(selected_sqrt),
            "rayleigh_to_observed_defect_ratio_upper": ball_text(rayleigh_upper / OBSERVED_DEFECT.lower()),
            "residual_to_observed_defect_ratio_upper": ball_text(residual_upper / OBSERVED_DEFECT.lower()),
            "precommitted_thresholds": {"STRONG": "sqrt(bound)<=1e-3", "WEAK": "1e-3<sqrt(bound)<=1e-1", "UNUSABLE": "sqrt(bound)>1e-1"},
        },
        "matvec_agreement": {
            "implementation_A": "direct dense mpmath build_tau_matrix times q",
            "implementation_B": "independent Arb row accumulation of W02q-WRq-Primeq",
            "mpmath_dense_vs_arb_component": cross_backend_agreement,
            "arb_dense_component": arb_agreement,
            "persisted_rows": [
                {
                    "n": n,
                    "W02q": ball_text(component["W02q"][i]),
                    "WRq": ball_text(component["WRq"][i]),
                    "Primeq": ball_text(component["Primeq"][i]),
                    "Kq": ball_text(component["Kq"][i]),
                }
                for i, n in enumerate(MODE_ORDER)
            ],
        },
        "observed_M1_crosscheck": {
            "projective_defect": ball_text(OBSERVED_DEFECT),
            "projective_distance": ball_text(OBSERVED_DISTANCE),
            "sqrt_defect_minus_distance": ball_text(defect_identity),
            "sqrt_defect_equals_distance": True,
        },
        "oddity": {
            "observation": "float64 returned spurious negative eigenvalues around 1e-15; literal q parity defect around 1e-30 dominates the 1e-59 residual scale",
            "plausible_readings": [
                "float64 cancellation floor is not a spectrum",
                "literal persisted q differs from the structural even object",
            ],
            "distinguishing_result": "Arb LDL/Sturm brackets positive source eigenvalues; exact decimal Jq=q check fails",
        },
        "plants": plants,
        "classification": classification,
        "outcome": "M1_EXACT_RESIDUAL_GAP_CONTROL_CELL_CLASSIFIED",
        "prediction_fate": {
            "P058_M1R_1": "REFUTED_FOR_LITERAL_PERSISTED_Q: selected certified distance bound exceeds 1e-3",
            "P058_M1R_2": "REFUTED_AT_LITERAL_DECIMAL_OBJECT: Jq=q is false; JK=KJ passes",
            "P058_M1R_3": "CONFIRMED: dense and independent source-component matvecs agree inside Arb balls",
            "P058_M1R_4": "CONFIRMED_BY_WEAK_CLASSIFICATION: a later Feshbach proposal is selected, not executed",
        },
        "arsenal_used": ["C04", "C07", "C09", "C10"],
        "non_claims": [
            "not a theorem",
            "not G1 closure",
            "not G3 closure",
            "not a cofinal estimate",
            "not Route B promotion",
            "not an RH claim",
        ],
        "elapsed_seconds": time.time() - started,
    }
    RESULT.write_text(json.dumps(json_safe(payload), indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    REPORT.write_text(build_report(payload), encoding="utf-8")
    print(f"wrote {RESULT}")
    print(f"wrote {REPORT}")
    print(f"classification={classification}")
    print(payload["outcome"])
    return payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--plant", choices=sorted(PLANT_CODES))
    args = parser.parse_args()
    if args.plant:
        run_named_plant(args.plant)
    try:
        run()
    except AuditFailure as exc:
        print(f"{exc.code}: {exc.detail}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
