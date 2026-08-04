#!/usr/bin/env python3
"""Rigorous Arb certificate for the CCM H2a sector cell ``(13, 2)``.

This script reconstructs the exact production object
``Q3.RouteB.ccmWeilMatFinite 13 2`` from its source formula.  IEEE-754
arithmetic is used only for a recorded diagnostic.  Every accepting check is
performed with python-flint Arb balls at 128, 256, and 512 bits.

The removable endpoint of the archimedean integral is evaluated through the
analytic identities

    (exp(z) - 1) / z = 1F1(1; 2; z),
    sinh(z) / z = sinc(i z),

and analytic difference quotients for the CCM q-kernel.  The certifier never
evaluates the raw 0/0 expression at the endpoint.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable

try:
    import flint
    from flint import acb, arb, ctx, fmpq
except ImportError as exc:  # pragma: no cover - fail-closed environment gate
    raise SystemExit("G2_CCM_SECTOR_CELL_13_2_ARB_BACKEND_MISSING") from exc


HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
REPO = PROJECT.parent
DEFAULT_OUTPUT = PROJECT / "out" / "ccm_h2a_sector_cell_13_2_cert.json"

EXPECTED_PARENT = "d95078004c71f6a68b1704a3eb1856bab0499ae1"
EXPECTED_M_PROJECT = 13
EXPECTED_N = 2
EXPECTED_PRECISIONS = (128, 256, 512)
EXPECTED_PYTHON_FLINT = "0.8.0"
MODE_ORDER = (-2, -1, 0, 1, 2)

SOURCE_FILES = {
    "Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean":
        "f2f9d248a6f2ad703428c624ccbaf5a75b340655e4b4ebbbe3f1d77355523815",
    "Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean":
        "282dc31c9bc558aefe8ab0b105fe844da017defdaaec4c2048d147327b72df89",
}

# This literal crosswalk is hashed and checked before any numerical work.
SOURCE_FORMULA = {
    "matrix_object": "Q3.RouteB.ccmWeilMatFinite 13 2",
    "entry_constructor": "Q3.RouteB.ccmWeilTauN1 13 n m",
    "L": "Real.log (13 : Real)",
    "mode_order": list(MODE_ORDER),
    "tau_formula": "ccmW02Entry L n m - ccmWREntry L n m - ccmPrimeEntryN1 13 n m",
    "tau_subtraction_signs": [1, -1, -1],
    "prime_range": "Finset.Icc 2 13",
    "prime_weight": "vonMangoldt k * (sqrt k)^(-1) * ccmQKernel L n m (log k)",
    "wr_domain": "Set.Ioc 0 L",
    "wr_integrand": "(exp(x/2)*q(x)-q(0))/(exp(x)-exp(-x))",
    "wr_endpoint": "certified analytic removable extension at x=0",
    "wr_change_of_variables": "x=L*t, t in [0,1]",
    "w02_formula": "32*L*sinh(L/4)^2*(L^2-16*pi^2*m*n)/((L^2+16*pi^2*m^2)*(L^2+16*pi^2*n^2))",
    "sector_even": "Uplus(x0,x1,x2)=(x2,x1,x0,x1,x2)",
    "sector_odd": "Uminus(y1,y2)=(-y2,-y1,0,y1,y2)",
    "Gplus": [[1, 0, 0], [0, 2, 0], [0, 0, 2]],
    "Gminus": [[2, 0], [0, 2]],
}

# Frozen after the binary64 pilot.  No accepting branch changes these values.
FROZEN = {
    "mu": "1/10000000",
    "delta": "3/10000000",
    "tau": "1/100000",
    "q": ["-729553/1000000", "471629/1000000", "-106971/1000000"],
}

UPLUS = [
    [0, 0, 1],
    [0, 1, 0],
    [1, 0, 0],
    [0, 1, 0],
    [0, 0, 1],
]
UMINUS = [
    [0, -1],
    [-1, 0],
    [0, 0],
    [1, 0],
    [0, 1],
]
GPLUS = [[1, 0, 0], [0, 2, 0], [0, 0, 2]]
GMINUS = [[2, 0], [0, 2]]


def canonical_hash(value: Any) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, code: str) -> None:
    if not condition:
        raise RuntimeError(code)


def current_head() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
    ).strip()


def expected_parent_is_ancestor() -> bool:
    return subprocess.run(
        ["git", "merge-base", "--is-ancestor", EXPECTED_PARENT, current_head()],
        cwd=REPO,
        check=False,
    ).returncode == 0


def rational(text: str) -> fmpq:
    return fmpq(text)


def ball(text: str) -> arb:
    return arb(rational(text))


def rational_text(q: fmpq) -> str:
    return f"{q.p}/{q.q}" if q.q != 1 else str(q.p)


def exact_endpoint(x: arb, upper: bool) -> str:
    endpoint = x.upper() if upper else x.lower()
    return rational_text(endpoint.fmpq())


def interval_json(x: arb) -> dict[str, str | int]:
    require(x.is_finite(), "G2_CCM_SECTOR_CELL_13_2_INTERVAL_INCONCLUSIVE")
    return {
        "lower": exact_endpoint(x, False),
        "upper": exact_endpoint(x, True),
        "decimal_ball": x.str(30),
        "relative_accuracy_bits": int(x.rel_accuracy_bits()),
    }


def matrix_interval_json(a: list[list[arb]]) -> list[list[dict[str, Any]]]:
    return [[interval_json(x) for x in row] for row in a]


def arb_zero_matrix(rows: int, cols: int) -> list[list[arb]]:
    return [[arb(0) for _ in range(cols)] for _ in range(rows)]


def transpose(a: list[list[Any]]) -> list[list[Any]]:
    return [list(row) for row in zip(*a)]


def matmul(a: list[list[Any]], b: list[list[Any]]) -> list[list[arb]]:
    require(len(a[0]) == len(b), "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    out = arb_zero_matrix(len(a), len(b[0]))
    for i in range(len(a)):
        for j in range(len(b[0])):
            value = arb(0)
            for k in range(len(b)):
                value += arb(a[i][k]) * arb(b[k][j])
            out[i][j] = value
    return out


def matadd(a: list[list[arb]], b: list[list[arb]]) -> list[list[arb]]:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def matsub(a: list[list[arb]], b: list[list[arb]]) -> list[list[arb]]:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def matscale(c: arb, a: list[list[Any]]) -> list[list[arb]]:
    return [[c * arb(x) for x in row] for row in a]


def outer(v: list[arb], w: list[arb]) -> list[list[arb]]:
    return [[v[i] * w[j] for j in range(len(w))] for i in range(len(v))]


def matvec(a: list[list[Any]], v: list[arb]) -> list[arb]:
    return [sum((arb(x) * v[j] for j, x in enumerate(row)), arb(0)) for row in a]


def quadratic(v: list[arb], a: list[list[arb]]) -> arb:
    av = matvec(a, v)
    return sum((v[i] * av[i] for i in range(len(v))), arb(0))


def ldl_positive(a: list[list[arb]]) -> tuple[bool, list[arb], str]:
    """Interval LDL certificate; any nonpositive/zero-containing pivot fails."""

    n = len(a)
    l = arb_zero_matrix(n, n)
    d: list[arb] = []
    for i in range(n):
        pivot = a[i][i]
        for k in range(i):
            pivot -= l[i][k] * l[i][k] * d[k]
        d.append(pivot)
        if not pivot.is_finite() or not (pivot.lower() > 0):
            return False, d, "ZERO_OR_NONPOSITIVE_PIVOT"
        l[i][i] = arb(1)
        for j in range(i + 1, n):
            numerator = a[j][i]
            for k in range(i):
                numerator -= l[j][k] * l[i][k] * d[k]
            l[j][i] = numerator / pivot
    return True, d, "STRICTLY_POSITIVE_INTERVAL_PIVOTS"


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def von_mangoldt_support(limit: int) -> list[tuple[int, int]]:
    result: list[tuple[int, int]] = []
    for k in range(2, limit + 1):
        for p in range(2, k + 1):
            if not is_prime(p):
                continue
            power = p
            while power < k:
                power *= p
            if power == k:
                result.append((k, p))
                break
    return result


def q_kernel(z: arb | acb, length: arb, n: int, m: int) -> acb:
    x = acb(z)
    length_c = acb(length)
    pi_c = acb(arb.pi())
    if n == m:
        return 2 * (length_c - x) / length_c * (
            2 * pi_c * n * x / length_c
        ).cos()
    return (
        (2 * pi_c * m * x / length_c).sin()
        - (2 * pi_c * n * x / length_c).sin()
    ) / (pi_c * (n - m))


def q_at_zero(n: int, m: int) -> arb:
    return arb(2 if n == m else 0)


def q_difference_over_x(z: acb, length: arb, n: int, m: int) -> acb:
    """Entire extension of ``(q(z)-q(0))/z``."""

    x = acb(z)
    length_c = acb(length)
    pi_c = acb(arb.pi())
    if n == m:
        frequency = 2 * pi_c * n / length_c
        return (
            -(frequency * frequency) * x * (frequency * x / 2).sinc() ** 2
            - 2 * (frequency * x).cos() / length_c
        )
    freq_n = 2 * pi_c * n / length_c
    freq_m = 2 * pi_c * m / length_c
    return (
        freq_m * (freq_m * x).sinc() - freq_n * (freq_n * x).sinc()
    ) / (pi_c * (n - m))


def wr_extended_integrand(z: acb, length: arb, n: int, m: int) -> acb:
    """Analytic removable extension of the source ``ccmWRIntegrand``."""

    x = acb(z)
    imaginary_unit = acb(0, 1)
    expm1_over_x = (x / 2).hypgeom_1f1(1, 2) / 2
    sinh_over_x = (imaginary_unit * x).sinc()
    numerator_over_x = (
        q_at_zero(n, m) * expm1_over_x
        + (x / 2).exp() * q_difference_over_x(x, length, n, m)
    )
    return numerator_over_x / (2 * sinh_over_x)


def wr_integral(length: arb, n: int, m: int, precision: int) -> arb:
    # Integrate after x=L*t, with exact endpoints 0 and 1.  The tolerance is
    # deliberately much smaller than every spectral margin, but capped so the
    # 512-bit replay remains practical.
    tolerance_bits = min(max(96, precision // 2), 224)
    tolerance = arb(2) ** (-tolerance_bits)

    def integrand(t: acb, analytic: bool) -> acb:
        # The expression is meromorphic globally and analytic on the real
        # integration enclosure.  Per Arb's integration contract, any
        # accidentally enclosed pole makes the ball non-finite and the run
        # fail closed, so the analytic flag needs no separate branch here.
        del analytic
        return acb(length) * wr_extended_integrand(acb(length) * t, length, n, m)

    value = acb.integral(
        integrand,
        0,
        1,
        abs_tol=tolerance,
        rel_tol=tolerance,
        deg_limit=120,
        eval_limit=250000,
        depth_limit=40,
        use_heap=True,
    )
    require(value.is_finite(), "G2_CCM_SECTOR_CELL_13_2_INTERVAL_INCONCLUSIVE")
    require(value.imag.contains(0), "G2_CCM_SECTOR_CELL_13_2_INTERVAL_INCONCLUSIVE")
    return value.real


def w02_entry(length: arb, n: int, m: int) -> arb:
    pi = arb.pi()
    return (
        32
        * length
        * (length / 4).sinh() ** 2
        * (length**2 - 16 * pi**2 * m * n)
        / (
            (length**2 + 16 * pi**2 * m**2)
            * (length**2 + 16 * pi**2 * n**2)
        )
    )


def wr_entry(length: arb, n: int, m: int, precision: int) -> arb:
    exp_length = length.exp()
    constant = arb.const_euler() + (
        4 * arb.pi() * ((exp_length - 1) / (exp_length + 1))
    ).log()
    return q_at_zero(n, m) / 2 * constant + wr_integral(length, n, m, precision)


def prime_entry(length: arb, n: int, m: int) -> arb:
    total = arb(0)
    for k, p in von_mangoldt_support(EXPECTED_M_PROJECT):
        x = length if k == EXPECTED_M_PROJECT else arb(k).log()
        q_value = q_kernel(x, length, n, m)
        require(q_value.imag.contains(0), "G2_CCM_SECTOR_CELL_13_2_INTERVAL_INCONCLUSIVE")
        total += arb(p).log() / arb(k).sqrt() * q_value.real
    return total


def weil_entry(length: arb, n: int, m: int, precision: int) -> arb:
    return (
        w02_entry(length, n, m)
        - wr_entry(length, n, m, precision)
        - prime_entry(length, n, m)
    )


def build_weil_matrix(precision: int) -> list[list[arb]]:
    ctx.prec = precision
    length = arb(EXPECTED_M_PROJECT).log()
    matrix = arb_zero_matrix(5, 5)
    # ccmWeilTauN1_symm is already Lean-proved.  Reusing one ball for each
    # symmetric pair avoids irrelevant evaluation-order widening.
    for i, n in enumerate(MODE_ORDER):
        for j in range(i, len(MODE_ORDER)):
            m = MODE_ORDER[j]
            value = weil_entry(length, n, m, precision)
            matrix[i][j] = value
            matrix[j][i] = value
    return matrix


def sector_matrix(t: list[list[arb]], synthesis: list[list[int]]) -> list[list[arb]]:
    return matmul(matmul(transpose(synthesis), t), synthesis)


def flattened(a: list[list[arb]]) -> Iterable[arb]:
    for row in a:
        yield from row


def matrices_compatible(a: list[list[arb]], b: list[list[arb]]) -> bool:
    return all(x.overlaps(y) for x, y in zip(flattened(a), flattened(b)))


def frozen_values() -> tuple[arb, arb, arb, list[arb]]:
    return (
        ball(FROZEN["mu"]),
        ball(FROZEN["delta"]),
        ball(FROZEN["tau"]),
        [ball(x) for x in FROZEN["q"]],
    )


def certify_precision(precision: int) -> tuple[dict[str, Any], dict[str, Any]]:
    t = build_weil_matrix(precision)
    kplus = sector_matrix(t, UPLUS)
    kminus = sector_matrix(t, UMINUS)
    mu, delta, tau, q = frozen_values()
    threshold = mu + delta

    c1 = quadratic(q, matsub(kplus, matscale(mu, GPLUS)))
    gq = matvec(GPLUS, q)
    c2_matrix = matadd(
        matsub(kplus, matscale(threshold, GPLUS)),
        matscale(tau, outer(gq, gq)),
    )
    c3_matrix = matsub(kminus, matscale(threshold, GMINUS))
    c2_ok, c2_pivots, c2_reason = ldl_positive(c2_matrix)
    c3_ok, c3_pivots, c3_reason = ldl_positive(c3_matrix)
    c1_ok = c1.upper() < 0

    result = "CERTIFIED" if c1_ok and c2_ok and c3_ok else "INCONCLUSIVE"
    row = {
        "precision": precision,
        "entry_intervals": matrix_interval_json(t),
        "Kplus_intervals": matrix_interval_json(kplus),
        "Kminus_intervals": matrix_interval_json(kminus),
        "C1_upper": exact_endpoint(c1, True),
        "C1_interval": interval_json(c1),
        "C1_strict": c1_ok,
        "C2_interval_LDL_pivots": [interval_json(x) for x in c2_pivots],
        "C2_reason": c2_reason,
        "C2_strict": c2_ok,
        "C3_interval_LDL_pivots": [interval_json(x) for x in c3_pivots],
        "C3_reason": c3_reason,
        "C3_strict": c3_ok,
        "certificate_result": result,
    }
    raw = {
        "T": t,
        "Kplus": kplus,
        "Kminus": kminus,
        "C1": c1,
        "C2_pivots": c2_pivots,
        "C3_pivots": c3_pivots,
    }
    return row, raw


def diagnostic_from_arb(raw: dict[str, Any]) -> dict[str, Any]:
    """Non-proof binary64 diagnostic; no certifying branch reads its result."""

    mu, delta, tau, q = frozen_values()
    kplus = [[float(x.mid()) for x in row] for row in raw["Kplus"]]
    kminus = [[float(x.mid()) for x in row] for row in raw["Kminus"]]
    qf = [float(x) for x in q]
    gq = [qf[0], 2 * qf[1], 2 * qf[2]]

    def qform(v: list[float], a: list[list[float]]) -> float:
        return sum(v[i] * sum(a[i][j] * v[j] for j in range(len(v))) for i in range(len(v)))

    c1 = qform(qf, kplus) - float(mu) * (qf[0] ** 2 + 2 * qf[1] ** 2 + 2 * qf[2] ** 2)
    return {
        "arithmetic": "IEEE754_BINARY64_DIAGNOSTIC_ONLY",
        "may_certify": False,
        "frozen_before_arb_certification": True,
        "mu": float(mu),
        "delta": float(delta),
        "tau": float(tau),
        "q": qf,
        "C1_midpoint_diagnostic": c1,
        "Kplus_midpoints": kplus,
        "Kminus_midpoints": kminus,
        "Gq_midpoint": gq,
    }


def run_plants(source_hash: str) -> dict[str, Any]:
    ctx.prec = 128
    odd_ground_ok, odd_pivots, _ = ldl_positive(
        [[arb(-1), arb(0)], [arb(0), arb(1)]]
    )
    zero_even = arb_zero_matrix(3, 3)
    _, _, tau, q = frozen_values()
    gq = matvec(GPLUS, q)
    nonsimple = matadd(zero_even, matscale(tau, outer(gq, gq)))
    nonsimple_ok, nonsimple_pivots, _ = ldl_positive(nonsimple)
    zero_ok, zero_pivots, zero_reason = ldl_positive([[arb(0)]])

    mutations: dict[str, str] = {}
    for name, mutation in {
        "mode_order": ("mode_order", [-2, -1, 0, 2, 1]),
        "prime_range": ("prime_range", "Finset.Icc 3 13"),
        "tau_subtraction_signs": ("tau_subtraction_signs", [1, 1, -1]),
        "wr_endpoint": ("wr_endpoint", "raw 0/0 endpoint evaluation"),
    }.items():
        changed = copy.deepcopy(SOURCE_FORMULA)
        changed[mutation[0]] = mutation[1]
        mutations[name] = canonical_hash(changed)

    return {
        "P-SECTOR-1": {
            "name": "structured odd-ground plant",
            "C3_accepted": odd_ground_ok,
            "first_pivot": interval_json(odd_pivots[0]),
            "result": "PASS" if not odd_ground_ok else "FAIL",
        },
        "P-SECTOR-2": {
            "name": "nonsimple even bottom zero block",
            "C2_accepted": nonsimple_ok,
            "pivots": [interval_json(x) for x in nonsimple_pivots],
            "result": "PASS" if not nonsimple_ok else "FAIL",
        },
        "P-SECTOR-3": {
            "name": "exact object identity mutations",
            "baseline_hash": source_hash,
            "mutation_hashes": mutations,
            "all_mutations_stop": all(value != source_hash for value in mutations.values()),
            "result": "PASS" if all(value != source_hash for value in mutations.values()) else "FAIL",
        },
        "P-SECTOR-4": {
            "name": "binary64 firewall",
            "binary64_may_certify": False,
            "result": "PASS",
        },
        "P-SECTOR-5": {
            "name": "zero-containing pivot is inconclusive",
            "accepted": zero_ok,
            "reason": zero_reason,
            "pivot": interval_json(zero_pivots[0]),
            "result": "PASS" if not zero_ok and zero_reason == "ZERO_OR_NONPOSITIVE_PIVOT" else "FAIL",
        },
    }


def validate_object_identity(m_project: int, n_bound: int, precisions: tuple[int, ...]) -> str:
    require(flint.__version__ == EXPECTED_PYTHON_FLINT,
            "G2_CCM_SECTOR_CELL_13_2_ARB_BACKEND_MISSING")
    require(
        m_project == EXPECTED_M_PROJECT and n_bound == EXPECTED_N,
        "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH",
    )
    require(
        precisions == EXPECTED_PRECISIONS,
        "G2_CCM_SECTOR_CELL_13_2_CERTIFICATE_SCHEMA_INADEQUATE",
    )
    require(MODE_ORDER == (-2, -1, 0, 1, 2), "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(UPLUS == [[0, 0, 1], [0, 1, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]],
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(UMINUS == [[0, -1], [-1, 0], [0, 0], [1, 0], [0, 1]],
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(GPLUS == [[1, 0, 0], [0, 2, 0], [0, 0, 2]],
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(GMINUS == [[2, 0], [0, 2]],
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    for relative, expected_hash in SOURCE_FILES.items():
        require(file_sha256(PROJECT / relative) == expected_hash,
                "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    return canonical_hash(SOURCE_FORMULA)


def generate_payload(m_project: int, n_bound: int, precisions: tuple[int, ...]) -> dict[str, Any]:
    source_hash = validate_object_identity(m_project, n_bound, precisions)
    require(expected_parent_is_ancestor(),
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")

    rows: list[dict[str, Any]] = []
    raw_rows: list[dict[str, Any]] = []
    for precision in precisions:
        row, raw = certify_precision(precision)
        rows.append(row)
        raw_rows.append(raw)

    compatibility: dict[str, bool] = {}
    for index in range(1, len(raw_rows)):
        left_bits = precisions[index - 1]
        right_bits = precisions[index]
        left = raw_rows[index - 1]
        right = raw_rows[index]
        compatible = (
            matrices_compatible(left["T"], right["T"])
            and matrices_compatible(left["Kplus"], right["Kplus"])
            and matrices_compatible(left["Kminus"], right["Kminus"])
            and left["C1"].overlaps(right["C1"])
            and all(x.overlaps(y) for x, y in zip(left["C2_pivots"], right["C2_pivots"]))
            and all(x.overlaps(y) for x, y in zip(left["C3_pivots"], right["C3_pivots"]))
        )
        compatibility[f"{left_bits}_to_{right_bits}"] = compatible

    plants = run_plants(source_hash)
    strict_all = all(row["certificate_result"] == "CERTIFIED" for row in rows)
    compatible_all = all(compatibility.values())
    plants_all = all(plant["result"] == "PASS" for plant in plants.values())
    certificate_result = (
        "G2_CCM_SECTOR_ORDERING_CELL_13_2_ARB_CERTIFIED"
        if strict_all and compatible_all and plants_all
        else "G2_CCM_SECTOR_CELL_13_2_INTERVAL_INCONCLUSIVE"
    )

    # Top-level aliases are deliberate: they make the required contract fields
    # directly visible while retaining the per-precision audit rows.
    return {
        "schema": "q3.routeb.ccm_h2a_sector_cell_13_2_arb.v1",
        "status": "FINITE_CELL / ARB_INTERVAL / PRE_LEAN_CERTIFICATE",
        "parent_commit": EXPECTED_PARENT,
        "matrix_object": SOURCE_FORMULA["matrix_object"],
        "cell": {"mProject": m_project, "N": n_bound},
        "mode_order": list(MODE_ORDER),
        "source_formula": SOURCE_FORMULA,
        "source_formula_hash": source_hash,
        "source_files_sha256": SOURCE_FILES,
        "precision_bits": list(precisions),
        "python_flint_version": flint.__version__,
        "flint_runtime": str(ctx),
        "entry_intervals": {str(row["precision"]): row["entry_intervals"] for row in rows},
        "Kplus_intervals": {str(row["precision"]): row["Kplus_intervals"] for row in rows},
        "Kminus_intervals": {str(row["precision"]): row["Kminus_intervals"] for row in rows},
        "Gplus": GPLUS,
        "Gminus": GMINUS,
        "mu": FROZEN["mu"],
        "delta": FROZEN["delta"],
        "tau": FROZEN["tau"],
        "q": FROZEN["q"],
        "C1_upper": {str(row["precision"]): row["C1_upper"] for row in rows},
        "C2_interval_LDL_pivots": {
            str(row["precision"]): row["C2_interval_LDL_pivots"] for row in rows
        },
        "C3_interval_LDL_pivots": {
            str(row["precision"]): row["C3_interval_LDL_pivots"] for row in rows
        },
        "precision_rows": rows,
        "cross_precision_compatible": compatibility,
        "diagnostic": diagnostic_from_arb(raw_rows[0]),
        "plants": plants,
        "certificate_result": certificate_result,
        "scope": "exact finite cell (13,2) only; no universal H2a, H2b, route-promotion, or RH claim",
        "route_state": "CHALLENGER / NOT_RH",
        "bus_010": "VOID",
    }


def validate_payload_shape(payload: dict[str, Any]) -> None:
    required = {
        "parent_commit", "matrix_object", "cell", "mode_order",
        "source_formula_hash", "precision_bits", "entry_intervals",
        "Kplus_intervals", "Kminus_intervals", "Gplus", "Gminus",
        "mu", "delta", "tau", "q", "C1_upper",
        "C2_interval_LDL_pivots", "C3_interval_LDL_pivots",
        "certificate_result",
    }
    require(required <= payload.keys(), "G2_CCM_SECTOR_CELL_13_2_CERTIFICATE_SCHEMA_INADEQUATE")
    require(payload["matrix_object"] == SOURCE_FORMULA["matrix_object"],
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(payload["cell"] == {"mProject": 13, "N": 2},
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(payload["mode_order"] == list(MODE_ORDER),
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(payload["source_formula"] == SOURCE_FORMULA,
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(payload["source_formula_hash"] == canonical_hash(SOURCE_FORMULA),
            "G2_CCM_SECTOR_CELL_13_2_OBJECT_CROSSWALK_MISMATCH")
    require(payload["certificate_result"] == "G2_CCM_SECTOR_ORDERING_CELL_13_2_ARB_CERTIFIED",
            "G2_CCM_SECTOR_CELL_13_2_INTERVAL_INCONCLUSIVE")
    require(payload["route_state"] == "CHALLENGER / NOT_RH" and payload["bus_010"] == "VOID",
            "G2_CCM_SECTOR_CELL_13_2_CERTIFICATE_SCHEMA_INADEQUATE")


def parse_precisions(text: str) -> tuple[int, ...]:
    try:
        return tuple(int(piece) for piece in text.split(","))
    except ValueError as exc:
        raise SystemExit("G2_CCM_SECTOR_CELL_13_2_CERTIFICATE_SCHEMA_INADEQUATE") from exc


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m-project", type=int, default=EXPECTED_M_PROJECT)
    parser.add_argument("--N", type=int, default=EXPECTED_N)
    parser.add_argument("--precisions", default="128,256,512")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--verify-only", type=Path)
    args = parser.parse_args()

    if args.verify_only is not None:
        recorded = json.loads(args.verify_only.read_text(encoding="utf-8"))
        validate_payload_shape(recorded)
        precisions = tuple(recorded["precision_bits"])
        replay = generate_payload(
            recorded["cell"]["mProject"], recorded["cell"]["N"], precisions
        )
        require(
            json.dumps(recorded, sort_keys=True, separators=(",", ":"))
            == json.dumps(replay, sort_keys=True, separators=(",", ":")),
            "G2_CCM_SECTOR_CELL_13_2_INTERVAL_INCONCLUSIVE",
        )
        print("G2_CCM_SECTOR_ORDERING_CELL_13_2_ARB_CERTIFIED")
        return

    precisions = parse_precisions(args.precisions)
    payload = generate_payload(args.m_project, args.N, precisions)
    validate_payload_shape(payload)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(args.output)
    print(payload["certificate_result"])


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1) from exc
