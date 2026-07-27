#!/usr/bin/env python3
"""Goal 022: high-precision adjudication of the canonical E_star candidates.

The finite prolate eigenpairs are rebuilt in arbitrary precision from the
normalized-even-Legendre tridiagonal.  A shifted tridiagonal inverse iteration
removes the float64 seed error.  E_star is then evaluated with the independent
centre Taylor recurrence of the prolate ODE.  The precision ladder is the
amended Proshka ladder

    p0 = max(100, ceil(-log10(scale_L2)) + 80),
    p0, p0 + 100, p0 + 200.

The old float64 eigensystem is used only as an eigenvalue/eigenvector seed.
It is never used in a reported E_star value.  The packet carries the computed
mu_j = lambda * J_j / c_j; mu is never replaced by one.

This is a numerical sign diagnostic, not a theorem.  It does not evaluate G3,
Fejer or the residual, does not mutate STATE, and does not create Bus 010.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import platform
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np
from scipy import linalg


REQUEST_DIR = Path(__file__).resolve().parent
GOAL = REQUEST_DIR / "022_candidate_adjudication.goal.md"
SOURCE_JSON = REQUEST_DIR / "E_STAR_FULL_WINDOW_CANONICAL.json"
SOURCE_CANDIDATES = (
    REQUEST_DIR / "E_STAR_FULL_WINDOW_CANONICAL_CANDIDATE_POSITIVE_RUNS.csv"
)
SOURCE_FINGERPRINT = (
    REQUEST_DIR / "E_STAR_FULL_WINDOW_CANONICAL_FINGERPRINT.csv"
)
SOURCE_MODE_LOCK = REQUEST_DIR / "PROLATE_SAME_MODE_LOCK.csv"

RESULT_JSON = REQUEST_DIR / "E_STAR_CANDIDATE_ADJUDICATION.json"
SUMMARY_CSV = REQUEST_DIR / "E_STAR_CANDIDATE_ADJUDICATION.csv"
POINTS_CSV = REQUEST_DIR / "E_STAR_CANDIDATE_ADJUDICATION_POINTS.csv"
FINGERPRINT_CSV = (
    REQUEST_DIR / "E_STAR_CANDIDATE_ADJUDICATION_FINGERPRINT.csv"
)

M_VALUES = (13, 53, 257)
MODE_COLUMNS = (0, 2)
CORE_POINTS = 17
GUARD_FRACTIONS = (mp.mpf(1) / 4, mp.mpf(1) / 2, mp.mpf(3) / 4)
# Stop before the centre recurrence globally enters its roundoff-driven
# growing solution.  The emitted last-term ratio remains the local judge:
# any point that has not reached a decreasing tail is classified STILL_FLOOR.
TAYLOR_TERMS = {13: 600, 53: 1400, 257: 5500}
FINGERPRINT_T = ("0", "0.25", "0.5", "0.75")
LAST_TERM_COUNT = 16


@dataclass
class ModeData:
    column: int
    characteristic: mp.mpf
    eigenvector: list[mp.mpf]
    degrees: list[int]
    finite_residual: mp.mpf
    infinite_tail_residual: mp.mpf
    gap_lower_estimate: mp.mpf
    center_t: mp.mpf
    integral_t: mp.mpf
    mu: mp.mpf
    endpoint_x: mp.mpf
    taylor_x: list[mp.mpf]


@dataclass
class EvalPoint:
    record_id: str
    role: str
    u: mp.mpf
    count: int
    a2: mp.mpf
    endpoint_half: bool
    acc: mp.mpf
    a_power: mp.mpf
    last_terms: list[mp.mpf]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mp_text(value: mp.mpf, digits: int = 80) -> str:
    if not mp.isfinite(value):
        return str(value)
    return mp.nstr(value, digits, strip_zeros=False)


def log10_abs(value: mp.mpf) -> mp.mpf:
    if value == 0:
        return mp.ninf
    return mp.log10(abs(value))


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise RuntimeError(f"EMPTY_OUTPUT:{path}")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=list(rows[0]),
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(rows)


def precision_ladders() -> dict[int, tuple[int, int, int]]:
    scales: dict[int, list[float]] = {m: [] for m in M_VALUES}
    with SOURCE_MODE_LOCK.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            m = int(row["m"])
            if m in scales:
                scales[m].append(float(row["scale_L2_log10"]))
    ladders: dict[int, tuple[int, int, int]] = {}
    for m in M_VALUES:
        if len(scales[m]) != 2:
            raise RuntimeError(f"MISSING_SCALE_L2_ROWS:{m}:{len(scales[m])}")
        p0 = max(100, math.ceil(max(-x for x in scales[m])) + 80)
        ladders[m] = (p0, p0 + 100, p0 + 200)
    return ladders


def x2_entries(n: int, c: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    diagonal = mp.mpf(n + 1) ** 2 / (
        mp.mpf(2 * n + 1) * (2 * n + 3)
    )
    if n:
        diagonal += mp.mpf(n) ** 2 / (
            mp.mpf(2 * n + 1) * (2 * n - 1)
        )
    off = (
        c
        * c
        * mp.mpf(n + 1)
        * (n + 2)
        / (mp.mpf(2 * n + 1) * (2 * n + 3))
        * mp.sqrt(mp.mpf(2 * n + 1) / (2 * n + 5))
    )
    return diagonal, off


def tridiagonal(
    m: int, degree: int
) -> tuple[list[int], list[mp.mpf], list[mp.mpf], mp.mpf]:
    degrees = list(range(0, degree + 1, 2))
    c = 2 * mp.pi * m
    diagonal: list[mp.mpf] = []
    off: list[mp.mpf] = []
    for n in degrees:
        x2_diag, _ = x2_entries(n, c)
        diagonal.append(mp.mpf(n) * (n + 1) + c * c * x2_diag)
    for n in degrees[:-1]:
        _, x2_off = x2_entries(n, c)
        off.append(x2_off)
    return degrees, diagonal, off, c


def solve_shifted_tridiagonal(
    diagonal: list[mp.mpf],
    off: list[mp.mpf],
    shift: mp.mpf,
    rhs: list[mp.mpf],
) -> list[mp.mpf]:
    n = len(diagonal)
    cprime = [mp.mpf(0)] * (n - 1)
    dprime = [mp.mpf(0)] * n
    denominator = diagonal[0] - shift
    cprime[0] = off[0] / denominator
    dprime[0] = rhs[0] / denominator
    for i in range(1, n):
        denominator = (
            diagonal[i] - shift - off[i - 1] * cprime[i - 1]
        )
        if i < n - 1:
            cprime[i] = off[i] / denominator
        dprime[i] = (
            rhs[i] - off[i - 1] * dprime[i - 1]
        ) / denominator
    result = [mp.mpf(0)] * n
    result[-1] = dprime[-1]
    for i in range(n - 2, -1, -1):
        result[i] = dprime[i] - cprime[i] * result[i + 1]
    return result


def matvec(
    diagonal: list[mp.mpf],
    off: list[mp.mpf],
    vector: list[mp.mpf],
) -> list[mp.mpf]:
    n = len(diagonal)
    return [
        diagonal[i] * vector[i]
        + (off[i - 1] * vector[i - 1] if i else 0)
        + (off[i] * vector[i + 1] if i + 1 < n else 0)
        for i in range(n)
    ]


def refined_eigenpair(
    m: int,
    column: int,
    degree: int,
    dps: int,
) -> tuple[
    list[int],
    mp.mpf,
    list[mp.mpf],
    mp.mpf,
    mp.mpf,
    mp.mpf,
    mp.mpf,
]:
    degrees, diagonal, off, c = tridiagonal(m, degree)
    diag_float = np.asarray([float(x) for x in diagonal])
    off_float = np.asarray([float(x) for x in off])
    seeds, seed_vectors = linalg.eigh_tridiagonal(
        diag_float,
        off_float,
        select="i",
        select_range=(0, 4),
        check_finite=True,
    )
    eigenvalue = mp.mpf(str(seeds[column]))
    vector = [mp.mpf(str(x)) for x in seed_vectors[:, column]]
    target = mp.power(10, -dps + 20)
    residual = mp.inf
    for _ in range(8):
        vector = solve_shifted_tridiagonal(
            diagonal, off, eigenvalue, vector
        )
        norm = mp.sqrt(mp.fsum(x * x for x in vector))
        vector = [x / norm for x in vector]
        if vector[0] < 0:
            vector = [-x for x in vector]
        image = matvec(diagonal, off, vector)
        new_eigenvalue = mp.fsum(
            vector[i] * image[i] for i in range(len(vector))
        )
        residual = mp.sqrt(
            mp.fsum(
                (image[i] - new_eigenvalue * vector[i]) ** 2
                for i in range(len(vector))
            )
        )
        eigenvalue = new_eigenvalue
        if residual < target:
            break
    if residual >= target:
        raise RuntimeError(
            f"MP_EIGENPAIR_DID_NOT_CONVERGE:{m}:{column}:{dps}:"
            f"{mp_text(residual, 30)}"
        )
    _, next_off = x2_entries(degree, c)
    tail_residual = abs(next_off * vector[-1])
    neighbor_gaps = [
        abs(float(seeds[column]) - float(seeds[j]))
        for j in range(5)
        if j != column
    ]
    gap_lower = mp.mpf(str(min(neighbor_gaps) / 2))
    return (
        degrees,
        eigenvalue,
        vector,
        residual,
        tail_residual,
        gap_lower,
        c,
    )


def legendre_center(
    vector: list[mp.mpf], degrees: list[int]
) -> mp.mpf:
    p_even_zero = mp.mpf(1)
    terms: list[mp.mpf] = []
    for i, n in enumerate(degrees):
        terms.append(
            vector[i]
            * mp.sqrt(mp.mpf(2 * n + 1) / 2)
            * p_even_zero
        )
        p_even_zero = (
            -p_even_zero * mp.mpf(2 * i + 1) / (2 * i + 2)
        )
    return mp.fsum(terms)


def legendre_value_x(
    vector: list[mp.mpf],
    degrees: list[int],
    t: mp.mpf,
    lam: mp.mpf,
) -> mp.mpf:
    if t == 1:
        return mp.fsum(
            vector[i] * mp.sqrt(mp.mpf(2 * n + 1) / (2 * lam))
            for i, n in enumerate(degrees)
        )
    p_prev = mp.mpf(1)
    p_current = t
    terms = [
        vector[0] * mp.sqrt(mp.mpf(1) / (2 * lam)) * p_prev
    ]
    even_index = 1
    for n in range(1, degrees[-1]):
        p_next = (
            (2 * n + 1) * t * p_current - n * p_prev
        ) / (n + 1)
        if (n + 1) % 2 == 0:
            degree = n + 1
            terms.append(
                vector[even_index]
                * mp.sqrt(mp.mpf(2 * degree + 1) / (2 * lam))
                * p_next
            )
            even_index += 1
        p_prev, p_current = p_current, p_next
    return mp.fsum(terms)


def build_mode(
    m: int,
    column: int,
    degree: int,
    dps: int,
    taylor_terms: int,
) -> ModeData:
    (
        degrees,
        characteristic,
        vector,
        finite_residual,
        tail_residual,
        gap_lower,
        c,
    ) = refined_eigenpair(m, column, degree, dps)
    lam = mp.sqrt(m)
    center_t = legendre_center(vector, degrees)
    integral_t = mp.sqrt(2) * vector[0]
    mu = lam * integral_t / center_t
    endpoint_x = legendre_value_x(vector, degrees, mp.mpf(1), lam)
    center_x = center_t / mp.sqrt(lam)
    taylor = [center_x]
    previous2 = mp.mpf(0)
    current = center_x
    for k in range(0, 2 * (taylor_terms - 1), 2):
        following = (
            (mp.mpf(k) * (k + 1) - characteristic) * current
            + c * c * previous2
        ) / ((k + 2) * (k + 1))
        taylor.append(following)
        previous2, current = current, following
    return ModeData(
        column=column,
        characteristic=characteristic,
        eigenvector=vector,
        degrees=degrees,
        finite_residual=finite_residual,
        infinite_tail_residual=tail_residual,
        gap_lower_estimate=gap_lower,
        center_t=center_t,
        integral_t=integral_t,
        mu=mu,
        endpoint_x=endpoint_x,
        taylor_x=taylor,
    )


def packet_data(
    m: int, dps: int, taylor_terms: int
) -> tuple[list[mp.mpf], mp.mpf, list[ModeData], mp.mpf]:
    degree = max(180, 20 * m)
    modes = [
        build_mode(m, column, degree, dps, taylor_terms)
        for column in MODE_COLUMNS
    ]
    mode0, mode4 = modes
    j0 = mode0.integral_t
    j4 = mode4.integral_t
    denominator = mp.sqrt(j0 * j0 + j4 * j4)
    packet_taylor = [
        (j4 * mode0.taylor_x[k] - j0 * mode4.taylor_x[k])
        / denominator
        for k in range(taylor_terms)
    ]
    packet_endpoint = (
        j4 * mode0.endpoint_x - j0 * mode4.endpoint_x
    ) / denominator
    representation_floor = max(
        (
            mode.finite_residual + mode.infinite_tail_residual
        )
        / mode.gap_lower_estimate
        * (degree + 1)
        for mode in modes
    )
    return packet_taylor, packet_endpoint, modes, representation_floor


def packet_legendre_value(
    m: int, modes: list[ModeData], t: mp.mpf
) -> mp.mpf:
    lam = mp.sqrt(m)
    mode0, mode4 = modes
    denominator = mp.sqrt(
        mode0.integral_t**2 + mode4.integral_t**2
    )
    value0 = legendre_value_x(
        mode0.eigenvector, mode0.degrees, t, lam
    )
    value4 = legendre_value_x(
        mode4.eigenvector, mode4.degrees, t, lam
    )
    return (
        mode4.integral_t * value0 - mode0.integral_t * value4
    ) / denominator


def taylor_value(coefficients: list[mp.mpf], t: mp.mpf) -> mp.mpf:
    t2 = t * t
    value = mp.mpf(0)
    for coefficient in reversed(coefficients):
        value = value * t2 + coefficient
    return value


def source_records() -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    with SOURCE_CANDIDATES.open(newline="", encoding="utf-8") as handle:
        for index, row in enumerate(csv.DictReader(handle), start=1):
            records.append(
                {
                    "record_id": f"C{index:03d}",
                    "source_kind": "candidate",
                    "m": int(row["m"]),
                    "r": int(row["r"]),
                    "u_left": row["u_left_sample"],
                    "u_right": row["u_right_sample"],
                    "source_sample_count": int(row["sample_count"]),
                    "source_min_log10_margin": row["min_log10_margin"],
                    "source_max_log10_value": row["max_log10_value"],
                }
            )
    source = json.loads(SOURCE_JSON.read_text(encoding="utf-8"))
    zero_index = 0
    for m_text, levels in source["results"].items():
        for level in levels:
            for band in level["bands"]:
                for sample in band["samples"]:
                    if int(sample["sign"]) != 0:
                        continue
                    zero_index += 1
                    records.append(
                        {
                            "record_id": f"Z{zero_index:03d}",
                            "source_kind": "float64_zero",
                            "m": int(m_text),
                            "r": int(band["r"]),
                            "u_left": sample["u"],
                            "u_right": sample["u"],
                            "source_sample_count": 1,
                            "source_min_log10_margin": "-inf",
                            "source_max_log10_value": "-inf",
                        }
                    )
    if len(records) != 70 or zero_index != 2:
        raise RuntimeError(
            f"SOURCE_RECORD_COUNT_MISMATCH:{len(records)}:{zero_index}"
        )
    return records


def open_grid(record: dict[str, Any]) -> list[tuple[str, mp.mpf]]:
    m = int(record["m"])
    r = int(record["r"])
    lam = mp.sqrt(m)
    left_tooth = lam / (r + 1)
    right_tooth = lam / r
    source_left = mp.mpf(record["u_left"])
    source_right = mp.mpf(record["u_right"])
    if record["source_kind"] == "float64_zero":
        step = (right_tooth - left_tooth) / 66
        source_left = max(left_tooth, source_left - 2 * step)
        source_right = min(right_tooth, source_right + 2 * step)
        core_role = "zero_local"
    else:
        core_role = "candidate"
    raw: list[tuple[str, mp.mpf]] = []
    for fraction in GUARD_FRACTIONS:
        raw.append(
            (
                "left_guard",
                left_tooth + fraction * (source_left - left_tooth),
            )
        )
    if source_left == source_right:
        raw.append((core_role, source_left))
    else:
        for index in range(CORE_POINTS):
            fraction = mp.mpf(index) / (CORE_POINTS - 1)
            raw.append(
                (
                    core_role,
                    source_left
                    + fraction * (source_right - source_left),
                )
            )
    for fraction in GUARD_FRACTIONS:
        raw.append(
            (
                "right_guard",
                source_right
                + fraction * (right_tooth - source_right),
            )
        )
    seen: set[str] = set()
    output: list[tuple[str, mp.mpf]] = []
    for role, value in raw:
        key = mp.nstr(value, 80)
        if key not in seen and left_tooth < value < right_tooth:
            seen.add(key)
            output.append((role, value))
    return output


def build_eval_points(
    records: list[dict[str, Any]], m: int
) -> list[EvalPoint]:
    lam = mp.sqrt(m)
    points: list[EvalPoint] = []
    for record in records:
        if int(record["m"]) != m:
            continue
        r = int(record["r"])
        for role, u in open_grid(record):
            points.append(
                EvalPoint(
                    record_id=record["record_id"],
                    role=role,
                    u=u,
                    count=r,
                    a2=(u / lam) ** 2,
                    endpoint_half=False,
                    acc=mp.mpf(0),
                    a_power=mp.mpf(1),
                    last_terms=[],
                )
            )
        points.extend(
            [
                EvalPoint(
                    record_id=record["record_id"],
                    role="left_tooth",
                    u=lam / (r + 1),
                    count=r,
                    a2=mp.mpf(1) / (r + 1) ** 2,
                    endpoint_half=True,
                    acc=mp.mpf(0),
                    a_power=mp.mpf(1),
                    last_terms=[],
                ),
                EvalPoint(
                    record_id=record["record_id"],
                    role="right_tooth",
                    u=lam / r,
                    count=r - 1,
                    a2=mp.mpf(1) / r**2,
                    endpoint_half=True,
                    acc=mp.mpf(0),
                    a_power=mp.mpf(1),
                    last_terms=[],
                ),
            ]
        )
    return points


def tail_bound(last_terms: list[mp.mpf]) -> mp.mpf:
    if len(last_terms) < 4:
        return mp.inf
    absolute = [abs(x) for x in last_terms]
    ratios = [
        absolute[i] / absolute[i - 1]
        for i in range(1, len(absolute))
        if absolute[i - 1] != 0
    ]
    if not ratios:
        return mp.mpf(0)
    q = max(ratios[-8:])
    if q >= 1:
        return mp.inf
    return absolute[-1] / (1 - q)


def evaluate_level(
    m: int,
    dps: int,
    records: list[dict[str, Any]],
) -> tuple[
    list[dict[str, Any]],
    dict[str, Any],
    list[dict[str, Any]],
]:
    taylor_terms = TAYLOR_TERMS[m]
    with mp.workdps(dps):
        print(
            f"[022] m={m} dps={dps} building mp eigenpairs "
            f"degree={max(180, 20*m)} K={taylor_terms}",
            flush=True,
        )
        coefficients, endpoint, modes, representation_floor = packet_data(
            m, dps, taylor_terms
        )
        fingerprint_rows: list[dict[str, Any]] = []
        fingerprint_error = mp.mpf(0)
        for label in FINGERPRINT_T:
            t = mp.mpf(label)
            legendre = packet_legendre_value(m, modes, t)
            series = taylor_value(coefficients, t)
            difference = abs(legendre - series)
            fingerprint_error = max(fingerprint_error, difference)
            fingerprint_rows.append(
                {
                    "m": m,
                    "dps": dps,
                    "t_label": label,
                    "legendre_value": mp_text(legendre),
                    "taylor_value": mp_text(series),
                    "absolute_difference": mp_text(difference),
                    "log10_absolute_difference": mp_text(
                        log10_abs(difference), 40
                    ),
                }
            )

        points = build_eval_points(records, m)
        counts = sorted({point.count for point in points if point.count > 0})
        max_count = max(counts)
        squares = [n * n for n in range(1, max_count + 1)]
        powers = [1] * max_count
        count_set = set(counts)
        for k, coefficient in enumerate(coefficients):
            running = 0
            sums: dict[int, int] = {0: 0}
            for index in range(max_count):
                running += powers[index]
                count = index + 1
                if count in count_set:
                    sums[count] = running
                powers[index] *= squares[index]
            weighted_coefficients = {
                count: coefficient * power_sum
                for count, power_sum in sums.items()
            }
            keep_term = k >= len(coefficients) - LAST_TERM_COUNT
            for point in points:
                term = weighted_coefficients[point.count] * point.a_power
                point.acc += term
                point.a_power *= point.a2
                if keep_term:
                    point.last_terms.append(term)
            if k and k % 1000 == 0:
                print(
                    f"[022] m={m} dps={dps} Taylor {k}/"
                    f"{len(coefficients)}",
                    flush=True,
                )

        point_rows: list[dict[str, Any]] = []
        max_estimated_error = mp.mpf(0)
        for point in points:
            if point.endpoint_half:
                point.acc += endpoint / 2
            value = mp.sqrt(point.u) * point.acc
            local_tail = mp.sqrt(point.u) * tail_bound(point.last_terms)
            mode_floor = (
                mp.sqrt(point.u)
                * max(point.count, 1)
                * 8
                * max(representation_floor, fingerprint_error)
            )
            estimated_error = local_tail + mode_floor
            max_estimated_error = max(
                max_estimated_error, estimated_error
            )
            point_rows.append(
                {
                    "record_id": point.record_id,
                    "m": m,
                    "dps": dps,
                    "role": point.role,
                    "u": mp_text(point.u, 50),
                    "sign": int(mp.sign(value)),
                    "value": mp_text(value),
                    "log10_abs": mp_text(log10_abs(value), 40),
                    "Taylor_tail_bound": mp_text(local_tail),
                    "mode_representation_error_estimate": mp_text(
                        mode_floor
                    ),
                    "total_error_estimate": mp_text(estimated_error),
                    "_value_mp": value,
                    "_error_mp": estimated_error,
                }
            )
        mode_rows = [
            {
                "column": mode.column,
                "characteristic": mp_text(mode.characteristic),
                "finite_residual": mp_text(mode.finite_residual),
                "infinite_tail_residual": mp_text(
                    mode.infinite_tail_residual
                ),
                "gap_lower_estimate": mp_text(mode.gap_lower_estimate),
                "center_t": mp_text(mode.center_t),
                "integral_t": mp_text(mode.integral_t),
                "mu=lambda*J/c": mp_text(mode.mu),
                "mu_minus_one": mp_text(mode.mu - 1),
                "endpoint_x": mp_text(mode.endpoint_x),
            }
            for mode in modes
        ]
        level_meta = {
            "m": m,
            "dps": dps,
            "degree": max(180, 20 * m),
            "Taylor_terms": taylor_terms,
            "representation_floor": mp_text(representation_floor),
            "fingerprint_error": mp_text(fingerprint_error),
            "max_estimated_error": mp_text(max_estimated_error),
            "modes": mode_rows,
        }
        return point_rows, level_meta, fingerprint_rows


def strip_internal(row: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in row.items() if not key.startswith("_")}


def classify_records(
    records: list[dict[str, Any]],
    point_rows: list[dict[str, Any]],
    ladders: dict[int, tuple[int, int, int]],
) -> list[dict[str, Any]]:
    by_record_level: dict[
        tuple[str, int], list[dict[str, Any]]
    ] = {}
    for row in point_rows:
        by_record_level.setdefault(
            (row["record_id"], int(row["dps"])), []
        ).append(row)
    output: list[dict[str, Any]] = []
    for record in records:
        record_id = record["record_id"]
        m = int(record["m"])
        levels = ladders[m]
        core_roles = (
            {"candidate"}
            if record["source_kind"] == "candidate"
            else {"zero_local"}
        )
        core_by_level = [
            [
                row
                for row in by_record_level[(record_id, dps)]
                if row["role"] in core_roles
            ]
            for dps in levels
        ]
        signs_by_level = [
            [int(row["sign"]) for row in rows]
            for rows in core_by_level
        ]
        final_values = [
            row["_value_mp"] for row in core_by_level[-1]
        ]
        final_margin = min(abs(value) for value in final_values)
        final_error = max(
            row["_error_mp"] for row in core_by_level[-1]
        )
        ladder_error = mp.mpf(0)
        for lower_rows, upper_rows in zip(
            core_by_level[:-1], core_by_level[1:]
        ):
            if len(lower_rows) != len(upper_rows):
                raise RuntimeError(
                    f"LADDER_GRID_MISMATCH:{record_id}"
                )
            ladder_error = max(
                ladder_error,
                max(
                    abs(
                        lower_rows[index]["_value_mp"]
                        - upper_rows[index]["_value_mp"]
                    )
                    for index in range(len(lower_rows))
                ),
            )
        total_error = max(final_error, ladder_error)
        negative = all(
            all(sign < 0 for sign in signs)
            for signs in signs_by_level
        )
        positive = all(
            all(sign > 0 for sign in signs)
            for signs in signs_by_level
        )
        margin_pass = final_margin > total_error
        if negative and margin_pass:
            classification = "NEGATIVE_CONFIRMED"
        elif positive and margin_pass:
            classification = "POSITIVE_CONFIRMED"
        else:
            classification = "STILL_FLOOR"
        tooth_rows = [
            row
            for row in by_record_level[(record_id, levels[-1])]
            if row["role"] in {"left_tooth", "right_tooth"}
        ]
        output.append(
            {
                **record,
                "p0": levels[0],
                "p1": levels[1],
                "p2": levels[2],
                "classification": classification,
                "final_min_margin": mp_text(final_margin),
                "final_min_log10_margin": mp_text(
                    log10_abs(final_margin), 40
                ),
                "final_error_estimate": mp_text(final_error),
                "ladder_error_estimate": mp_text(ladder_error),
                "decision_error_estimate": mp_text(total_error),
                "margin_over_error_orders": (
                    mp_text(
                        log10_abs(final_margin)
                        - log10_abs(total_error),
                        30,
                    )
                    if total_error != 0
                    else "inf"
                ),
                "left_tooth_sign_final": next(
                    int(row["sign"])
                    for row in tooth_rows
                    if row["role"] == "left_tooth"
                ),
                "right_tooth_sign_final": next(
                    int(row["sign"])
                    for row in tooth_rows
                    if row["role"] == "right_tooth"
                ),
                "core_point_count": len(core_by_level[-1]),
            }
        )
    return output


def fingerprint_crosscheck(
    computed: list[dict[str, Any]],
    ladders: dict[int, tuple[int, int, int]],
) -> list[dict[str, Any]]:
    source: dict[tuple[int, str], dict[str, str]] = {}
    with SOURCE_FINGERPRINT.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            if row["level"] == "P3" and row["t_label"] in FINGERPRINT_T:
                source[(int(row["m"]), row["t_label"])] = row
    output: list[dict[str, Any]] = []
    for row in computed:
        m = int(row["m"])
        if int(row["dps"]) != ladders[m][-1]:
            continue
        old = source[(m, row["t_label"])]
        value = mp.mpf(row["legendre_value"])
        old_log = mp.mpf(old["log10_abs"])
        output.append(
            {
                **strip_internal(row),
                "source_021_sign": old["sign"],
                "source_021_log10_abs": old["log10_abs"],
                "computed_sign": int(mp.sign(value)),
                "computed_log10_abs": mp_text(log10_abs(value), 40),
                "absolute_log10_drift_vs_021_P3": mp_text(
                    abs(log10_abs(value) - old_log), 40
                ),
                "sign_match_021_P3": (
                    int(mp.sign(value)) == int(old["sign"])
                ),
            }
        )
    return output


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--m",
        nargs="*",
        type=int,
        choices=M_VALUES,
        help="optional diagnostic subset; final artifacts require all m",
    )
    parser.add_argument(
        "--no-write",
        action="store_true",
        help="run without writing canonical artifacts",
    )
    return parser.parse_args()


def run() -> dict[str, Any]:
    args = parse_args()
    selected = tuple(args.m) if args.m else M_VALUES
    records = source_records()
    ladders = precision_ladders()
    all_points: list[dict[str, Any]] = []
    level_meta: list[dict[str, Any]] = []
    fingerprints: list[dict[str, Any]] = []
    for m in selected:
        for dps in ladders[m]:
            rows, meta, fp_rows = evaluate_level(
                m, dps, records
            )
            all_points.extend(rows)
            level_meta.append(meta)
            fingerprints.extend(fp_rows)
    if selected != M_VALUES:
        payload = {
            "diagnostic_subset": selected,
            "point_rows": len(all_points),
            "level_meta": level_meta,
        }
        print(json.dumps(payload, indent=2))
        return payload

    summary_rows = classify_records(records, all_points, ladders)
    classifications = [row["classification"] for row in summary_rows]
    if any(value == "POSITIVE_CONFIRMED" for value in classifications):
        verdict = "ESTAR_PHASE_SIGN_KILLED_CANONICAL"
    elif all(value == "NEGATIVE_CONFIRMED" for value in classifications):
        verdict = "CANONICAL_CANDIDATES_ALL_NEGATIVE"
    else:
        verdict = "CANDIDATES_STILL_FLOOR"
    fingerprint_rows = fingerprint_crosscheck(fingerprints, ladders)
    payload = {
        "verdict": verdict,
        "epistemic_status": (
            "HIGH_PRECISION_GRID_DIAGNOSTIC_NOT_A_THEOREM_NOT_RH"
        ),
        "source": {
            "goal": str(GOAL),
            "goal_sha256": sha256(GOAL),
            "source_021_json": str(SOURCE_JSON),
            "source_021_json_sha256": sha256(SOURCE_JSON),
            "source_candidates": str(SOURCE_CANDIDATES),
            "source_candidates_sha256": sha256(SOURCE_CANDIDATES),
            "source_mode_lock": str(SOURCE_MODE_LOCK),
            "source_mode_lock_sha256": sha256(SOURCE_MODE_LOCK),
        },
        "protocol": {
            "precision_formula": (
                "p0=max(100,ceil(-log10(scale_L2_local))+80);"
                " p0,p0+100,p0+200"
            ),
            "precision_ladders": {
                str(m): ladders[m] for m in M_VALUES
            },
            "mode_backend": (
                "mp tridiagonal inverse iteration + prolate ODE "
                "centre Taylor recurrence"
            ),
            "independent_crosscheck": (
                "normalized Legendre series fingerprints"
            ),
            "packet_formula": (
                "(J4*phi0-J0*phi4)/"
                "(sqrt(lambda)*sqrt(J0^2+J4^2)); N0=N4=1"
            ),
            "mu_formula": "mu_j=lambda*J_j/c_j; never replaced by 1",
            "Taylor_terms": TAYLOR_TERMS,
            "candidate_core_points": CORE_POINTS,
            "guard_fractions_to_neighbor_teeth": [
                "1/4",
                "1/2",
                "3/4",
            ],
            "star_endpoint_weight": "1/2",
        },
        "counts": {
            "candidate_records": sum(
                row["source_kind"] == "candidate" for row in records
            ),
            "float64_zero_records": sum(
                row["source_kind"] == "float64_zero" for row in records
            ),
            "NEGATIVE_CONFIRMED": classifications.count(
                "NEGATIVE_CONFIRMED"
            ),
            "POSITIVE_CONFIRMED": classifications.count(
                "POSITIVE_CONFIRMED"
            ),
            "STILL_FLOOR": classifications.count("STILL_FLOOR"),
            "point_rows": len(all_points),
        },
        "level_meta": level_meta,
        "records": summary_rows,
        "fingerprint_crosscheck": fingerprint_rows,
        "guards": {
            "float64_in_reported_E_star_chain": False,
            "float64_seed_refined_away": True,
            "mu_forced_to_one": False,
            "mode_error_estimate_required": True,
            "margin_must_exceed_mode_error": True,
            "Fejer_evaluated": False,
            "residual_evaluated": False,
            "G3_evaluated": False,
            "STATE_mutated": False,
            "Bus_010_created": False,
        },
        "environment": {
            "python": platform.python_version(),
            "mpmath": mp.__version__,
            "numpy": np.__version__,
        },
    }
    if not args.no_write:
        write_csv(SUMMARY_CSV, summary_rows)
        write_csv(
            POINTS_CSV, [strip_internal(row) for row in all_points]
        )
        write_csv(FINGERPRINT_CSV, fingerprint_rows)
        RESULT_JSON.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    print(
        json.dumps(
            {
                "verdict": verdict,
                "counts": payload["counts"],
                "precision_ladders": payload["protocol"][
                    "precision_ladders"
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return payload


if __name__ == "__main__":
    run()
