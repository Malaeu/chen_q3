"""Exact periodic-character disk sums for the CF22 independent-P diagnostic.

The finite disk sum is exact and zero-extended on every prime dividing an
ideal row.  This module is a diagnostic helper; it does not alter or extend
the frozen CF22 pilot.
"""
from __future__ import annotations

import ctypes
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import hashlib
from math import gcd
from numbers import Integral
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
from typing import Any, Sequence


try:
    from .. import evaluate
except (ImportError, ValueError):
    _EXPERIMENT_DIR = Path(__file__).resolve().parents[1]
    if str(_EXPERIMENT_DIR) not in sys.path:
        sys.path.insert(0, str(_EXPERIMENT_DIR))
    import evaluate  # type: ignore[no-redef]


MAX_BOUND = 2 * 48 * 49**6
MAX_PERIOD_NORM = 1_000_000
_CPP_FILE = Path(__file__).with_name("periodic_counter.cpp")
_TABLE_CACHE_SIZE = 32


@dataclass(frozen=True)
class _Period:
    factors: tuple[tuple[evaluate.I, int], ...]
    h1: int
    h2: int
    b_hnf: int
    norm: int


@dataclass(frozen=True)
class _CharacterTable:
    h1: int
    h2: int
    b_hnf: int
    # Each byte stores an entry in {-2,-1,0,1,2} after adding 2.
    encoded: bytes


def _extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    """Return positive g,s,t with a*s+b*t=g=gcd(a,b)."""
    old_r, r = abs(a), abs(b)
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if a < 0:
        old_s = -old_s
    if b < 0:
        old_t = -old_t
    return old_r, old_s, old_t


def _lcm_factors(
    left: tuple[tuple[evaluate.I, int], ...],
    right: tuple[tuple[evaluate.I, int], ...],
) -> tuple[tuple[evaluate.I, int], ...]:
    exponents = dict(left)
    for prime, exponent in right:
        exponents[prime] = max(exponents.get(prime, 0), exponent)
    return tuple(sorted(exponents.items()))


def _principal_period(
    left: tuple[tuple[evaluate.I, int], ...],
    right: tuple[tuple[evaluate.I, int], ...],
) -> _Period:
    factors = _lcm_factors(left, right)
    period_norm = evaluate.ideal_norm(factors)
    if period_norm > MAX_PERIOD_NORM:
        raise ValueError(
            f"lcm ideal norm period {period_norm} exceeds explicit limit "
            f"{MAX_PERIOD_NORM}; no period was truncated"
        )

    a, b = evaluate.ideal_generator(factors)
    generated_norm = evaluate.norm((a, b))
    h2 = gcd(a, b)
    if h2 <= 0 or generated_norm % h2:
        raise ArithmeticError(("invalid principal ideal HNF data", factors, (a, b)))
    h1 = generated_norm // h2
    bezout_gcd, s, t = _extended_gcd(b, a - b)
    if bezout_gcd != h2:
        raise ArithmeticError(
            ("HNF Bezout gcd mismatch", factors, bezout_gcd, h2)
        )
    b_hnf = (a * s - b * t) % h1
    if generated_norm != period_norm or h1 * h2 != period_norm:
        raise ArithmeticError(
            ("lcm ideal norm/generator mismatch", factors, period_norm, generated_norm)
        )
    return _Period(factors, h1, h2, b_hnf, period_norm)


@lru_cache(maxsize=_TABLE_CACHE_SIZE)
def _pair_table(
    period: _Period,
    left: tuple[tuple[evaluate.I, int], ...],
    right: tuple[tuple[evaluate.I, int], ...],
    orientation: int,
) -> _CharacterTable:
    """Build the full lcm-ideal period table, retaining both zero masks."""
    values = bytearray(period.norm)
    for j in range(period.h2):
        row_offset = j * period.h1
        for x in range(period.h1):
            z = (x, j)
            left_phase = evaluate.phase_index(left, z, orientation)
            right_phase = evaluate.phase_index(right, z, orientation)
            if left_phase is None or right_phase is None:
                value = 0
            else:
                exact = 2 * evaluate.ROOT_REAL[(left_phase - right_phase) % 6]
                if exact.denominator != 1:
                    raise ArithmeticError(("nonintegral 2Re of sixth root", exact))
                value = int(exact)
            if value < -2 or value > 2:
                raise ArithmeticError(("periodic character table value out of range", value))
            values[row_offset + x] = value + 2
    return _CharacterTable(period.h1, period.h2, period.b_hnf, bytes(values))


@lru_cache(maxsize=None)
def _unit_phase(
    factors: tuple[tuple[evaluate.I, int], ...], orientation: int
) -> int:
    phase = evaluate.phase_index(factors, (1, 1), orientation)
    if phase is None:
        raise ArithmeticError("the unit (1,1) cannot be zero under an ideal character")
    return phase


def _pair_vanishes_by_units(
    left: tuple[tuple[evaluate.I, int], ...],
    right: tuple[tuple[evaluate.I, int], ...],
    orientation: int,
) -> bool:
    # (1,1) generates the six units.  The common-prime zero mask is unit
    # invariant, so a nontrivial quotient character cancels each full orbit.
    return _unit_phase(left, orientation) != _unit_phase(right, orientation)


@lru_cache(maxsize=1)
def _native_library() -> ctypes.CDLL:
    if not _CPP_FILE.is_file():
        raise FileNotFoundError(_CPP_FILE)
    compiler = shutil.which("clang++")
    if compiler is None:
        raise RuntimeError("clang++ is required to build the exact periodic counter")

    source = _CPP_FILE.read_bytes()
    identity = hashlib.sha256(
        source + sys.platform.encode() + platform.machine().encode()
    ).hexdigest()
    cache_dir = Path("/tmp") / f"cf22-periodic-counter-{identity}"
    cache_dir.mkdir(parents=True, exist_ok=True)
    suffix = ".dylib" if sys.platform == "darwin" else ".so"
    library_path = cache_dir / f"libperiodic_counter{suffix}"
    if not library_path.is_file():
        temporary_path = cache_dir / f"libperiodic_counter.{os.getpid()}.tmp{suffix}"
        if sys.platform == "darwin":
            flags = ["-dynamiclib"]
        else:
            flags = ["-shared", "-fPIC"]
        command = [
            compiler,
            "-std=c++17",
            "-O3",
            "-DNDEBUG",
            *flags,
            str(_CPP_FILE),
            "-o",
            str(temporary_path),
        ]
        result = subprocess.run(command, capture_output=True, text=True)
        if result.returncode:
            temporary_path.unlink(missing_ok=True)
            raise RuntimeError(
                "clang++ failed to build periodic_counter.cpp: "
                + (result.stderr.strip() or result.stdout.strip())
            )
        temporary_path.replace(library_path)

    library = ctypes.CDLL(str(library_path))
    function = library.periodic_disk_sums
    function.argtypes = [
        ctypes.POINTER(ctypes.c_uint8),
        ctypes.c_int64,
        ctypes.c_int64,
        ctypes.c_int64,
        ctypes.POINTER(ctypes.c_int64),
        ctypes.c_int64,
        ctypes.POINTER(ctypes.c_int64),
        ctypes.POINTER(ctypes.c_char),
        ctypes.c_size_t,
    ]
    function.restype = ctypes.c_int
    return library


def _counter_sums(
    table: bytes,
    h1: int,
    h2: int,
    b_hnf: int,
    bounds: Sequence[int],
) -> list[int]:
    if h1 <= 0 or h2 <= 0 or len(table) != h1 * h2:
        raise ValueError("table length must equal the positive ideal period h1*h2")
    if h1 * h2 > MAX_PERIOD_NORM:
        raise ValueError(
            f"ideal norm period {h1 * h2} exceeds explicit limit "
            f"{MAX_PERIOD_NORM}; no period was truncated"
        )
    library = _native_library()
    function = library.periodic_disk_sums
    table_arg = (ctypes.c_uint8 * len(table)).from_buffer_copy(table)
    bound_arg = (ctypes.c_int64 * len(bounds))(*bounds)
    output_arg = (ctypes.c_int64 * len(bounds))()
    error_arg = ctypes.create_string_buffer(512)
    status = function(
        table_arg,
        h1,
        h2,
        b_hnf,
        bound_arg,
        len(bounds),
        output_arg,
        error_arg,
        len(error_arg),
    )
    if status:
        message = error_arg.value.decode("utf-8", errors="replace")
        raise RuntimeError(f"native periodic disk counter failed ({status}): {message}")
    return list(output_arg)


def _validate_bounds(bounds: Sequence[int]) -> list[int]:
    result: list[int] = []
    for bound in bounds:
        if isinstance(bound, bool) or not isinstance(bound, Integral):
            raise TypeError(f"radius must be an integer, got {bound!r}")
        bound = int(bound)
        if bound < 0 or bound > MAX_BOUND:
            raise ValueError(
                f"radius {bound} is outside [0,{MAX_BOUND}]; no disk was truncated"
            )
        result.append(bound)
    return result


def raw_sums(
    n_rows: list[evaluate.Ideal],
    bounds: list[int],
    orientation: int = 1,
) -> list[dict[str, Any]]:
    """Return exact unweighted periodic character Gram sums at each radius.

    ``pair_2re[i][j]`` is the integer sum of
    ``2*Re(chi_i(w)^eps * conjugate(chi_j(w)^eps))`` over
    ``0 < norm(w) <= B``.  Characters use evaluate.py's exact phase tables and
    zero extension, including primes shared by the two rows.
    """
    if (
        isinstance(orientation, bool)
        or not isinstance(orientation, Integral)
        or orientation not in (-1, 1)
    ):
        raise ValueError("orientation must be -1 or +1")
    if any(not hasattr(row, "factors") for row in n_rows):
        raise TypeError("n_rows must contain evaluate.Ideal values")
    checked_bounds = _validate_bounds(bounds)
    if not checked_bounds:
        return []

    unique_bounds = sorted(set(checked_bounds))
    # Period 1 with value 1 counts lattice points; the native counter removes
    # the origin and therefore returns N(B)=#{w: 0<norm(w)<=B}.
    n_by_bound = dict(
        zip(unique_bounds, _counter_sums(bytes((3,)), 1, 1, 0, unique_bounds))
    )

    count = len(n_rows)
    matrices = {bound: [[0] * count for _ in range(count)] for bound in unique_bounds}
    for i, left_row in enumerate(n_rows):
        left = left_row.factors
        for j in range(i, count):
            right = n_rows[j].factors
            # Always form/check the complete lcm period before applying an
            # exact unit-orbit cancellation shortcut.
            period = _principal_period(left, right)
            if _pair_vanishes_by_units(left, right, orientation):
                values = [0] * len(unique_bounds)
            else:
                table = _pair_table(period, left, right, orientation)
                values = _counter_sums(
                    table.encoded,
                    table.h1,
                    table.h2,
                    table.b_hnf,
                    unique_bounds,
                )
            for bound, value in zip(unique_bounds, values):
                matrices[bound][i][j] = value
                matrices[bound][j][i] = value

    return [
        {"B": bound, "N": n_by_bound[bound], "pair_2re": matrices[bound]}
        for bound in checked_bounds
    ]


def raw_energy(pair_2re: Sequence[Sequence[int]], weights: Sequence[Any]) -> Any:
    """Evaluate the real quadratic form represented by ``pair_2re`` exactly.

    For integer/Fraction weights the result stays rational; ball-valued weights
    such as python-flint ``arb`` stay ball-valued.
    """
    size = len(weights)
    if len(pair_2re) != size or any(len(row) != size for row in pair_2re):
        raise ValueError("pair_2re must be a square matrix matching weights")
    for i in range(size):
        for j in range(size):
            value = pair_2re[i][j]
            if isinstance(value, bool) or not isinstance(value, Integral):
                raise TypeError("pair_2re entries must be integers")
            if value != pair_2re[j][i]:
                raise ValueError("pair_2re must be symmetric")

    total: Any = 0
    for i, weight in enumerate(weights):
        diagonal = int(pair_2re[i][i]) * weight * weight
        if isinstance(diagonal, Integral):
            total += Fraction(int(diagonal), 2)
        else:
            total += diagonal / 2
        for j in range(i + 1, size):
            total += int(pair_2re[i][j]) * weight * weights[j]
    return total


__all__ = [
    "MAX_BOUND",
    "MAX_PERIOD_NORM",
    "raw_energy",
    "raw_sums",
]
