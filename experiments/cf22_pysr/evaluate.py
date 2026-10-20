#!/usr/bin/env python3
"""Certified finite evaluator for the source-locked CF22 specialization.

This computes the complete finite row/column sums for the fixed plan profiles.
It is a finite-source specialization only; it is not a cofinal estimate.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import hashlib
from math import isqrt
import json
from pathlib import Path
import subprocess
import sys

from flint import arb, ctx, fmpq


I = tuple[int, int]
ONE: I = (1, 0)
ZERO: I = (0, 0)
UNITS: tuple[I, ...] = (
    (1, 0), (-1, 0), (0, 1), (0, -1), (-1, -1), (1, 1),
)
ROOT: list[I] = [ONE]


def rm(x: I, y: I) -> I:
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c + b * d


for _ in range(5):
    ROOT.append(rm(ROOT[-1], (0, 1)))
ROOT_INDEX = {z: k for k, z in enumerate(ROOT)}
ROOT_REAL = tuple(Fraction(2 * z[0] + z[1], 2) for z in ROOT)
MAX_ENUM_NORM = 10_000


def norm(z: I) -> int:
    return z[0] ** 2 - z[0] * z[1] + z[1] ** 2


def em(x: I, y: I) -> I:
    a, b = x
    c, d = y
    return a * c - b * d, a * d + b * c - b * d


def ep(x: I, k: int) -> I:
    v = ONE
    while k:
        if k & 1:
            v = em(v, x)
        x = em(x, x)
        k //= 2
    return v


def isprime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def split_generators(q: int) -> list[I]:
    out: list[I] = []
    bound = isqrt(4 * q // 3) + 2
    for b in range(-bound, bound + 1):
        if b % 3:
            continue
        d = 4 * q - 3 * b * b
        if d < 0:
            continue
        s = isqrt(d)
        if s * s != d:
            continue
        for t in {s, -s}:
            if (b + t) % 2 == 0:
                a = (b + t) // 2
                if a % 3 == 1 and norm((a, b)) == q:
                    out.append((a, b))
    out = sorted(set(out))
    if len(out) != 2:
        raise ArithmeticError(("split generators", q, out))
    return out


@lru_cache(maxsize=None)
def cp(p: I, u: I) -> I:
    """Sixth-power residue symbol, copied from the Q03 source diagnostic."""
    q = norm(p)
    l = isqrt(q)
    if l * l == q:
        def mm(x: I, y: I) -> I:
            return tuple(t % l for t in em(x, y))  # type: ignore[return-value]

        def pw(x: I, k: int) -> I:
            v = (1, 0)
            while k:
                if k & 1:
                    v = mm(v, x)
                x = mm(x, x)
                k //= 2
            return v

        x = (u[0] % l, u[1] % l)
        if x == (0, 0):
            return ZERO
        roots = [pw((1, 1), j) for j in range(6)]
        return ROOT[roots.index(pw(x, (q - 1) // 6))]
    w = (-p[0] * pow(p[1], -1, q)) % q
    x = (u[0] + w * u[1]) % q
    if x == 0:
        return ZERO
    roots = [pow((1 + w) % q, j, q) for j in range(6)]
    return ROOT[roots.index(pow(x, (q - 1) // 6, q))]


def chi(f: dict[I, int], u: I) -> I:
    """Hecke symbol from the Q03 source diagnostic, with zero extension."""
    v = ONE
    for p, k in f.items():
        c = cp(p, u)
        if c == ZERO:
            return ZERO
        for _ in range(k):
            v = rm(v, c)
    return v


RAMIFIED_3: I = (1, -1)
INERT_2: I = (-2, 0)  # primary associate; its ideal norm is 4.
BAD_PRIMES = frozenset((RAMIFIED_3, INERT_2))


@dataclass(frozen=True)
class Ideal:
    q: int
    factors: tuple[tuple[I, int], ...]
    gen: I


@dataclass(frozen=True)
class Element:
    z: I
    q: int
    factors: tuple[tuple[I, int], ...]


def factor_integer(n: int) -> tuple[tuple[int, int], ...]:
    if n < 1:
        raise ValueError("positive integer required")
    result: list[tuple[int, int]] = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            result.append((d, e))
        d += 1 if d == 2 else 2
    if n > 1:
        result.append((n, 1))
    return tuple(result)


@lru_cache(maxsize=None)
def ideal_factorizations_of_norm(q: int) -> tuple[tuple[tuple[I, int], ...], ...]:
    """Enumerate all Eisenstein prime-ideal factorizations of norm q."""
    states: list[dict[I, int]] = [{}]
    for p, e in factor_integer(q):
        if p == 3:
            options = [{RAMIFIED_3: e}]
        elif p % 3 == 2:
            if e % 2:
                return ()
            options = [{(-p, 0): e // 2}]
        else:
            g1, g2 = split_generators(p)
            options = []
            for k in range(e + 1):
                part: dict[I, int] = {}
                if k:
                    part[g1] = k
                if e - k:
                    part[g2] = e - k
                options.append(part)
        states = [
            {**state, **part}
            for state in states
            for part in options
        ]
    return tuple(sorted(tuple(sorted(f.items())) for f in states))


def ideal_generator(factors: tuple[tuple[I, int], ...]) -> I:
    g = ONE
    for p, e in factors:
        g = em(g, ep(p, e))
    return g


def ideal_norm(factors: tuple[tuple[I, int], ...]) -> int:
    q = 1
    for p, e in factors:
        q *= norm(p) ** e
    return q


def good_ideal(factors: tuple[tuple[I, int], ...]) -> bool:
    return all(p not in BAD_PRIMES for p, _ in factors)


def mu(factors: tuple[tuple[I, int], ...]) -> int:
    if any(e > 1 for _, e in factors):
        return 0
    return -1 if len(factors) % 2 else 1


def sixthfree(factors: tuple[tuple[I, int], ...]) -> bool:
    return all(e < 6 for _, e in factors)


@lru_cache(maxsize=None)
def ideals_up_to(max_norm: int) -> tuple[Ideal, ...]:
    rows: list[Ideal] = []
    for q in range(1, max_norm + 1):
        for factors in ideal_factorizations_of_norm(q):
            gen = ideal_generator(factors)
            if ideal_norm(factors) != q or norm(gen) != q:
                raise ArithmeticError(("ideal norm/generator mismatch", q, factors, gen))
            rows.append(Ideal(q, factors, gen))
    return tuple(sorted(rows, key=lambda row: (row.q, row.factors)))


@lru_cache(maxsize=None)
def elements_up_to(max_norm: int) -> tuple[Element, ...]:
    rows: list[Element] = []
    seen: set[I] = set()
    for ideal in ideals_up_to(max_norm):
        units_seen: set[I] = set()
        for unit in UNITS:
            z = em(unit, ideal.gen)
            if z in units_seen or z in seen:
                raise ArithmeticError(("duplicate element enumeration", z, ideal))
            units_seen.add(z)
            seen.add(z)
            if norm(z) != ideal.q:
                raise ArithmeticError(("unit norm mismatch", ideal, z))
            rows.append(Element(z, ideal.q, ideal.factors))
        if len(units_seen) != 6:
            raise ArithmeticError(("unit orbit is not size six", ideal))
    return tuple(sorted(rows, key=lambda row: (row.q, row.z)))


def is_coprime(f: tuple[tuple[I, int], ...], g: tuple[tuple[I, int], ...]) -> bool:
    return not ({p for p, _ in f} & {p for p, _ in g})


def arb_fraction(x: Fraction) -> arb:
    return arb(fmpq(x.numerator, x.denominator))


def rational_exponent(U: int, e: Fraction) -> arb:
    return arb(U) ** fmpq(e.numerator, e.denominator)


def scaled_power(U: int, e: Fraction, scale: Fraction = Fraction(1)) -> arb:
    return arb_fraction(scale) * rational_exponent(U, e)


def valuation_map(n: int) -> dict[int, int]:
    return dict(factor_integer(n))


def exact_scaled_power_equality(q: int, U: int, e: Fraction, scale: Fraction) -> bool:
    # q = scale * U**e iff the prime valuations agree after multiplying by e.denominator.
    lhs = valuation_map(q)
    den = valuation_map(scale.denominator)
    num = valuation_map(scale.numerator)
    rhs = valuation_map(U)
    primes = set(lhs) | set(den) | set(num) | set(rhs)
    return all(
        e.denominator * (lhs.get(p, 0) + den.get(p, 0) - num.get(p, 0))
        == e.numerator * rhs.get(p, 0)
        for p in primes
    )


BOUNDARY_PRECISIONS: list[int] = []


def compare_integer_scaled_power(q: int, U: int, e: Fraction,
                                 scale: Fraction = Fraction(1),
                                 base_precision: int | None = None) -> int:
    """Certified sign of q - scale*U**e; equality is decided exactly."""
    if exact_scaled_power_equality(q, U, e, scale):
        return 0
    initial = base_precision or ctx.prec
    precision = initial
    while precision <= max(initial, 8192):
        ctx.prec = precision
        bound = scaled_power(U, e, scale)
        qb = arb(q)
        if qb < bound:
            BOUNDARY_PRECISIONS.append(precision)
            ctx.prec = initial
            return -1
        if qb > bound:
            BOUNDARY_PRECISIONS.append(precision)
            ctx.prec = initial
            return 1
        precision *= 2
    ctx.prec = initial
    raise ArithmeticError(f"ambiguous certified norm boundary: q={q}, U={U}, exponent={e}, scale={scale}")


def ball_endpoints(x: arb, digits: int = 50) -> tuple[Fraction, Fraction, dict[str, str]]:
    mid, rad, exponent = (int(v) for v in x.mid_rad_10exp(digits))
    power = Fraction(10**exponent) if exponent >= 0 else Fraction(1, 10 ** (-exponent))
    lo = Fraction(mid - rad) * power
    hi = Fraction(mid + rad) * power
    return lo, hi, {
        "lower": f"{mid - rad}e{exponent}",
        "upper": f"{mid + rad}e{exponent}",
    }


def ball_midpoint_decimal(x: arb, digits: int = 50) -> str:
    mid, _rad, exponent = (int(v) for v in x.mid_rad_10exp(digits))
    return f"{mid}e{exponent}"


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def certified_ceil(x: arb) -> int:
    _, upper, _ = ball_endpoints(x)
    return ceil_fraction(upper)


def interval_json(x: arb) -> dict[str, str]:
    return ball_endpoints(x)[2]


def interval_width(x: arb) -> Fraction:
    lo, hi, _ = ball_endpoints(x)
    return hi - lo


def decimal_fraction(x: Fraction) -> str:
    # Plan r/ell denominators have only 2 and 5 as prime factors.
    den = x.denominator
    twos = fives = 0
    while den % 2 == 0:
        den //= 2
        twos += 1
    while den % 5 == 0:
        den //= 5
        fives += 1
    if den != 1:
        return f"{x.numerator}/{x.denominator}"
    digits = max(twos, fives)
    scaled = x.numerator * (10**digits // x.denominator)
    sign = "-" if scaled < 0 else ""
    text = str(abs(scaled)).rjust(digits + 1, "0")
    if digits == 0:
        return sign + text
    result = sign + text[:-digits] + "." + text[-digits:]
    return result.rstrip("0").rstrip(".") if "." in result else result


def bump(q: int, scale: int, base_precision: int) -> arb:
    """Fixed profile exp(1-1/(1-(2y-2)^2)) on (1/2,3/2)."""
    y = arb(fmpq(q, scale))
    d = arb(1) - (2 * y - 2) ** 2
    if not d > 0:
        raise ArithmeticError("profile bump evaluated outside its certified support")
    return (arb(1) - 1 / d).exp()


def rho_weight(q: int, U: int, precision: int) -> arb:
    if compare_integer_scaled_power(q, U, Fraction(1), Fraction(1, 2), precision) <= 0:
        return arb(0)
    if compare_integer_scaled_power(q, U, Fraction(1), Fraction(3, 2), precision) >= 0:
        return arb(0)
    return bump(q, U, precision)


def W_weight(q: int, U: int, ell: Fraction, precision: int) -> arb:
    if compare_integer_scaled_power(q, U, ell, Fraction(1, 2), precision) <= 0:
        return arb(0)
    if compare_integer_scaled_power(q, U, ell, Fraction(3, 2), precision) >= 0:
        return arb(0)
    L = rational_exponent(U, ell)
    y = arb(q) / L
    d = arb(1) - (2 * y - 2) ** 2
    if not d > 0:
        raise ArithmeticError("certified support and Arb profile evaluation disagree")
    return (arb(1) - 1 / d).exp()


def phase_index(factors: tuple[tuple[I, int], ...], z: I, orientation: int) -> int | None:
    value = chi(dict(factors), z)
    if value == ZERO:
        return None
    k = ROOT_INDEX[value]
    return k if orientation == 1 else (-k) % 6


def phase_norm(z: tuple[arb, arb]) -> arb:
    a, b = z
    return a * a + a * b + b * b


def phase_real_inner(z: tuple[arb, arb], w: tuple[arb, arb]) -> arb:
    a, b = z
    c, d = w
    return a * c + (a * d + b * c) / 2 + b * d


def check_plan(plan: dict) -> None:
    expected_profiles = {
        "rho": "exp(1-1/(1-(2*y-2)^2)) on 1/2<y<3/2, zero elsewhere",
        "W": "same as rho",
        "C_H": 2,
        "S": "prime ideals above 6",
        "nu": "1 on good ideals, zero extension",
    }
    if plan.get("schema") != "cf22-pilot-plan-v1":
        raise ValueError("unexpected plan schema")
    if plan.get("scope") != "FINITE_SOURCE_SPECIALIZATION":
        raise ValueError("plan must be labeled FINITE_SOURCE_SPECIALIZATION")
    if plan.get("profiles") != expected_profiles:
        raise ValueError("plan profile differs from the fixed source specialization")
    if not isinstance(plan.get("configs"), list) or not plan["configs"]:
        raise ValueError("plan must contain configurations")


def self_checks() -> None:
    if len(set(UNITS)) != 6 or any(norm(u) != 1 for u in UNITS):
        raise ArithmeticError("Eisenstein unit list is incomplete")
    # Independently compare ideal enumeration with exact lattice enumeration.
    bound = 32
    enumerated = {row.z for row in elements_up_to(bound)}
    lattice: set[I] = set()
    bmax = 2 * int(bound**0.5) + 3
    for a in range(-bmax, bmax + 1):
        for b in range(-bmax, bmax + 1):
            z = (a, b)
            if norm(z) and norm(z) <= bound:
                lattice.add(z)
    if lattice != enumerated:
        raise ArithmeticError(("ideal/lattice enumeration mismatch", len(lattice), len(enumerated)))
    if not any(RAMIFIED_3 in dict(f) for f in ideal_factorizations_of_norm(3)):
        raise ArithmeticError("ramified prime branch missing")
    if not any(INERT_2 in dict(f) for f in ideal_factorizations_of_norm(4)):
        raise ArithmeticError("inert prime branch missing")
    split7 = ideal_factorizations_of_norm(7)
    if len(split7) != 2 or split7[0] == split7[1]:
        raise ArithmeticError("both split prime branches are required")
    # Source semantics are ideal-exponent based: N(8)=64 has (2)^3, while
    # the element (64,0) has (2)^6 and is excluded from the sixthfree u family.
    f64 = ideal_factorizations_of_norm(norm((8, 0)))
    row64 = next(f for f in f64 if ideal_generator(f) in ((8, 0), (-8, 0)))
    if not sixthfree(row64) or norm((8, 0)) != 64:
        raise ArithmeticError("norm-64 source sixthfree classification changed")
    f4096 = ideal_factorizations_of_norm(norm((64, 0)))
    row4096 = next(f for f in f4096 if ideal_generator(f) == (64, 0))
    if sixthfree(row4096) or dict(row4096).get(INERT_2) != 6:
        raise ArithmeticError("sixth-power ideal boundary classification changed")
    if mu(((INERT_2, 1),)) != -1 or mu(((INERT_2, 2),)) != 0:
        raise ArithmeticError("Möbius squarefree boundary changed")
    # A shared prime is a zero symbol; the unit row is coherently all ones.
    for p in (INERT_2, split_generators(7)[0], split_generators(7)[1]):
        if cp(p, p) != ZERO:
            raise ArithmeticError(("shared-prime zero mask missing", p))
        if chi({p: 1}, ONE) != ONE:
            raise ArithmeticError(("unit row is not coherent", p))


def canonical_support_hash(n_rows: list[Ideal], amp_rows: list[Ideal],
                           u_rows: list[Element], w_rows: list[Element],
                           n_u: list[list[int | None]], n_w: list[list[int | None]],
                           n_a_masks: list[list[bool]], n_w_coprime: list[list[bool]]) -> str:
    payload = {
        "n": [[x.q, [(*p, e) for p, e in x.factors], mu(x.factors)] for x in n_rows],
        "amp": [[x.q, [(*p, e) for p, e in x.factors]] for x in amp_rows],
        "u": [[x.z[0], x.z[1], x.q, [(*p, e) for p, e in x.factors]] for x in u_rows],
        "w": [[x.z[0], x.z[1], x.q, [(*p, e) for p, e in x.factors]] for x in w_rows],
        "n_amp_masks": n_a_masks,
        "n_u_symbol_masks": [[v is None for v in row] for row in n_u],
        "n_w_symbol_masks": [[v is None for v in row] for row in n_w],
        "n_w_gcd_masks": n_w_coprime,
    }
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def source_hashes(repo: Path) -> dict[str, str]:
    paths = {
        "full_cusp_pair_q07": repo / "docs/literature/openai_math_2026-10-07/PROSHKA_VERDICT_FULL_CUSP_PAIR_Q07.md",
        "signed_incidence_q03": repo / "docs/literature/openai_math_2026-10-07/PROSHKA_VERDICT_SIGNED_INCIDENCE_Q03.md",
    }
    out: dict[str, str] = {}
    for label, path in paths.items():
        if not path.is_file():
            raise FileNotFoundError(path)
        out[label] = hashlib.sha256(path.read_bytes()).hexdigest()
    return out


def source_commit(repo: Path) -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True, stderr=subprocess.PIPE
    ).strip()


def validate_config(config: dict) -> tuple[int, Fraction, Fraction, int]:
    U = config.get("U")
    if not isinstance(U, int) or U < 2:
        raise ValueError(f"invalid U in config {config!r}")
    r = Fraction(config["r"])
    ell = Fraction(config["ell"])
    orientation = config.get("orientation")
    if r < Fraction(28, 25) or r > Fraction(113, 100):
        raise ValueError(f"r outside source band: {r}")
    if ell < r - Fraction(1, 100) or ell > r:
        raise ValueError(f"ell outside source band: r={r}, ell={ell}")
    if orientation not in (-1, 1):
        raise ValueError("orientation must be -1 or +1")
    return U, r, ell, orientation


def evaluate_config(config: dict, precision: int, absolute_q_tolerance: Fraction) -> dict:
    U, r, ell, orientation = validate_config(config)
    ctx.prec = precision
    BOUNDARY_PRECISIONS.clear()
    eP = (Fraction(10001, 10000) * r - 1) / 6
    eH = Fraction(10001, 10000) * r
    P = rational_exponent(U, eP)
    H = rational_exponent(U, eH)
    L = rational_exponent(U, ell)

    amp_limit = certified_ceil(P)
    w_limit_ball = 2 * H
    w_limit = certified_ceil(w_limit_ball)
    n_limit_ball = arb_fraction(Fraction(3, 2)) * L
    n_limit = certified_ceil(n_limit_ball)
    u_limit = (3 * U) // 2
    if max(amp_limit, w_limit, n_limit, u_limit) > MAX_ENUM_NORM:
        raise RuntimeError(
            f"exact enumeration bound exceeds {MAX_ENUM_NORM}; no support was truncated"
        )

    amp_rows = [x for x in ideals_up_to(amp_limit)
                if good_ideal(x.factors)
                and compare_integer_scaled_power(x.q, U, eP, Fraction(1), precision) <= 0]
    if not amp_rows:
        raise ArithmeticError("amplifier ideal set unexpectedly empty")

    u_rows_all = elements_up_to(u_limit)
    u_rows: list[Element] = []
    rho_by_z: dict[I, arb] = {}
    for row in u_rows_all:
        if not sixthfree(row.factors):
            continue
        weight = rho_weight(row.q, U, precision)
        if weight > 0:
            u_rows.append(row)
            rho_by_z[row.z] = weight

    all_n = ideals_up_to(n_limit)
    n_rows: list[Ideal] = []
    W_by_f: list[arb] = []
    for row in all_n:
        if not good_ideal(row.factors):
            continue
        lower_cmp = compare_integer_scaled_power(row.q, U, ell, Fraction(1, 2), precision)
        upper_cmp = compare_integer_scaled_power(row.q, U, ell, Fraction(3, 2), precision)
        if lower_cmp > 0 and upper_cmp < 0:
            n_rows.append(row)
            W_by_f.append(W_weight(row.q, U, ell, precision))

    all_w = elements_up_to(w_limit)
    w_rows = [
        row for row in all_w
        if compare_integer_scaled_power(row.q, U, eH, Fraction(2), precision) <= 0
    ]
    if not w_rows or not n_rows or not u_rows:
        raise ArithmeticError("a required finite support is empty")
    if not any(row.z == ONE for row in w_rows):
        raise ArithmeticError("raw w support must include the unit element")

    active = [i for i, n in enumerate(n_rows) if mu(n.factors) != 0]
    operation_estimate = (len(active) * max(0, len(active) - 1) // 2) * (
        len(amp_rows) * len(u_rows) + len(w_rows)
    )
    if operation_estimate > 50_000_000:
        raise RuntimeError(f"exact off-diagonal evaluation estimate too large: {operation_estimate} terms")

    # Exact Omega(w) by complete u,a enumeration. a is represented by its
    # primary generator; its sixth power is independent of the chosen unit.
    omega: dict[I, arb] = {}
    omega_pairs = 0
    w_set = {row.z for row in w_rows}
    amp_mask_by_n = [[is_coprime(n.factors, a.factors) for a in amp_rows] for n in n_rows]
    for u in u_rows:
        rw = rho_by_z[u.z]
        for a in amp_rows:
            target = em(u.z, ep(a.gen, 6))
            q_target = norm(target)
            if compare_integer_scaled_power(q_target, U, eH, Fraction(2), precision) > 0:
                raise ArithmeticError("C_H=2 failed to contain a rho-supported u*a^6 row")
            if target not in w_set:
                raise ArithmeticError(("u*a^6 target missing from raw V_H enumeration", target, q_target))
            omega[target] = omega.get(target, arb(0)) + rw
            omega_pairs += 1

    omega_mass = sum((omega.get(w.z, arb(0)) for w in w_rows), arb(0))
    lam = omega_mass / len(w_rows)

    # Complete source rows and all character zero masks.
    n_u_indices = [
        [phase_index(n.factors, u.z, orientation) for u in u_rows]
        for n in n_rows
    ]
    n_w_indices = [
        [phase_index(n.factors, w.z, orientation) for w in w_rows]
        for n in n_rows
    ]
    n_w_coprime = [
        [is_coprime(n.factors, w.factors) for w in w_rows]
        for n in n_rows
    ]

    # The raw and masked finite energies, with 1/L included exactly once.
    E_M = arb(0)
    for a_index, _a in enumerate(amp_rows):
        valid_n = [i for i, masks in enumerate(amp_mask_by_n) if masks[a_index]]
        for u_index, u in enumerate(u_rows):
            coeffs = [arb(0) for _ in range(6)]
            for i in valid_n:
                m = mu(n_rows[i].factors)
                k = n_u_indices[i][u_index]
                if m and k is not None:
                    coeffs[k] += m * W_by_f[i]
            a = sum((coeffs[k] * ROOT[k][0] for k in range(6)), arb(0))
            b = sum((coeffs[k] * ROOT[k][1] for k in range(6)), arb(0))
            E_M += rho_by_z[u.z] * (a * a + a * b + b * b) / L

    R_H = arb(0)
    for w_index, _w in enumerate(w_rows):
        coeffs = [arb(0) for _ in range(6)]
        for i, n in enumerate(n_rows):
            m = mu(n.factors)
            k = n_w_indices[i][w_index]
            if m and k is not None:
                coeffs[k] += m * W_by_f[i]
        a = sum((coeffs[k] * ROOT[k][0] for k in range(6)), arb(0))
        b = sum((coeffs[k] * ROOT[k][1] for k in range(6)), arb(0))
        R_H += (a * a + a * b + b * b) / L

    # Independent audit of E_M = sum_w Omega(w) |M_w|^2. This identity uses
    # the sixth-power character and the zero-extended coprimality mask.
    E_M_omega = arb(0)
    for w_index, w in enumerate(w_rows):
        ow = omega.get(w.z, arb(0))
        if ow == 0:
            continue
        coeffs = [arb(0) for _ in range(6)]
        for i, n in enumerate(n_rows):
            m = mu(n.factors)
            k = n_w_indices[i][w_index]
            if m and k is not None:
                coeffs[k] += m * W_by_f[i]
        a = sum((coeffs[k] * ROOT[k][0] for k in range(6)), arb(0))
        b = sum((coeffs[k] * ROOT[k][1] for k in range(6)), arb(0))
        E_M_omega += ow * (a * a + a * b + b * b) / L
    if not E_M.overlaps(E_M_omega):
        raise ArithmeticError("independent E_M / Omega-row audit intervals do not overlap")

    D_diag = arb(0)
    for i, n in enumerate(n_rows):
        m = mu(n.factors)
        if m == 0:
            continue
        inner = arb(0)
        for j, w in enumerate(w_rows):
            if n_w_coprime[i][j]:
                inner += omega.get(w.z, arb(0)) - lam
        D_diag += (W_by_f[i] ** 2) * inner / L

    C_algebraic = E_M - lam * R_H - D_diag

    # Independent off-diagonal n-pair evaluation. This avoids reusing the
    # E_M, R_H, or D_diag reductions above.
    direct_sum = arb(0)
    direct_pair_count = 0
    for pos, i in enumerate(active):
        ni = n_rows[i]
        mi = mu(ni.factors)
        for j in active[pos + 1:]:
            nj = n_rows[j]
            mj = mu(nj.factors)
            kernel_u = arb(0)
            for a_index, _a in enumerate(amp_rows):
                if not (amp_mask_by_n[i][a_index] and amp_mask_by_n[j][a_index]):
                    continue
                for k, u in enumerate(u_rows):
                    ci = n_u_indices[i][k]
                    cj = n_u_indices[j][k]
                    if ci is not None and cj is not None:
                        kernel_u += rho_by_z[u.z] * arb_fraction(ROOT_REAL[(ci - cj) % 6])
            kernel_w = arb(0)
            for k in range(len(w_rows)):
                ci = n_w_indices[i][k]
                cj = n_w_indices[j][k]
                if ci is not None and cj is not None:
                    kernel_w += arb_fraction(ROOT_REAL[(ci - cj) % 6])
            direct_sum += (2 * mi * mj * W_by_f[i] * W_by_f[j] / L) * (kernel_u - lam * kernel_w)
            direct_pair_count += 1
    C_direct = direct_sum
    if not C_algebraic.overlaps(C_direct):
        raise ArithmeticError("algebraic C and independent off-diagonal C do not overlap")

    denominator = P * (arb(U) ** fmpq(1, 6)) * (L ** fmpq(5, 6))
    q_value = C_algebraic / denominator
    if interval_width(q_value) > absolute_q_tolerance:
        raise ArithmeticError(
            f"certified q interval exceeds plan tolerance {absolute_q_tolerance}"
        )

    support_hash = canonical_support_hash(
        n_rows, amp_rows, u_rows, w_rows,
        n_u_indices, n_w_indices, amp_mask_by_n, n_w_coprime,
    )
    max_boundary_precision = max(BOUNDARY_PRECISIONS, default=precision)
    return {
        "id": config["id"],
        "split": config.get("split"),
        "U": str(U),
        "configuration": {
            "U": U,
            "r": f"{r.numerator}/{r.denominator}",
            "ell": f"{ell.numerator}/{ell.denominator}",
            "orientation": orientation,
        },
        "parameters": {
            "P": interval_json(P),
            "H": interval_json(H),
            "L": interval_json(L),
            "C_H": 2,
        },
        "precision_bits": precision,
        "boundary_precision_max_bits": max_boundary_precision,
        "counts": {
            "amp": len(amp_rows),
            "u": len(u_rows),
            "w": len(w_rows),
            "n": len(n_rows),
            "n_nonzero_mu": len(active),
            "omega_nonzero": sum(1 for w in w_rows if omega.get(w.z, arb(0)) > 0),
            "omega_pairs": omega_pairs,
            "direct_n_pairs": direct_pair_count,
            "amp_is_unit_only": len(amp_rows) == 1 and amp_rows[0].q == 1,
        },
        "masked_support_sha256": support_hash,
        "components": {
            "E_M": interval_json(E_M),
            "E_M_via_Omega_rows": interval_json(E_M_omega),
            "omega_mass": interval_json(omega_mass),
            "lambda": interval_json(lam),
            "R_H": interval_json(R_H),
            "lambda_R_H": interval_json(lam * R_H),
            "D_diag": interval_json(D_diag),
            "normalization_S": interval_json(denominator),
            "C_algebraic": interval_json(C_algebraic),
            "C_direct_off_diagonal": interval_json(C_direct),
            "C_overlap_verified": C_algebraic.overlaps(C_direct),
            "E_M_Omega_overlap_verified": E_M.overlaps(E_M_omega),
        },
        "C": interval_json(C_algebraic),
        "q": interval_json(q_value),
        "q_lower": interval_json(q_value)["lower"],
        "q_upper": interval_json(q_value)["upper"],
        "features": {
            "logU": ball_midpoint_decimal(arb(U).log()),
            "r": decimal_fraction(r),
            "ell": decimal_fraction(ell),
        },
        "feature_intervals": {
            "logU": interval_json(arb(U).log()),
            "r": interval_json(arb_fraction(r)),
            "ell": interval_json(arb_fraction(ell)),
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", required=True, help="preregistered plan JSON")
    parser.add_argument("--output", required=True, help="output JSON path")
    args = parser.parse_args(argv)
    plan_path = Path(args.plan).resolve()
    output_path = Path(args.output).resolve()
    plan_bytes = plan_path.read_bytes()
    plan = json.loads(plan_bytes)
    check_plan(plan)
    precision = plan.get("precision_bits")
    if not isinstance(precision, int) or precision < 64:
        raise ValueError("precision_bits must be an integer >=64")
    tolerance = Fraction(plan.get("absolute_q_tolerance", "0"))
    if tolerance <= 0:
        raise ValueError("absolute_q_tolerance must be positive")
    ctx.prec = precision
    self_checks()
    repo = Path(__file__).resolve().parents[2]
    results = [evaluate_config(config, precision, tolerance) for config in plan["configs"]]
    evaluator_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    payload = {
        "schema": "cf22-finite-evaluation-v1",
        "provenance": {
            "scope": "FINITE_SOURCE_SPECIALIZATION",
            "source_commit": source_commit(repo),
            "plan_sha256": hashlib.sha256(plan_bytes).hexdigest(),
            "evaluator_sha256": evaluator_hash,
            "source_sha256": source_hashes(repo),
            "precision_bits": precision,
            "absolute_q_tolerance": str(tolerance),
            "source_specialization": {
            "S": "prime ideals above 6",
            "nu": "1 on good ideals, zero extension",
            "orientation": "per configuration; both signs are conjugate computations",
            "rho_W": "exp(1-1/(1-(2*y-2)^2)) on 1/2<y<3/2, zero elsewhere",
            },
        },
        "rows": results,
        "limitations": [
            "Finite source specialization only; no cofinal or all-fixed-nu conclusion.",
            "The observed amplifier count is reported for every configuration; unit-only support is a recorded degeneracy.",
        ],
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("x", encoding="utf-8") as output_file:
        output_file.write(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:  # A failed exact enumeration must never be emitted as a partial result.
        print(f"evaluate.py: {type(exc).__name__}: {exc}", file=sys.stderr)
        raise
