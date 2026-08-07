#!/usr/bin/env python3
"""Reproduce the c=13, N=4 cutoff-free archimedean source block.

The calculation uses the exact finite test-function route from Groskin's
three-route reproducibility package and independently guards the bridge to the
CCM divided-difference matrix.  No finite-difference diagonal and no
oscillatory tail quadrature are used.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


HERE = Path(__file__).resolve().parent
REFERENCE = HERE / "threeroute_c13N4_reference.json"
T0 = mp.mpf(60)
NPER = 60
BRIDGE_POINTS = ("0.9", "7.1", "14.2", "31.7")


def h_plus(r: mp.mpf) -> mp.mpf:
    return mp.re(mp.digamma(mp.mpf(1) / 4 + mp.mpc(0, r) / 2)) - mp.log(mp.pi)


class TestFn:
    """Exact finite chain v -> K_v -> g_v for the published control vector."""

    def __init__(self, c: int, nmax: int, vector: list[str]) -> None:
        self.c = c
        self.nmax = nmax
        self.L = mp.log(c)
        self.delta = self.L / (2 * mp.pi)
        self.vector = [mp.mpf(value) for value in vector]
        self.u: dict[int, mp.mpf] = {0: self.vector[0]}
        for k in range(1, nmax + 1):
            self.u[k] = self.vector[k] / mp.sqrt(2)
            self.u[-k] = self.vector[k] / mp.sqrt(2)

        self.alpha: dict[int, mp.mpc] = {}
        self.beta: dict[int, mp.mpf] = {}
        for k in range(-nmax, nmax + 1):
            off_diagonal_sum = mp.fsum(
                self.u[n] / (k - n) for n in self.u if n != k
            )
            self.alpha[k] = 2 * self.u[k] * off_diagonal_sum / (mp.pi * 1j)
            self.beta[k] = 2 * self.u[k] ** 2

    @staticmethod
    def _int_poly_exp(alpha: mp.mpc, beta: mp.mpf, phase: mp.mpc) -> mp.mpc:
        """Integral of (alpha + beta*w) exp(i*phase*w) over w in [0,1]."""
        if abs(phase) < mp.mpf(10) ** -8:
            alpha_series = mp.mpc(0)
            beta_series = mp.mpc(0)
            for j in range(25):
                coefficient = (1j * phase) ** j
                alpha_series += coefficient / mp.factorial(j + 1)
                beta_series += coefficient / (mp.factorial(j) * (j + 2))
            return alpha * alpha_series + beta * beta_series
        iphase = 1j * phase
        exponential = mp.exp(iphase)
        return (
            alpha * (exponential - 1) / iphase
            + beta * ((exponential * (iphase - 1) + 1) / iphase**2)
        )

    def g(self, z: mp.mpf | mp.mpc) -> mp.mpf | mp.mpc:
        """Exact finite expression for the source-side test function g_v."""
        theta = z * self.L
        total = mp.mpc(0)
        for k in self.u:
            alpha = self.alpha[k]
            beta = self.beta[k]
            total += (
                mp.exp(1j * theta)
                / 2
                * self._int_poly_exp(alpha, beta, 2 * mp.pi * k - theta)
            )
            total += (
                mp.exp(-1j * theta)
                / 2
                * self._int_poly_exp(alpha, beta, 2 * mp.pi * k + theta)
            )
        value = 2 * mp.pi * self.delta * total
        return mp.re(value) if abs(mp.im(z)) < mp.mpf(10) ** -30 else value


def s_integer(r: mp.mpf, x: int, L: mp.mpf) -> mp.mpf:
    """Exact integer-mode kernel S(r,x,L), away from removable resonances."""
    if x == 0:
        return mp.mpf(0)
    rho = 2 * mp.pi / L
    return (
        2
        * rho
        * x
        * mp.sin(L * r / 2) ** 2
        / (r**2 - (rho * x) ** 2)
    )


def ds_integer(r: mp.mpf, x: int, L: mp.mpf) -> mp.mpf:
    """Analytic x-derivative of S, including the x=0 diagonal."""
    rho = 2 * mp.pi / L
    rho_x_sq = (rho * x) ** 2
    return (
        2
        * rho
        * mp.sin(L * r / 2) ** 2
        * (r**2 + rho_x_sq)
        / (r**2 - rho_x_sq) ** 2
    )


def bridge_error(test_fn: TestFn, r: mp.mpf) -> mp.mpf:
    """Check sum u_m u_n q_mn(r) / pi = g_v(r) pointwise."""
    values = {n: s_integer(r, n, test_fn.L) for n in test_fn.u}
    contraction = mp.fsum(
        test_fn.u[m]
        * test_fn.u[n]
        * (
            ds_integer(r, m, test_fn.L)
            if m == n
            else (values[m] - values[n]) / (m - n)
        )
        for m in test_fn.u
        for n in test_fn.u
    )
    return abs(contraction / mp.pi - test_fn.g(r))


def ranktwo_tail(
    u: dict[int, mp.mpf], L: mp.mpf, split: mp.mpf
) -> tuple[mp.mpf, mp.mpf]:
    """Cutoff-free tail with the oscillatory half integrated twice by parts."""
    rho = 2 * mp.pi / L

    def finite_rank_density(r: mp.mpf) -> mp.mpf:
        a = r / rho
        p_channel = mp.fsum(u[n] / (a - n) for n in u)
        q_channel = mp.fsum(u[n] / (a + n) for n in u)
        return p_channel**2 + q_channel**2

    density = lambda r: h_plus(r) * finite_rank_density(r) / (rho * mp.pi**2)
    smooth = mp.quad(
        density,
        [split, 2 * split, 8 * split, 64 * split, 1024 * split, mp.inf],
    ) / 2

    first = lambda r: mp.diff(density, r)
    second = lambda r: mp.diff(density, r, 2)
    boundary_1 = -density(split) * mp.sin(L * split) / L
    boundary_2 = -first(split) * mp.cos(L * split) / L**2
    period = 2 * mp.pi / L
    points = [split + k * period for k in range(NPER + 1)]
    remainder = -(1 / L**2) * mp.quad(
        lambda r: second(r) * mp.cos(L * r), points
    )
    endpoint = points[-1]
    remainder_bound = (1 / L**2) * mp.quad(
        lambda r: abs(second(r)), [endpoint, 4 * endpoint, 64 * endpoint, mp.inf]
    )
    cosine_part = -(boundary_1 + boundary_2 + remainder) / 2
    return smooth + cosine_part, remainder_bound / 2


def compute(reference: dict[str, object], dps: int) -> dict[str, mp.mpf]:
    mp.mp.dps = dps
    test_fn = TestFn(
        int(reference["c"]),
        int(reference["N"]),
        list(reference["v"]),  # type: ignore[arg-type]
    )
    bridge_max = max(
        bridge_error(test_fn, mp.mpf(point)) for point in BRIDGE_POINTS
    )
    head = (1 / mp.pi) * mp.quad(
        lambda r: h_plus(r) * test_fn.g(r),
        [0, 5, 10, 20, 40, T0],
    )
    tail, tail_bound = ranktwo_tail(test_fn.u, test_fn.L, T0)
    return {
        "arch": head + tail,
        "head": head,
        "tail": tail,
        "tail_bound": tail_bound,
        "bridge_max": bridge_max,
    }


def load_reference() -> dict[str, object]:
    reference = json.loads(REFERENCE.read_text(encoding="utf-8"))
    expected = {
        "record": "https://zenodo.org/records/21146461",
        "package_md5": "71e7890a609c6db38f1324ce8225b840",
        "member_sha256": "b6382ce9fc80c7ffa557e2e003b33f6f836eac01ec289b898458f798876b58d4",
        "verifier_sha256": "345df0765c9ca9538bab71de12b2a90ea83ea08fb68abb7114b7e8d7f2812bdd",
    }
    for key, value in expected.items():
        if reference.get("source", {}).get(key) != value:  # type: ignore[union-attr]
            raise SystemExit(f"SOURCE_LOCK_MISMATCH:{key}")
    if reference.get("c") != 13 or reference.get("N") != 4:
        raise SystemExit("CONTROL_CELL_MISMATCH")
    return reference


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", nargs="+", type=int, default=[30, 40])
    args = parser.parse_args()
    if len(args.dps) < 2 or args.dps != sorted(set(args.dps)):
        raise SystemExit("PRECISION_LADDER_INVALID")

    reference = load_reference()
    mp.mp.dps = max(args.dps)
    target = mp.mpf(str(reference["route2_arch"]))
    published_tail_bound = mp.mpf(str(reference["route2_tail_rem_bound"]))
    rows: list[tuple[int, dict[str, mp.mpf]]] = []
    for dps in args.dps:
        print(f"dps={dps}: start", flush=True)
        result = compute(reference, dps)
        rows.append((dps, result))
        print(
            "  arch=%s  diff=%s  bridge=%s  tail_bound=%s"
            % (
                mp.nstr(result["arch"], 35),
                mp.nstr(result["arch"] - target, 10),
                mp.nstr(result["bridge_max"], 5),
                mp.nstr(result["tail_bound"], 8),
            ),
            flush=True,
        )

    precision_delta = abs(rows[-1][1]["arch"] - rows[-2][1]["arch"])
    target_delta = abs(rows[-1][1]["arch"] - target)
    bridge_limit = mp.mpf(10) ** (-(min(args.dps) - 8))
    passed = (
        all(result["bridge_max"] <= bridge_limit for _, result in rows)
        and precision_delta <= mp.mpf("1e-18")
        and target_delta <= published_tail_bound
        and rows[-1][1]["tail_bound"] <= published_tail_bound * mp.mpf("1.01")
    )

    print(f"precision_delta={mp.nstr(precision_delta, 10)}")
    print(f"target_delta={mp.nstr(target_delta, 10)}")
    print(f"published_tail_bound={mp.nstr(published_tail_bound, 10)}")
    print("PHASE0_ARCH_BLOCK=" + ("PASS" if passed else "FAIL"))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
