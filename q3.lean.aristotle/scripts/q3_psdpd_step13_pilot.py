#!/usr/bin/env python3
"""
Step 13 PSD-pd numerical pilot.

Builds:
  G, A, P, P0, Pnu, Q, N
and checks:
  min eig(C^circ, G^circ), where C = A - P
  max eig(Pnu^circ, R^circ), where R = A - P0

Notation:
  k_spline = B-spline degree
  r_pow    = prime-power exponent in p^r

This is a reconnaissance script, not a proof-grade certificate.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from scipy import linalg, special


def sym(M: np.ndarray) -> np.ndarray:
    """Force a real symmetric matrix numerically."""
    return 0.5 * (M + M.T)


def trap_weights_uniform(x: np.ndarray) -> np.ndarray:
    """Trapezoid weights for a uniform grid."""
    if len(x) < 2:
        raise ValueError("Need at least two grid points.")
    dx = x[1] - x[0]
    w = np.full_like(x, dx, dtype=float)
    w[0] *= 0.5
    w[-1] *= 0.5
    return w


def sieve_primes(n: int) -> list[int]:
    """Simple prime sieve up to n."""
    if n < 2:
        return []
    is_prime = np.ones(n + 1, dtype=bool)
    is_prime[:2] = False
    for q in range(2, int(n**0.5) + 1):
        if is_prime[q]:
            is_prime[q * q : n + 1 : q] = False
    return np.flatnonzero(is_prime).tolist()


def centered_bspline(deg: int, x: np.ndarray | float) -> np.ndarray:
    """
    Centered cardinal B-spline b_deg.

    Support:
      [-(deg+1)/2, (deg+1)/2]

    Formula:
      b_deg(x) = 1/deg! * sum_j (-1)^j C(deg+1,j)
                 (x + (deg+1)/2 - j)_+^deg

    For pilot usage, prefer deg >= 1.
    """
    x_arr = np.asarray(x, dtype=float)

    if deg == 0:
        return ((x_arr >= -0.5) & (x_arr <= 0.5)).astype(float)

    y = x_arr + 0.5 * (deg + 1)
    out = np.zeros_like(x_arr, dtype=float)

    inv_fact = 1.0 / math.factorial(deg)
    for j in range(deg + 2):
        coeff = (-1.0) ** j * math.comb(deg + 1, j)
        out += coeff * np.maximum(y - j, 0.0) ** deg

    out *= inv_fact

    support_radius = 0.5 * (deg + 1)
    out = np.where(np.abs(x_arr) <= support_radius + 1e-14, out, 0.0)
    return out


@dataclass(frozen=True)
class SplinePacket:
    k_spline: int
    s_k: float
    c_k: float

    @staticmethod
    def build(k_spline: int) -> "SplinePacket":
        if k_spline < 1:
            raise ValueError("Use k_spline >= 1 for this pilot.")
        s_k = 0.5 * (k_spline + 1)
        c_k = float(centered_bspline(2 * k_spline + 1, np.array([0.0]))[0])
        if c_k <= 0:
            raise ValueError("Bad spline normalization: c_k <= 0.")
        return SplinePacket(k_spline=k_spline, s_k=s_k, c_k=c_k)

    def r_corr(self, x: np.ndarray | float) -> np.ndarray:
        """
        r_k(x) = autocorrelation of normalized eta_k.

        r_k(x) = b_{2k+1}(s_k x) / c_k
        support in [-2,2].
        """
        return centered_bspline(2 * self.k_spline + 1, self.s_k * np.asarray(x)) / self.c_k


def sinc_plain(x: np.ndarray) -> np.ndarray:
    """sin(x)/x via NumPy's normalized sinc."""
    return np.sinc(x / np.pi)


def E_abs2_axis(t: np.ndarray, ell: float, packet: SplinePacket) -> np.ndarray:
    """
    |E_{ell,k}(it)|^2.

    E_{ell,k}(it)
      = 1/sqrt(s_k c_k) *
        [ sin(ell*t/(2s_k)) / (ell*t/(2s_k)) ]^(k+1)
    """
    x = ell * t / (2.0 * packet.s_k)
    return (1.0 / (packet.s_k * packet.c_k)) * sinc_plain(x) ** (2 * packet.k_spline + 2)


def omega(t: np.ndarray) -> np.ndarray:
    """
    Omega(t) = Gamma_R'/Gamma_R(1/2+it)
             + Gamma_R'/Gamma_R(1/2-it)

    With Gamma_R(s)=pi^(-s/2) Gamma(s/2):
      Omega(t) = -log(pi) + Re psi(1/4 + it/2)
    """
    z = 0.25 + 0.5j * t
    return -np.log(np.pi) + np.real(special.digamma(z))


@dataclass(frozen=True)
class PrimeShift:
    a: float
    weight: float
    p: int
    r_pow: int


def prime_power_shifts(L: float) -> list[PrimeShift]:
    """
    Build shifts a = r_pow * log(p) <= 2L
    with weight log(p) / p^(r_pow/2).
    """
    max_n = int(np.floor(np.exp(2.0 * L))) + 1
    primes = sieve_primes(max_n)

    shifts: list[PrimeShift] = []
    cutoff = 2.0 * L + 1e-14

    for p in primes:
        logp = math.log(p)
        r_pow = 1
        while r_pow * logp <= cutoff:
            a = r_pow * logp
            weight = logp * math.exp(-0.5 * a)
            shifts.append(PrimeShift(a=a, weight=weight, p=p, r_pow=r_pow))
            r_pow += 1

    shifts.sort(key=lambda x: x.a)
    return shifts


@dataclass(frozen=True)
class PilotParams:
    L: float = 3.0
    ell: float = 0.35
    delta: float = 0.25
    k_spline: int = 5
    arch_tmax: float = 180.0
    arch_nt: int = 24001
    p0_na: int = 12001


def build_centers(params: PilotParams) -> np.ndarray:
    """Grid centers u_j in [-L+ell, L-ell]."""
    L, ell, delta = params.L, params.ell, params.delta
    return np.arange(-L + ell, L - ell + 0.5 * delta, delta, dtype=float)


def build_G(D: np.ndarray, params: PilotParams, packet: SplinePacket) -> np.ndarray:
    return sym(packet.r_corr(D / params.ell))


def build_A(D: np.ndarray, params: PilotParams, packet: SplinePacket) -> np.ndarray:
    """
    A_ij = ell/pi * int_0^inf Omega(t) |E(it)|^2 cos(t*d_ij) dt.

    Pilot uses finite cutoff [0, arch_tmax] and trapezoid.
    Not proof-grade.
    """
    t = np.linspace(0.0, params.arch_tmax, params.arch_nt)
    wt = trap_weights_uniform(t)

    base = wt * omega(t) * E_abs2_axis(t, params.ell, packet)

    A = np.zeros_like(D, dtype=float)
    for idx in range(len(t)):
        A += base[idx] * np.cos(t[idx] * D)

    A *= params.ell / np.pi
    return sym(A)


def build_P(D: np.ndarray, params: PilotParams, packet: SplinePacket) -> tuple[np.ndarray, list[PrimeShift]]:
    """
    P_ij = sum_{r log p <= 2L} weight *
           [r_k((d_ij-a)/ell) + r_k((d_ij+a)/ell)].
    """
    shifts = prime_power_shifts(params.L)
    P = np.zeros_like(D, dtype=float)

    for sh in shifts:
        P += sh.weight * (
            packet.r_corr((D - sh.a) / params.ell)
            + packet.r_corr((D + sh.a) / params.ell)
        )

    return sym(P), shifts


def build_P0(D: np.ndarray, params: PilotParams, packet: SplinePacket) -> np.ndarray:
    """
    P0_ij = int_0^{2L} e^{a/2}
            [r_k((d_ij-a)/ell) + r_k((d_ij+a)/ell)] da.

    Pilot uses trapezoid on [0,2L].
    """
    a_grid = np.linspace(0.0, 2.0 * params.L, params.p0_na)
    wa = trap_weights_uniform(a_grid)

    P0 = np.zeros_like(D, dtype=float)
    for a, w in zip(a_grid, wa):
        P0 += w * np.exp(0.5 * a) * (
            packet.r_corr((D - a) / params.ell)
            + packet.r_corr((D + a) / params.ell)
        )

    return sym(P0)


def build_Q(u: np.ndarray) -> np.ndarray:
    """
    Boundary-null constraints:
      sum v_j e^{u_j/2}  = 0
      sum v_j e^{-u_j/2} = 0.

    Constants sqrt(ell)*E(±1/2) are dropped.
    """
    return np.vstack([np.exp(0.5 * u), np.exp(-0.5 * u)])


def boundary_null_basis(Q: np.ndarray) -> np.ndarray:
    """Return a matrix whose columns span ker(Q)."""
    return linalg.null_space(Q)


def generalized_eigs_safe(A: np.ndarray, B: np.ndarray) -> np.ndarray | None:
    try:
        return linalg.eigh(sym(A), sym(B), eigvals_only=True)
    except Exception:
        return None


def run_pilot(params: PilotParams) -> None:
    packet = SplinePacket.build(params.k_spline)

    u = build_centers(params)
    n = len(u)
    D = u[:, None] - u[None, :]

    print("== Step 13 PSD-pd pilot ==")
    print(f"L={params.L}, ell={params.ell}, delta={params.delta}, k_spline={params.k_spline}")
    print(f"n_centers={n}")
    print(f"arch_tmax={params.arch_tmax}, arch_nt={params.arch_nt}, p0_na={params.p0_na}")
    print("[WARN] A and P0 are trapezoid pilots, not interval-certified.")

    G = build_G(D, params, packet)
    A = build_A(D, params, packet)
    P, shifts = build_P(D, params, packet)
    P0 = build_P0(D, params, packet)

    Pnu = sym(P - P0)
    R = sym(A - P0)
    C = sym(A - P)

    C_from_split = sym(R - Pnu)
    split_err = np.linalg.norm(C - C_from_split, ord="fro")

    Q = build_Q(u)
    N = boundary_null_basis(Q)

    if N.shape[1] == 0:
        raise RuntimeError("Boundary-null subspace is empty. Increase n_centers.")

    Gc = sym(N.T @ G @ N)
    P0c = sym(N.T @ P0 @ N)
    Pnuc = sym(N.T @ Pnu @ N)
    Rc = sym(N.T @ R @ N)
    Cc = sym(N.T @ C @ N)

    q_resid = np.linalg.norm(Q @ N, ord="fro")
    print(f"prime_power_shifts={len(shifts)}")
    print(f"W_L=sum_weights={sum(sh.weight for sh in shifts):.16e}")
    print(f"dim ker(Q)={N.shape[1]}")
    print(f"||Q N||_F={q_resid:.3e}")
    print(f"||C - (R-Pnu)||_F={split_err:.3e}")

    eig_G = np.linalg.eigvalsh(Gc)
    print(f"eig(Gc): min={eig_G[0]:.16e}, max={eig_G[-1]:.16e}")

    eig_negP0_G = generalized_eigs_safe(-P0c, Gc)
    if eig_negP0_G is not None:
        print(
            "eig(-P0c, Gc): "
            f"min={eig_negP0_G[0]:.16e}, max={eig_negP0_G[-1]:.16e}"
        )
    else:
        print("eig(-P0c, Gc): FAILED")

    eig_C_G = generalized_eigs_safe(Cc, Gc)
    if eig_C_G is not None:
        print(
            "eig(Cc, Gc), C=A-P: "
            f"min={eig_C_G[0]:.16e}, max={eig_C_G[-1]:.16e}"
        )
    else:
        print("eig(Cc, Gc): FAILED")

    eig_R = np.linalg.eigvalsh(Rc)
    print(f"eig(Rc=A-P0): min={eig_R[0]:.16e}, max={eig_R[-1]:.16e}")

    if eig_R[0] > 1e-10:
        eig_rel = generalized_eigs_safe(Pnuc, Rc)
        if eig_rel is not None:
            print(
                "eig(Pnuc, Rc): "
                f"min={eig_rel[0]:.16e}, max={eig_rel[-1]:.16e}"
            )
            print(f"relative certificate max<=1 ? {eig_rel[-1] <= 1.0}")
        else:
            print("eig(Pnuc, Rc): FAILED")
    else:
        print("[WARN] Rc not positive definite enough for relative eig(Pnu,R).")

    print(f"||A||_F={np.linalg.norm(A, 'fro'):.16e}")
    print(f"||P||_F={np.linalg.norm(P, 'fro'):.16e}")
    print(f"||P0||_F={np.linalg.norm(P0, 'fro'):.16e}")
    print(f"||Pnu||_F={np.linalg.norm(Pnu, 'fro'):.16e}")


def parse_args() -> PilotParams:
    parser = argparse.ArgumentParser()
    parser.add_argument("--L", type=float, default=3.0)
    parser.add_argument("--ell", type=float, default=0.35)
    parser.add_argument("--delta", type=float, default=0.25)
    parser.add_argument("--k-spline", type=int, default=5)
    parser.add_argument("--arch-tmax", type=float, default=180.0)
    parser.add_argument("--arch-nt", type=int, default=24001)
    parser.add_argument("--p0-na", type=int, default=12001)
    args = parser.parse_args()

    return PilotParams(
        L=args.L,
        ell=args.ell,
        delta=args.delta,
        k_spline=args.k_spline,
        arch_tmax=args.arch_tmax,
        arch_nt=args.arch_nt,
        p0_na=args.p0_na,
    )


if __name__ == "__main__":
    run_pilot(parse_args())
