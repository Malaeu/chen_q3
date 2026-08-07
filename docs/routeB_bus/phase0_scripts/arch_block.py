#!/usr/bin/env python3
"""Archimedean block of the truncated Weil matrix — head + integration-by-parts tail.

Technique borrowed from Groskin's ranktwo_tail (arXiv:2607.02828 package): the smooth part
on a GEOMETRIC mesh, the oscillating part by two integrations by parts so that cos(Lr) is
never quadratured. The formulas and the code here are ours; only the method is theirs.

Target: reproduce route2_arch = 0.047697482652328006439872417749 for the reference vector at
c = 13, N = 4 (threeroute_c13N4_package.json), computed independently.

  ψ_arch(x) = (1/π²) ∫₀^∞ h₊(r)·S(r,x,L) dr
  h₊(r)     = Re ψ_Γ(¼ + ir/2) − log π
  S(r,x,L)  = B(cos A − cos rL)/(r² − B²),  A = 2πx, B = A/L      [exact, BL = A]

The r = B point is a removable 0/0 — handled through the sine form.
"""
from __future__ import annotations
import json
import mpmath as mp

mp.mp.dps = 30

C = 13
L = mp.log(C)
N = 4
T0 = mp.mpf(40)          # head/tail split
NPER = 60                # periods for the remainder integral, as in their ranktwo_tail


def h_plus(r):
    return mp.re(mp.digamma(mp.mpf(1) / 4 + mp.mpc(0, r) / 2)) - mp.log(mp.pi)


def sinc(z):
    return mp.mpf(1) if abs(z) < mp.mpf(10) ** -25 else mp.sin(z) / z


def S_stable(r, x):
    """Exact kernel, singularity-free at r = B."""
    A = 2 * mp.pi * x
    B = A / L
    half = L * (r - B) / 2
    t1 = L * mp.sin((A + r * L) / 2) * sinc(half)
    t2 = (-2 * mp.sin((r * L + A) / 2) * mp.sin(half) / (r + B)
          if abs(r + B) > mp.mpf(10) ** -25 else mp.mpf(0))
    return (t1 + t2) / 2


def psi_arch(x):
    """Head by quadrature, tail split into smooth + oscillating, the latter by parts."""
    x = mp.mpf(x)
    A = 2 * mp.pi * x
    B = A / L
    if abs(x) < mp.mpf(10) ** -30:
        return mp.mpf(0), mp.mpf(0)           # B = 0 ⇒ S ≡ 0

    head = mp.quad(lambda r: h_plus(r) * S_stable(r, x), [0, 1, 4, 12, 25, T0])

    # smooth half of the tail: B·cos A/(r² − B²) — geometric mesh, integrand ~ log r / r²
    smooth = mp.quad(lambda r: h_plus(r) * B * mp.cos(A) / (r * r - B * B),
                     [T0, 2 * T0, 8 * T0, 64 * T0, 1024 * T0, mp.inf])

    # oscillating half: −B·cos(Lr)/(r² − B²), twice by parts.
    #   ∫_T0^∞ H cos(Lr) dr = −H(T0)sin(LT0)/L − H'(T0)cos(LT0)/L² − (1/L²)∫_T0^∞ H''cos(Lr)dr
    H = lambda r: -h_plus(r) * B / (r * r - B * B)
    dH = lambda r: mp.diff(H, r)
    d2H = lambda r: mp.diff(H, r, 2)
    b1 = -H(T0) * mp.sin(L * T0) / L
    b2 = -dH(T0) * mp.cos(L * T0) / L ** 2
    per = 2 * mp.pi / L
    pts = [T0 + k * per for k in range(NPER + 1)]
    rem = -(1 / L ** 2) * mp.quad(lambda r: d2H(r) * mp.cos(L * r), pts)
    R = pts[-1]
    rem_bound = (1 / L ** 2) * mp.quad(lambda r: abs(d2H(r)), [R, 4 * R, 64 * R, mp.inf])
    osc = b1 + b2 + rem

    return (head + smooth + osc) / mp.pi ** 2, rem_bound / mp.pi ** 2


def main():
    ref = json.load(open("gwpkg/threeroute_c13N4_package.json"))
    v = [mp.mpf(s) for s in ref["v"]]
    u = {0: v[0]}
    for k in range(1, N + 1):
        u[k] = u[-k] = v[k] / mp.sqrt(2)

    print("archimedean block — ψ_arch(x) for x = 0..N, head+parts tail")
    vals, bounds = {}, {}
    for x in range(0, N + 1):
        val, bnd = psi_arch(x)
        vals[x], bounds[x] = val, bnd
        vals[-x] = -val          # S is odd in x ⇒ ψ_arch odd
        print(f"  x={x}   ψ={mp.nstr(val, 20):>24}   rem_bound={mp.nstr(bnd, 4)}")

    # derivative on the diagonal, by the same construction
    def dpsi(x):
        return mp.diff(lambda t: psi_arch(t)[0], mp.mpf(x))

    idx = range(-N, N + 1)
    total = mp.mpf(0)
    for m in idx:
        for n in idx:
            q = dpsi(m) if m == n else (vals[m] - vals[n]) / (m - n)
            total += u[m] * u[n] * q

    theirs = mp.mpf(ref["route2_arch"])
    print(f"\n  my  <v, Q_arch v> = {mp.nstr(total, 24)}")
    print(f"  their route2_arch = {mp.nstr(theirs, 24)}")
    print(f"  difference        = {mp.nstr(total - theirs, 6)}")
    print(f"  also with sign flipped: {mp.nstr(-total - theirs, 6)}")
    print(f"  their tail bound  = {ref['route2_tail_rem_bound']}")


if __name__ == "__main__":
    main()
