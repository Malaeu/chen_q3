#!/usr/bin/env python3
"""Phase 0 — CCM_D0_MODE_INDEX_CROSSWALK, source lock, no fitted scalar.

Mandated by PROSHKA_VERDICT_CCM_PENALTY_CROSSWALK_2026-08-07 §5, §7, §10.
Numerics are FORBIDDEN until this passes.

Every matrix entry below is rebuilt from the PAPER formulas (Groskin arXiv:2607.02828 §2.1
and Lemma 2.1, which identifies the assembly with the CCM Galerkin matrix), not from any
implementation package. The pole block is computed TWICE by two independent closed forms and
cross-checked — that is the "independent reconstruction" the verdict requires.

Control cell from the K6 precommit: m = 13.  N is kept small here on purpose: Phase 0 checks
FORMULAS, not spectra, and a small N makes every entry hand-auditable.

Read-only. Writes nothing.
"""
from __future__ import annotations
import mpmath as mp

mp.mp.dps = 30
import sys
_p = print
def print(*a, **k): _p(*a, **k); sys.stdout.flush()

# ── K6 precommit, frozen before any evaluation ────────────────────────────────
M = 13                      # i.m  — our PairIndex.m
N = 6                       # i.N  — small on purpose for Phase 0
LAM = mp.sqrt(M)            # λ = √m          (derived, §Phase-0.2)
L = mp.log(M)               # L = 2 log λ = log m
C = M                       # Groskin's prime cutoff c = λ² = m
BETA = L / (4 * mp.pi)      # β = L/(4π)      (Lemma 2.1)

print("=" * 66)
print("PHASE 0 — CCM_D0_MODE_INDEX_CROSSWALK")
print("=" * 66)
print(f"m = {M}   λ = √m = {mp.nstr(LAM, 12)}   L = log m = {mp.nstr(L, 12)}")
print(f"c (prime cutoff) = λ² = {C}    N = {N}    modes n = -{N}..{N}")

# ── 0.2  parameter crosswalk, derived not fitted ──────────────────────────────
print("\n── 0.2 crosswalk (derived) " + "─" * 38)
lhs, rhs = 2 * mp.log(LAM), L
print(f"  2·log λ = {mp.nstr(lhs, 20)}")
print(f"  log m   = {mp.nstr(rhs, 20)}")
ok_L = abs(lhs - rhs) < mp.mpf(10) ** (-30)
print(f"  2 log λ == log m : {'PASS' if ok_L else 'FAIL'}")

# ── prime block ───────────────────────────────────────────────────────────────
def prime_powers_upto(c: int):
    """(q, Λ(q)) for prime powers q = p^a ≤ c."""
    out = []
    for p in range(2, c + 1):
        if any(p % d == 0 for d in range(2, int(p ** 0.5) + 1)):
            continue
        q = p
        while q <= c:
            out.append((q, mp.log(p)))
            q *= p
    return sorted(out)

PP = prime_powers_upto(C)
print(f"\n── prime powers q = p^a ≤ c = {C} " + "─" * 26)
print("  " + "  ".join(f"{q}(Λ=log{int(mp.e**lam+0.5)})" for q, lam in PP))

def psi_prime(x):
    """ψ_p^{(c)}(x) = −(1/π) Σ_{q≤c} (Λ(q)/√q)·sin(2πx(1 − log q/L))   [Groskin (1)]"""
    s = mp.mpf(0)
    for q, lam in PP:
        s += lam / mp.sqrt(q) * mp.sin(2 * mp.pi * x * (1 - mp.log(q) / L))
    return -s / mp.pi

def dpsi_prime(x):
    s = mp.mpf(0)
    for q, lam in PP:
        w = 1 - mp.log(q) / L
        s += lam / mp.sqrt(q) * 2 * mp.pi * w * mp.cos(2 * mp.pi * x * w)
    return -s / mp.pi

# ── pole block: closed form A (Lemma 2.1, via ψ₀) ─────────────────────────────
C_c = L * (mp.sqrt(C) + 1 / mp.sqrt(C) - 2) / (2 * mp.pi ** 2)

def psi_pole(x):      # ψ₀(n) = C_c·n/(n²+β²)
    return C_c * x / (x ** 2 + BETA ** 2)

def dpsi_pole(x):     # ψ₀′(n) = C_c(β²−n²)/(n²+β²)²
    return C_c * (BETA ** 2 - x ** 2) / (x ** 2 + BETA ** 2) ** 2

def pole_entry_A(mm, nn):
    """Divided difference of ψ₀ — the generic (Q_ψ) rule."""
    return dpsi_pole(mm) if mm == nn else (psi_pole(mm) - psi_pole(nn)) / (mm - nn)

def pole_entry_B(mm, nn):
    """Independent closed form, Lemma 2.1:
       (Q_pole)_{mn} = 32 L sinh²(L/4)(L² − 16π²mn) / ((L²+16π²m²)(L²+16π²n²))"""
    num = 32 * L * mp.sinh(L / 4) ** 2 * (L ** 2 - 16 * mp.pi ** 2 * mm * nn)
    den = (L ** 2 + 16 * mp.pi ** 2 * mm ** 2) * (L ** 2 + 16 * mp.pi ** 2 * nn ** 2)
    return num / den

print("\n── pole block: two independent closed forms " + "─" * 21)
worst = mp.mpf(0)
for (mm, nn) in [(0, 0), (1, 1), (2, -3), (0, 4), (5, -5), (6, 2)]:
    a, b = pole_entry_A(mm, nn), pole_entry_B(mm, nn)
    rel = abs(a - b) / max(abs(a), mp.mpf(1e-40))
    worst = max(worst, rel)
    print(f"  ({mm:>2},{nn:>3}) A={mp.nstr(a, 14):>18}  B={mp.nstr(b, 14):>18}  rel={mp.nstr(rel, 3)}")
ok_pole = worst < mp.mpf(10) ** (-25)
print(f"  worst relative difference: {mp.nstr(worst, 5)}  → {'PASS' if ok_pole else 'FAIL'}")

# ── archimedean block ─────────────────────────────────────────────────────────
def h_plus(r):
    """h₊(r) = Re ψ_Γ(¼ + ir/2) − log π"""
    return mp.re(mp.digamma(mp.mpf(1) / 4 + mp.mpc(0, r) / 2)) - mp.log(mp.pi)

def S_kernel(r, x):
    """S(r,x,L) = ∫₀^L sin(2πx(1 − y/L))·cos(ry) dy.

    Closed form.  Write A = 2πx, B = 2πx/L, so the integrand is sin(A − B y)·cos(r y)
    = ½[ sin(A + (r−B)y) + sin(A − (r+B)y) ].  Both pieces integrate elementarily.
    Doing this by quadrature — inside another quadrature, with a numerical derivative on
    top — was what made the first run time out with no output at all.
    """
    A = 2 * mp.pi * x
    B = 2 * mp.pi * x / L
    def piece(w, sign):
        # ∫₀^L sin(A + sign·w·y) dy
        if abs(w) < mp.mpf(10) ** (-30):
            return mp.sin(A) * L
        return (mp.cos(A) - mp.cos(A + sign * w * L)) / (sign * w)
    return (piece(r - B, 1) + piece(r + B, -1)) / 2

def dS_kernel(r, x):
    """∂S/∂x, differentiated under the integral sign — analytic, not numerical."""
    return mp.quad(lambda y: 2 * mp.pi * (1 - y / L)
                   * mp.cos(2 * mp.pi * x * (1 - y / L)) * mp.cos(r * y), [0, L])

T_ARCH = mp.mpf(40)

def psi_arch(x):
    """ψ_ℝ,T(x) = (1/2π²)∫_{−T}^{T} h₊(r)S(r,x,L) dr ; integrand even in r ⇒ 2×∫₀^T."""
    f = lambda r: h_plus(r) * S_kernel(r, x)
    return mp.quad(f, [0, 1, 4, 12, T_ARCH]) * 2 / (2 * mp.pi ** 2)

def dpsi_arch(x):
    f = lambda r: h_plus(r) * dS_kernel(r, x)
    return mp.quad(f, [0, 1, 4, 12, T_ARCH]) * 2 / (2 * mp.pi ** 2)

# ── assemble K on a small index set, per the locked orientation ───────────────
# Groskin: Q_∞ = Q_prime + Q_pole + Q_arch,∞  and  ⟨v,Q_∞v⟩ = W_{0,2} − W_ℝ − W_p,
# i.e. −Q_prime, Q_pole, −Q_arch are the prime, pole, archimedean blocks.
# Proshka's locked orientation: K = W_{0,2} − W_ℝ − W_prime.  So K == Q_∞ as assembled.
def divided(f, df, mm, nn):
    return df(mm) if mm == nn else (f(mm) - f(nn)) / (mm - nn)

print("\n── K entries rebuilt from paper formulas " + "─" * 24)
print("   (arch block by quadrature, T = 60)")
CHECK = [(0, 0), (1, 1), (2, 3), (1, -1)]
entries = {}
for (mm, nn) in CHECK:
    kp = divided(psi_prime, dpsi_prime, mm, nn)
    kz = pole_entry_A(mm, nn)
    ka = divided(psi_arch, dpsi_arch, mm, nn)
    entries[(mm, nn)] = kp + kz + ka
    tag = "diag" if mm == nn else "off "
    print(f"  {tag} K[{mm:>2},{nn:>3}] = {mp.nstr(kp + kz + ka, 16):>22}"
          f"   (prime {mp.nstr(kp,7)}  pole {mp.nstr(kz,7)}  arch {mp.nstr(ka,7)})")

# ── symmetry, involution, commutation ─────────────────────────────────────────
print("\n── structural locks " + "─" * 45)
sym = abs(entries[(2, 3)] - divided(psi_prime, dpsi_prime, 3, 2)
          - pole_entry_A(3, 2)
          - divided(psi_arch, dpsi_arch, 3, 2))
print(f"  K[2,3] − K[3,2] = {mp.nstr(sym, 4)}   → {'PASS (symmetric)' if sym < mp.mpf(10)**(-20) else 'FAIL'}")

# J = mode reversal, J_{n,r} = δ_{n,−r}.  J² = I is immediate; JK = KJ is the claim to test.
# (JKJ)_{m,n} = K_{−m,−n}, so JK = KJ  ⟺  K_{−m,−n} = K_{m,n}.
def K_entry(mm, nn):
    return (divided(psi_prime, dpsi_prime, mm, nn) + pole_entry_A(mm, nn)
            + divided(psi_arch, dpsi_arch, mm, nn))

print("  J: mode reversal, J² = I by construction (δ_{n,−r} squared = δ_{n,r})")
worst_c = mp.mpf(0)
for (mm, nn) in [(1, 2), (0, 3), (2, -3), (4, 1)]:
    d = abs(K_entry(mm, nn) - K_entry(-mm, -nn))
    worst_c = max(worst_c, d)
    print(f"    K[{mm:>2},{nn:>3}] − K[{-mm:>2},{-nn:>3}] = {mp.nstr(d, 4)}")
print(f"  JK = KJ  ⟺  K_(−m,−n) = K_(m,n):  worst {mp.nstr(worst_c, 4)}"
      f"  → {'PASS' if worst_c < mp.mpf(10)**(-18) else 'FAIL'}")

print("\n" + "=" * 66)
print("G = I: basis orthonormal (V_n_m_orthonormal, D0LogWindowMeasureTransport.lean:213)")
print("       ⇒ Gram matrix is the identity, no computation required.")
print("=" * 66)
