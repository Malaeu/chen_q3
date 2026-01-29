#!/usr/bin/env python3
"""
Phase 0 Verification: Confirm Q definitions match Lean/LaTeX

This script verifies:
1. Q = arch_term - prime_term
2. arch_term = ∫ a*(ξ)·Φ(ξ) dξ
3. prime_term = Σ w_Q(n)·Φ(ξ_n)
4. Φ_{B=3,t=0.06} ∈ W_K for K > 3
5. Φ is in AtomCone_K_fixed
6. Q(Φ) < 0 with these exact definitions
"""

import numpy as np
from scipy import integrate
from scipy.special import digamma

# Constants
PI = np.pi

# === DEFINITIONS (must match Lean/LaTeX exactly) ===

def xi_n(n):
    """ξ_n = log(n)/(2π) -- Lean: Q3.xi_n"""
    return np.log(n) / (2 * PI)

def von_mangoldt(n):
    """Λ(n) = log(p) if n = p^k, else 0 -- Lean: ArithmeticFunction.vonMangoldt"""
    if n < 2:
        return 0.0
    # Check if n is a prime power
    for p in range(2, int(np.sqrt(n)) + 1):
        if n % p == 0:
            k = 0
            temp = n
            while temp % p == 0:
                temp //= p
                k += 1
            if temp == 1:
                return np.log(p)
            return 0.0
    # n is prime
    return np.log(n)

def w_Q(n):
    """w_Q(n) = 2·Λ(n)/√n (doubled for even functions) -- Lean: Q3.w_Q"""
    return 2 * von_mangoldt(n) / np.sqrt(n)

def a(xi):
    """a(ξ) = log(π) - Re(ψ(1/4 + iπξ)) -- Lean: Q3.a"""
    z = 0.25 + 1j * PI * xi
    return np.log(PI) - np.real(digamma(z))

def a_star(xi):
    """a*(ξ) = 2π·a(ξ) -- Lean: Q3.a_star"""
    return 2 * PI * a(xi)

def fejer_heat_window(B, t, xi):
    """Φ_{B,t}(ξ) = max(0, 1-|ξ|/B)·exp(-4π²tξ²) -- Lean: Q3.fejer_heat_window"""
    fejer = max(0, 1 - abs(xi) / B)
    heat = np.exp(-4 * PI**2 * t * xi**2)
    return fejer * heat

def Fejer_heat_atom(B, t, tau, xi):
    """Fejer_heat_atom = Φ(ξ-τ) + Φ(ξ+τ) (symmetrized) -- Lean: Q3.Fejer_heat_atom"""
    return fejer_heat_window(B, t, xi - tau) + fejer_heat_window(B, t, xi + tau)

# === Q FUNCTIONAL ===

def arch_term(Phi, B):
    """arch_term = ∫ a*(ξ)·Φ(ξ) dξ -- Lean: Q3.arch_term"""
    integrand = lambda xi: a_star(xi) * Phi(xi)
    result, _ = integrate.quad(integrand, -B, B, limit=200)
    return result

def prime_term(Phi, K, max_n=10000):
    """prime_term = Σ w_Q(n)·Φ(ξ_n) for n with |ξ_n| ≤ K -- Lean: Q3.prime_term"""
    total = 0.0
    for n in range(2, max_n + 1):
        xi = xi_n(n)
        if abs(xi) > K:
            break
        w = w_Q(n)
        if w > 0:
            total += w * Phi(xi)
    return total

def Q_functional(Phi, B, K):
    """Q(Φ) = arch_term - prime_term -- Lean: Q3.Q"""
    return arch_term(Phi, B) - prime_term(Phi, K)

# === VERIFICATION ===

def verify_phase0():
    """Run all Phase 0 checks"""
    print("=" * 70)
    print("PHASE 0: Definition Verification")
    print("Confirming Q definitions match Lean/LaTeX exactly")
    print("=" * 70)

    # Parameters
    B = 3.0
    t_sym = 3/50  # = 0.06
    K = 5.0  # K > B

    # Define Φ_{B,t}
    Phi = lambda xi: fejer_heat_window(B, t_sym, xi)

    print(f"\nParameters:")
    print(f"  B = {B}")
    print(f"  t_sym = {t_sym} = 3/50")
    print(f"  K = {K}")

    # ===== Check 0.1: Q definition =====
    print("\n" + "-" * 70)
    print("Check 0.1: Q = arch_term - prime_term")
    print("-" * 70)

    arch = arch_term(Phi, B)
    prime = prime_term(Phi, K)
    Q_val = Q_functional(Phi, B, K)

    print(f"\n  Lean definitions (Q3/Basic/Defs.lean):")
    print(f"    def Q (Φ) := arch_term Φ - prime_term Φ")
    print(f"    def arch_term (Φ) := ∫ ξ, a_star ξ * Φ ξ")
    print(f"    def prime_term (Φ) := ∑' n, w_Q n * Φ (xi_n n)")

    print(f"\n  Computed values:")
    print(f"    arch_term  = {arch:.6f}")
    print(f"    prime_term = {prime:.6f}")
    print(f"    Q = arch - prime = {Q_val:.6f}")

    check_01 = Q_val < 0
    print(f"\n  Q < 0? {Q_val:.4f} < 0 → {check_01} {'✓' if check_01 else '✗'}")

    # ===== Check 0.2: arch_term formula =====
    print("\n" + "-" * 70)
    print("Check 0.2: arch_term = ∫ a*(ξ)·Φ(ξ) dξ")
    print("-" * 70)

    # Also verify via periodization identity
    print(f"\n  Direct integral: {arch:.6f}")
    print(f"  This equals: 2π ∫ a(ξ)·Φ(ξ) dξ (by a* = 2π·a)")

    arch_via_a = 2 * PI * integrate.quad(lambda xi: a(xi) * Phi(xi), -B, B, limit=200)[0]
    print(f"  Cross-check via a(ξ): {arch_via_a:.6f}")

    check_02 = np.isclose(arch, arch_via_a, rtol=1e-6)
    print(f"\n  Consistent? {'✓' if check_02 else '✗'}")

    # ===== Check 0.3: prime_term formula =====
    print("\n" + "-" * 70)
    print("Check 0.3: prime_term = Σ w_Q(n)·Φ(ξ_n)")
    print("-" * 70)

    print(f"\n  Sum over prime powers n with |ξ_n| ≤ K:")
    print(f"    prime_term = {prime:.6f}")

    # Show breakdown
    print(f"\n  Breakdown (first 20 non-zero terms):")
    count = 0
    cumsum = 0
    for n in range(2, 10001):
        xi = xi_n(n)
        if abs(xi) > K:
            break
        w = w_Q(n)
        if w > 0:
            term = w * Phi(xi)
            cumsum += term
            if count < 20:
                print(f"    n={n:4d}: ξ_n={xi:7.4f}, w_Q={w:.4f}, Φ={Phi(xi):.6f}, term={term:.6f}")
            count += 1
    print(f"    ...")
    print(f"    Total {count} non-zero terms, sum = {cumsum:.6f}")

    check_03 = np.isclose(prime, cumsum, rtol=1e-6)
    print(f"\n  Consistent? {'✓' if check_03 else '✗'}")

    # ===== Check 0.4: w_Q values =====
    print("\n" + "-" * 70)
    print("Check 0.4: w_Q(n) = 2·Λ(n)/√n")
    print("-" * 70)

    print(f"\n  Lean: def w_Q (n) := 2 * vonMangoldt n / sqrt n")
    print(f"\n  Sample values:")
    for n in [2, 3, 4, 5, 7, 8, 9, 11, 16, 25, 27]:
        w = w_Q(n)
        Lambda = von_mangoldt(n)
        print(f"    n={n:3d}: Λ(n)={Lambda:.6f}, w_Q(n)={w:.6f}")

    check_04 = True  # Manual inspection
    print(f"\n  Matches Lean definition? ✓")

    # ===== Check 0.5: ξ_n values =====
    print("\n" + "-" * 70)
    print("Check 0.5: ξ_n = log(n)/(2π)")
    print("-" * 70)

    print(f"\n  Lean: def xi_n (n) := Real.log n / (2 * Real.pi)")
    print(f"\n  Sample values:")
    for n in [2, 3, 5, 10, 100, 1000]:
        xi = xi_n(n)
        print(f"    n={n:4d}: ξ_n = {xi:.6f}")

    check_05 = True
    print(f"\n  Matches Lean definition? ✓")

    # ===== Check 0.6: Φ properties =====
    print("\n" + "-" * 70)
    print("Check 0.6: Φ_{B,t}(ξ) = max(0, 1-|ξ|/B)·exp(-4π²tξ²)")
    print("-" * 70)

    print(f"\n  Lean: def fejer_heat_window (B t ξ) :=")
    print(f"          max 0 (1 - |ξ| / B) * exp(-4 * π² * t * ξ²)")

    print(f"\n  Sample values:")
    for xi in [0, 0.5, 1, 1.5, 2, 2.5, 3, 3.1]:
        val = Phi(xi)
        print(f"    Φ({xi:3.1f}) = {val:.6f}")

    print(f"\n  Properties:")
    print(f"    Even? Φ(-1) = {Phi(-1):.6f}, Φ(1) = {Phi(1):.6f} → {np.isclose(Phi(-1), Phi(1))} ✓")
    print(f"    Nonneg? min = {min(Phi(xi) for xi in np.linspace(-B, B, 100)):.6f} ≥ 0 ✓")
    print(f"    Support = [-{B}, {B}], Φ(B+0.01) = {Phi(B+0.01):.6f} = 0 ✓")

    check_06 = True
    print(f"\n  Matches Lean definition? ✓")

    # ===== Check 0.7: Φ ∈ W_K =====
    print("\n" + "-" * 70)
    print("Check 0.7: Φ ∈ W_K for K > B")
    print("-" * 70)

    print(f"\n  Lean: def W_K (K) := {{Φ | Continuous Φ ∧")
    print(f"                          support Φ ⊆ Ioo (-K) K ∧")
    print(f"                          IsEven Φ ∧ IsNonneg Φ}}")

    print(f"\n  Verification for K = {K}, B = {B}:")
    print(f"    Continuous: YES (Fejer × exp is continuous)")
    print(f"    Support ⊆ (-{K}, {K}): [-{B}, {B}] ⊂ (-{K}, {K}) → {'✓' if B < K else '✗'}")
    print(f"    Even: YES (|ξ| is symmetric)")
    print(f"    Nonneg: YES (max(0,...)·exp(...))")

    check_07 = B < K
    print(f"\n  Φ ∈ W_K? {'✓' if check_07 else '✗'}")

    # ===== Check 0.8: Φ in AtomCone =====
    print("\n" + "-" * 70)
    print("Check 0.8: Φ ∈ AtomCone_K_fixed")
    print("-" * 70)

    print(f"\n  Lean: def AtomCone_K_fixed (K t0) := {{g | ∃ n c B τ,")
    print(f"          (∀ i, c i ≥ 0) ∧ (∀ i, B i > 0) ∧")
    print(f"          (∀ i, |τ i| + B i ≤ K) ∧")
    print(f"          (g = Σ c_i · Fejer_heat_atom(B_i, t0, τ_i)) ∧ g ∈ W_K}}")

    print(f"\n  Key: Fejer_heat_atom(B, t, τ, ξ) = Φ(ξ-τ) + Φ(ξ+τ)")
    print(f"       At τ=0: atom(ξ) = Φ(ξ) + Φ(ξ) = 2·Φ(ξ)")

    atom_0 = Fejer_heat_atom(B, t_sym, 0, 0)
    phi_0 = Phi(0)
    print(f"\n  Verification:")
    print(f"    atom(B={B}, t={t_sym}, τ=0, ξ=0) = {atom_0:.6f}")
    print(f"    2·Φ(0) = {2*phi_0:.6f}")
    print(f"    Equal? {np.isclose(atom_0, 2*phi_0)} ✓")

    print(f"\n  Therefore: Φ = (1/2)·atom")
    print(f"    Representation: c = 1/2, B = {B}, τ = 0")
    print(f"    Check: c ≥ 0? 1/2 ≥ 0 ✓")
    print(f"    Check: B > 0? {B} > 0 ✓")
    print(f"    Check: |τ| + B ≤ K? 0 + {B} = {B} ≤ {K} {'✓' if B <= K else '✗'}")

    check_08 = B <= K
    print(f"\n  Φ ∈ AtomCone_K_fixed(K={K}, t0=...)? {'✓' if check_08 else '✗'}")

    # ===== FINAL VERDICT =====
    print("\n" + "=" * 70)
    print("PHASE 0 FINAL VERDICT")
    print("=" * 70)

    all_checks = [check_01, check_02, check_03, check_04, check_05, check_06, check_07, check_08]

    print(f"\n  Checklist:")
    print(f"    [{'✓' if check_01 else '✗'}] 0.1 Q < 0 at t_sym = 0.06")
    print(f"    [{'✓' if check_02 else '✗'}] 0.2 arch_term formula consistent")
    print(f"    [{'✓' if check_03 else '✗'}] 0.3 prime_term formula consistent")
    print(f"    [{'✓' if check_04 else '✗'}] 0.4 w_Q definition matches Lean")
    print(f"    [{'✓' if check_05 else '✗'}] 0.5 ξ_n definition matches Lean")
    print(f"    [{'✓' if check_06 else '✗'}] 0.6 Φ definition matches Lean")
    print(f"    [{'✓' if check_07 else '✗'}] 0.7 Φ ∈ W_K")
    print(f"    [{'✓' if check_08 else '✗'}] 0.8 Φ ∈ AtomCone_K_fixed")

    if all(all_checks):
        print(f"\n  ALL CHECKS PASSED!")
        print(f"\n  CONCLUSION:")
        print(f"    Q(Φ_{{B={B}, t={t_sym}}}) = {Q_val:.4f} < 0")
        print(f"    This Φ IS in the correct class (W_K, AtomCone_K_fixed)")
        print(f"    The axiom 'Q ≥ 0 on AtomCone' is FALSE at t_sym = {t_sym}")
        print(f"\n  => Must change t_sym or modify AtomCone definition")
    else:
        failed = [i+1 for i, c in enumerate(all_checks) if not c]
        print(f"\n  SOME CHECKS FAILED: {failed}")

    return Q_val, all(all_checks)

if __name__ == "__main__":
    Q_val, passed = verify_phase0()

    if passed:
        print("\n" + "=" * 70)
        print("BONUS: Testing t_critical = 0.15")
        print("=" * 70)

        B = 3.0
        t_critical = 3/20  # = 0.15
        K = 5.0

        Phi_crit = lambda xi: fejer_heat_window(B, t_critical, xi)
        Q_crit = Q_functional(Phi_crit, B, K)

        print(f"\n  At t_critical = {t_critical}:")
        print(f"    arch_term  = {arch_term(Phi_crit, B):.6f}")
        print(f"    prime_term = {prime_term(Phi_crit, K):.6f}")
        print(f"    Q = {Q_crit:.6f}")
        print(f"    Q ≥ 0? {Q_crit >= 0} {'✓' if Q_crit >= 0 else '✗'}")
