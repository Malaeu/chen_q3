/-
Q_nonneg on BaseAtomCone_K (τ = 0 only)
========================================

This file defines the positivity axiom/theorem for BaseAtomCone_K.

**Patch A Resolution (Proshka Analysis 2026-01-19):**
The A3 bridge uses fixed symbol P_A(B, t) without τ-shift.
BaseAtomCone_K aligns directly with this: τ = 0 for all atoms.

Architecture:
1. `Q_nonneg_on_BaseAtomCone_axiom` — Q ≥ 0 on base atoms (τ = 0)
2. τ-transfer from BaseAtomCone to AtomCone_K_fixed via A2 Lipschitz
3. T5_Transfer: full W_K coverage via density + Lipschitz
-/

import Q3.Axioms
import Q3.Proofs.HeatKernelParams

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3

/-! ## Axiom: Q ≥ 0 on BaseAtomCone_K

This axiom states that Q is nonnegative on the restricted cone where τ = 0.
Unlike the full `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` which has a parameter
mismatch (A3 uses P_A without τ, but atoms have arbitrary τ), this axiom aligns
directly with the A3 bridge.

**Proof sketch (to be formalized):**
1. For τ = 0: Fejer_heat_atom B t0_A1 0 = (2 * heat_scaling) * fejer_heat_window B t_sym
2. `honest_formula`: Q(fejer_heat_window) relates to Rayleigh quotient RQ(Toeplitz[P_A] - T_P_comp)
3. A3 bridge: RQ(Toeplitz[P_A] - T_P_comp) ≥ c_star/4
4. RKHS cap: prime_sum ≤ rho_one
5. Combined: Q(fejer_heat_window) ≥ c_star/4 - rho_one ≥ 0
6. Linearity extends to BaseAtomCone_K
-/

/-- Core positivity on BaseAtomCone_K (τ = 0 only).

This axiom aligns with the A3 bridge which uses P_A(B, t) without τ-shift.
The full τ-transfer to AtomCone_K_fixed is handled separately.

**Difference from Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom:**
- That axiom claims Q ≥ 0 on AtomCone_K_fixed (arbitrary τ)
- This axiom claims Q ≥ 0 on BaseAtomCone_K (τ = 0 only)
- BaseAtomCone_K matches the A3 bridge's parameter structure exactly
-/
axiom Q_nonneg_on_BaseAtomCone_axiom :
  ∀ (K : ℝ) (hK : K ≥ 1),
    ∀ g ∈ BaseAtomCone_K K t0_A1, Q g ≥ 0

/-- Theorem wrapper for the axiom. -/
theorem Q_nonneg_on_BaseAtomCone (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ BaseAtomCone_K K t0_A1, Q g ≥ 0 :=
  Q_nonneg_on_BaseAtomCone_axiom K hK

end Q3
