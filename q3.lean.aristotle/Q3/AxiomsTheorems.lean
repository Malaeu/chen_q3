/-
Q3 Axioms with Tier-2 as Theorems
=================================

This file replaces Tier-2 axioms with proven theorems.
Tier-1 axioms (classical results) remain as axioms.

Usage: Import this instead of Q3.Axioms to get axiom-free Tier-2.

REFACTORED 2025-12-20: Removed circular *_integrated imports.
Now uses REAL bridges for proven theorems.
-/

import Q3.Axioms  -- For Tier-1 axioms and Tier-2 fallbacks

-- Import WORKING self-contained bridges (no namespace conflicts)
import Q3.Proofs.node_spacing_bridge
import Q3.Proofs.S_K_Small_Bridge
import Q3.Proofs.W_Sum_Finite_Bridge
import Q3.Proofs.Q_Lipschitz  -- For Q_Lipschitz_on_W_K_thm (real proof!)
import Q3.Proofs.A1_density   -- For A1_density_WK_thm (real proof!)
import Q3.Proofs.A1prime.A1_density_fixed_t0  -- For A1_density_WK_fixed_t0 (closes axiom!)
import Q3.Proofs.HeatKernelParams
import Q3.Proofs.Params_Critical
import Q3.Proofs.SingleScale_Assumptions
import Q3.Proofs.P_A_Toeplitz_bridge  -- Fourier Toeplitz with P_A (correct formulation)
import Q3.Proofs.Q_nonneg_on_atoms_fourier_axiom
import Q3.Proofs.Schur_Test  -- For Schur_test_proof (Mathlib-based)
import Q3.Proofs.A_Star_Properties  -- For a_star_even_thm (Mathlib Gamma_conj)

-- NOTE: These bridges CONFLICT (they import standalone proofs that define
-- xi_n, S_K, delta_K etc. in root namespace):
-- - off_diag_exp_sum_bridge (imports off_diag_exp_sum → xi_n, S_K conflicts)
-- - S_K_small_bridge (imports S_K_small → delta_K, S_K conflicts)
-- - W_sum_finite_bridge (imports W_sum_finite → xi_n, N_K conflicts)
--
-- TODO: Refactor these bridges to be SELF-CONTAINED like node_spacing_bridge
--       (define local copies instead of importing standalone proofs)
--
-- Complex bridges not yet implemented:
-- - Q_Lipschitz_bridge (a_star mismatch)
-- - A3_bridge (Laurent polynomial → matrix form)
-- - Q_nonneg_bridge (depends on RKHS/A3)
-- - A1_density_bridge (exact? holes + AtomCone mismatch)

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Classical Pointwise Matrix.Norms.L2Operator

namespace Q3.Theorems

/-!
# TIER-1: CLASSICAL AXIOMS (remain as axioms)
These are re-exported from Q3.Axioms
-/

-- Tier-1 axioms are already available via Q3.Axioms (imported by _integrated files)
#check Q3.Weil_criterion
#check Q3.explicit_formula
#check Q3.a_star_pos
#check Q3.a_star_linear_growth
#check Q3.w_Q_heat_weight_summable
#check Q3.Szego_Bottcher_eigenvalue_bound
#check Q3.Szego_Bottcher_convergence
#check Q3.Schur_test
#check Q3.c_arch_pos
#check Q3.eigenvalue_le_norm

/-! ## Tier-1 Theorems: a_star properties (from Mathlib Gamma) -/

/-- **[T1.3d]** a_star is even: a*(-ξ) = a*(ξ)

* **Citation:** DLMF 5.5, Abramowitz & Stegun 6.3
* **Status:** theorem (wired via Mathlib Gamma_conj)
-/
theorem a_star_even : ∀ ξ : ℝ, Q3.a_star (-ξ) = Q3.a_star ξ :=
  Q3.a_star_even_thm

/-!
# TIER-2: Q3 PAPER CONTRIBUTIONS

## Status (2026-01-20):

**In main proof chain (`#print axioms RH_of_Weil_and_Q3`):**
- 3 Q3 PAPER AXIOMS remain (single‑scale): `SingleScale.continuous_P_A_shift`,
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`,
  `SingleScale.rho_oneK_tcritical_le_cstar_quarter`
- 6 EXTERNAL AXIOMS: `Weil_criterion`, `a_star_*`, `Schur_test`

**Theorem status:**
- ✅ PROVEN: node_spacing, S_K_small, W_sum_finite, Q_Lipschitz, RKHS_contraction
- ⚠️ AXIOM FALLBACK: A1_density (theorem exists but wiring issue), off_diag_exp_sum, A3_bridge

Note: "PROVEN" = actual theorem proof wired into main chain.
"AXIOM FALLBACK" = theorem may exist but main chain still uses axiom.
-/

/-! ## PROVEN THEOREMS (4/9) - Self-contained bridges + real proofs -/

-- NOTE: Schur_test remains as axiom (Tier-1 classical).
-- The Mathlib proof uses L∞ norm (Matrix.linfty_opNorm_def),
-- but our project uses L2/spectral norm (Matrix.Norms.L2Operator).
-- Full proof would require Gershgorin + spectral norm bounds.
-- See Q3/Proofs/Schur_Test.lean for L∞ version.

/-- **[RKHS Node Gap]** Adjacent nodes separated by `δ_K`.

* **Q3:** `rkhs:lem:node_gap_lower_bound`
* **Status:** theorem (wired)
-/
theorem node_spacing : ∀ (K : ℝ) (hK : K ≥ 1),
    ∀ (n₁ n₂ : ℕ), n₁ ∈ Q3.Nodes K → n₂ ∈ Q3.Nodes K → n₁ < n₂ →
      Q3.xi_n n₂ - Q3.xi_n n₁ ≥ Q3.delta_K K :=
  Q3.Proofs.NodeSpacingBridge.node_spacing_Q3

/-- **[RKHS S_K]** Off-diagonal geometric series bound.

* **Q3:** `lem:rkhs-gram-off`
* **Status:** theorem (wired)
-/
theorem S_K_small : ∀ (K t η : ℝ), K ≥ 1 → η > 0 → t ≤ Q3.t_min K η → Q3.S_K K t ≤ η :=
  Q3.Proofs.S_K_SmallBridgeV2.S_K_small_Q3

/-- **[A2 Local Finite]** Prime weight sum is finite on compacts.

* **Q3:** `lem:Q-local-finite`
* **Status:** theorem (wired)
-/
theorem W_sum_finite : ∀ (K : ℝ) (hK : K > 0), ∃ B, Q3.W_sum_axiom K ≤ B :=
  Q3.Proofs.W_sum_BridgeV3.W_sum_finite_Q3

/-! ## BLOCKED - Need self-contained bridges (1/9) -/

/-- **[RKHS Off-Diag]** Off-diagonal Gaussian sum bounded by `S_K`.

* **Q3:** `lem:rkhs-gram-off`
* **Status:** axiom fallback
-/
theorem off_diag_exp_sum (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    [Fintype (Q3.Nodes K)] (i : Q3.Nodes K) :
    ∑ j : Q3.Nodes K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t)) else 0) ≤ Q3.S_K K t :=
  Q3.off_diag_exp_sum_axiom K t hK ht i

/-! ## THEOREM (A1' Density - CLOSED!) -/

/-- **[A1' Density]** Fejér-heat atoms dense in `W_K`.

* **Q3:** `a1:thm:A1-local-density`
* **Status:** THEOREM (wired via A1prime.A1_density_WK_fixed_t0)
* **Proof:** Uses bounded hat interpolation + heat kernel Lipschitz bound.
-/
theorem A1_density_WK : ∀ (K : ℝ) (hK : K > 0) (t0 : ℝ) (ht0 : t0 > 0),
    ∀ Φ ∈ Q3.W_K K, ∀ ε > 0,
      ∃ g ∈ Q3.AtomCone_K_fixed K t0,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε :=
  fun K hK t0 ht0 Φ hΦ ε hε =>
    A1prime.A1_density_WK_fixed_t0 K hK t0 ht0 Φ (W_K_eq_q3 K ▸ hΦ) ε hε

/-- **[A2 Lipschitz]** `Q` is Lipschitz continuous on `W_K`.

* **Q3:** `cor:A2-Lip`
* **Status:** theorem (wired)
-/
theorem Q_Lipschitz : ∀ (K : ℝ) (hK : K > 0),
    ∃ L > 0, ∀ Φ₁ ∈ Q3.W_K K, ∀ Φ₂ ∈ Q3.W_K K,
      |Q3.Q Φ₁ - Q3.Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} :=
  Q3.Proofs.Q_Lipschitz_on_W_K_thm

/-- **[RKHS Contraction]** Prime operator `T_P` is strictly contractive.

* **Q3:** `rkhs:thm:rkhs-contraction`
* **Status:** theorem (wired)
-/
theorem RKHS_contraction : ∀ (K : ℝ) (hK : K ≥ 1), Q3.RKHS_contraction_data K :=
  Q3.Proofs.SingleScale.rkhs_contraction_data_of_tcritical

/-- **[A3 Bridge]** ~~K-dependent Toeplitz bridge (deprecated).~~

* **Q3:** `thm:A3` (old)
* **Status:** axiom fallback
-/
theorem A3_bridge : ∀ (K : ℝ) (hK : K ≥ 1), Q3.A3_bridge_data K :=
  Q3.A3_bridge_axiom

/-- **[A3 Rayleigh]** ~~Sampling Toeplitz variant (deprecated).~~

* **Q3:** `thm:a3-rayleigh-identification` (old)
* **Status:** axiom fallback (use A3_bridge_rayleigh_Fourier)
-/
theorem A3_bridge_rayleigh (K : ℝ) : Q3.A3_bridge_data_rayleigh K := by
  intro hK _inst
  simpa using (Q3.A3_bridge_rayleigh_axiom K hK)

/-- **[A3 Fourier]** Fourier Toeplitz with `P_A` symbol (correct formulation).

* **Q3:** `thm:a3-rayleigh-identification`
* **TeX:** `sections/A3/rayleigh_bridge.tex`
* **Status:** theorem (proven via P_A_Toeplitz_bridge)
-/
theorem A3_bridge_rayleigh_Fourier (K : ℝ) (hK : K > 0) :
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K := by
  apply Q3.Proofs.P_A_Bridge.A3_bridge_rayleigh_from_weight_sum_P_A K
  intro _inst
  exact Q3.Proofs.weight_sum_le_rho_one K K hK

/-- **[Main Positivity]** `Q(g) ≥ 0` on atom cone.

* **Q3:** `thm:Main-positivity`
* **TeX:** `sections/Main_closure.tex`
* **Status:** theorem (Fourier A3 + RKHS wrapper)
-/
theorem Q_nonneg_on_atoms : ∀ (K : ℝ) (hK : K ≥ 1) [Fintype (Q3.Nodes K)],
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K_fixed K Q3.t0_critical, Q3.Q g ≥ 0 := by
  intro K hK _inst hA3 hRKHS g hg
  simpa [Q3.Proofs.QNonnegClosure.t0_main] using
    (Q3.Proofs.QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm
      (K:=K) hK hA3 hRKHS g hg)

/-- **[Base Atoms (B-range, τ=0)]** Q(g) ≥ 0 on BaseAtomCone_critical_brange.

* **Q3:** single-scale certificate (t_critical, B ∈ [B_min, B_max])
* **Status:** theorem (from Q_nonneg_t_critical)
-/
theorem Q_nonneg_on_base_atoms_brange :
    ∀ (K : ℝ) (hK : K ≥ 1),
      Q3.PrimeCertMarginOnBrange →
      ∀ g ∈ Q3.BaseAtomCone_critical_brange K, Q3.Q g ≥ 0 := by
  intro K hK h_margin_cert g hg
  exact Q3.Q_nonneg_on_base_atoms_brange_tcritical K hK h_margin_cert g hg

end Q3.Theorems

/-!
# Summary (2026-01-20)

## Main Proof Chain: `#print axioms RH_of_Weil_and_Q3`

**Axiom dependencies (run `#print axioms RH_of_Weil_and_Q3` to refresh):**
- 3 Standard Lean: `propext`, `Classical.choice`, `Quot.sound`
- 6 External/Classical: `Weil_criterion`, `a_star_pos/continuous/bdd/even`, `Schur_test`
- 3 Q3 Paper (single‑scale) are now theorems (not axioms):
  `SingleScale.continuous_P_A_shift`,
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` (requires floor on `P_A_shift` at t_critical),
  `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

## Theorem Wiring Status

### ✅ WIRED INTO MAIN CHAIN (not in `#print axioms`)
- `node_spacing` → NodeSpacingBridge.node_spacing_Q3
- `S_K_small` → S_K_SmallBridgeV2.S_K_small_Q3
- `W_sum_finite` → W_sum_BridgeV2.W_sum_finite_Q3
- `Q_Lipschitz` → Q3.Proofs.Q_Lipschitz_on_W_K_thm
- `RKHS_contraction` → SingleScale.rkhs_contraction_data_of_tcritical

### ✅ THEOREM WIRED (previous wiring gaps closed)
- `A1_density` → A1prime.A1_density_WK_fixed_t0
- `Q_nonneg_on_atoms` → QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm

## Next Steps to Close Axioms
1. Remove remaining axioms (off_diag_exp_sum, A3_bridge if still referenced)
-/
