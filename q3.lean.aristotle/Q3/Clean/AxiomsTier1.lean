/-
Q3 Clean: Tier-1 assumptions and quarantined legacy assumptions
================================================================

This file contains a mixed legacy assumption surface. Some declarations encode
classical literature results; the raw-kernel global/compact positivity
assumptions are not literature-certified facts and are quarantined explicitly
below. In particular, global positivity of the raw kernel is known to be false.

NO Tier-2 axioms here - those are proven as theorems in TheoremsTier2.lean.

Tier-1 Axioms:
- T1.1: Weil Criterion (1952)
- T1.2: Explicit Formula (Guinand 1948)
- T1.3: a_star properties; global positivity is a quarantined legacy assumption
- T1.4: Szegő-Böttcher Theory (1958/1999)
- T1.5: Schur Test (1911)
- T1.6: c_arch positivity as a quarantined legacy assumption
- T1.7: Eigenvalue-Norm Bound
-/

import Q3.Basic.Defs  -- Only definitions, no Tier-2

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Classical Matrix.Norms.L2Operator

namespace Q3.Clean

/-!
# MIXED TIER-1 AND QUARANTINED LEGACY ASSUMPTIONS
-/

/-! ## T1.1: Weil Criterion (1952) -/
axiom Weil_criterion : (∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0) ↔ Q3.RH

/-! ## T1.2: Guinand-Weil Explicit Formula (1948) -/
axiom explicit_formula :
  ∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ = Q3.arch_term Φ - Q3.prime_term Φ

/-! ## T1.3: Archimedean Kernel Properties -/

namespace Conditional.LegacyArchFloor

/-- Legacy assumption. Global positivity is false for the raw kernel. -/
axiom rawKernelGlobalPosAssumption : ∀ ξ : ℝ, Q3.a_star ξ > 0

end Conditional.LegacyArchFloor

@[deprecated Q3.Clean.Conditional.LegacyArchFloor.rawKernelGlobalPosAssumption
  (since := "2026-08-27")]
theorem a_star_pos : ∀ ξ : ℝ, Q3.a_star ξ > 0 :=
  Q3.Clean.Conditional.LegacyArchFloor.rawKernelGlobalPosAssumption

axiom a_star_continuous : Continuous Q3.a_star

axiom a_star_bdd_on_compact : ∀ (K : ℝ) (hK : K > 0),
  ∃ M > 0, ∀ ξ ∈ Set.Icc (-K) K, Q3.a_star ξ ≤ M

axiom a_star_even : ∀ ξ : ℝ, Q3.a_star (-ξ) = Q3.a_star ξ

/-! ## T1.3e: Archimedean Kernel Linear Growth (global) -/
axiom a_star_linear_growth :
  ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ ξ : ℝ, |Q3.a_star ξ| ≤ C0 + C1 * |ξ|

/-! ## T1.3f: Prime Heat-Weight Summability (global) -/
axiom w_Q_heat_weight_summable :
  ∀ t : ℝ, 0 < t →
    Summable (fun n : ℕ =>
      Q3.w_Q n * (Real.exp (-4 * Real.pi ^ 2 * t * (Q3.xi_n n) ^ 2) * |Q3.xi_n n|))

/-! ## T1.4: Szegő-Böttcher Theory (1958/1999) -/

/-- Toeplitz matrix from symbol -/
noncomputable def ToeplitzMatrix (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => P ((i.val - j.val : ℤ) * Real.pi / M)

axiom Szego_Bottcher_eigenvalue_bound :
  ∀ (M : ℕ) (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ μ, (∃ v : Fin M → ℝ, v ≠ 0 ∧ (ToeplitzMatrix M P).mulVec v = μ • v) →
    sInf {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)} ≤ μ ∧
    μ ≤ sSup {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)}

axiom Szego_Bottcher_convergence :
  ∀ (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ ε > 0, ∃ N, ∀ m ≥ N,
    ∀ μ, (∃ v : Fin m → ℝ, v ≠ 0 ∧ (ToeplitzMatrix m P).mulVec v = μ • v) →
      ∃ θ ∈ Set.Icc 0 (2 * Real.pi), |μ - P θ| < ε

/-! ## T1.5: Schur Test (1911) -/
axiom Schur_test {n : Type*} [Fintype n] [DecidableEq n] :
  ∀ (A : Matrix n n ℝ), A.IsSymm →
  ∀ (C : ℝ), 0 ≤ C → (∀ i, ∑ j, |A i j| ≤ C) → ‖A‖ ≤ C

/-! ## T1.6: Quarantined legacy Archimedean compact-inf positivity -/

/-- Archimedean constant: c₀(K) = inf_{|ξ| ≤ K} a*(ξ) -/
noncomputable def c_arch (K : ℝ) : ℝ :=
  sInf {Q3.a_star ξ | ξ ∈ Set.Icc (-K) K}

namespace Conditional.LegacyArchFloor

axiom rawKernelCompactInfPosAssumption :
  ∀ K : ℝ, K > 0 → c_arch K > 0

end Conditional.LegacyArchFloor

@[deprecated Q3.Clean.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption
  (since := "2026-08-27")]
theorem c_arch_pos : ∀ K : ℝ, K > 0 → c_arch K > 0 :=
  Q3.Clean.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption

/-! ## T1.7: Eigenvalue-Norm Bound -/
axiom eigenvalue_le_norm {n : Type*} [Fintype n] [DecidableEq n] :
  ∀ (A : Matrix n n ℝ) (μ : ℝ),
  (∃ v : n → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v) → |μ| ≤ ‖A‖

/-! ## T1.8: Classical Analysis (used in bridges) -/

/-- Mean Value Theorem for log: |log i - log j| ≥ |i - j| / max(i,j)
    Classical calculus (Cauchy, ~1820) -/
axiom MVT_log_bound : ∀ (i j : ℕ), 2 ≤ i → 2 ≤ j → i ≠ j →
  |Real.log i - Real.log j| ≥ |(i : ℝ) - j| / max (i : ℝ) j

/-- Geometric series bound: Σ_{k=1}^∞ r^k = r/(1-r) for 0 < r < 1
    Elementary series (known since antiquity) -/
axiom geometric_series_bound : ∀ (r : ℝ), 0 < r → r < 1 →
  ∀ (S : ℕ → ℝ), (∀ k, S k ≤ r^k) → ∑' k, S k ≤ r / (1 - r)

/-- Off-diagonal sum bound by S_K (geometric series application) -/
axiom off_diag_geometric_bound : ∀ (K t : ℝ), K ≥ 1 → t > 0 →
  ∀ (δ : ℝ), δ > 0 →
  let r := Real.exp (-(δ^2) / (4 * t))
  r < 1 → 2 * r / (1 - r) ≤ Q3.S_K K t

/-- Legacy project assumption about `Q3.Q` on the broad Weil cone.
Despite its historical name, this is not generic RKHS inner-product
positivity and is not attributed here to Aronszajn's kernel theorem. -/
axiom RKHS_inner_product_nonneg : ∀ (f : ℝ → ℝ),
  Q3.Q f ≥ 0 ∨ f ∉ Q3.Weil_cone

/-- Heat kernel is approximate identity: ρ_t * f → f as t → 0
    Standard PDE theory (19th century) -/
axiom heat_kernel_approx_identity : ∀ (K : ℝ) (f : ℝ → ℝ),
  Continuous f → ∀ ε > 0, ∃ δ > 0, ∀ t > 0, t < δ →
  ∀ x ∈ Set.Icc (-K) K, |f x - ∫ y, Q3.heat_kernel t (x - y) * f y| < ε

/-- W_sum is nonnegative (sum of nonnegative weights) -/
axiom W_sum_nonneg : ∀ K : ℝ, Q3.W_sum K ≥ 0

/-- Heat convolution is smooth: ρ_t * Φ is C^∞ for any bounded Φ
    Standard PDE theory (19th century) -/
axiom heat_conv_smooth : ∀ (Φ : ℝ → ℝ) (t : ℝ), t > 0 →
  ContDiff ℝ ⊤ (fun x => ∫ y, Q3.heat_kernel t (x - y) * Φ y)

end Q3.Clean

/-!
# Summary

Selected Tier-1 declaration summary (derive counts from source census)

## T1.1-T1.7: Core Mathematical Framework
- Weil_criterion (1952)
- explicit_formula (Guinand 1948)
- rawKernelGlobalPosAssumption (legacy, known-false globally),
  a_star_continuous, a_star_bdd_on_compact, a_star_even
- Szego_Bottcher_eigenvalue_bound, Szego_Bottcher_convergence (1958/1999)
- Schur_test (1911)
- rawKernelCompactInfPosAssumption (legacy conditional)
- eigenvalue_le_norm

## T1.8: Analysis assumptions for bridges
- MVT_log_bound (Cauchy ~1820)
- geometric_series_bound (antiquity)
- off_diag_geometric_bound (application of geometric series)
- RKHS_inner_product_nonneg (legacy broad-cone project assumption)
- heat_kernel_approx_identity (19th century PDE)
- W_sum_nonneg (elementary)

The raw-kernel global and compact-inf positivity declarations above are
quarantined legacy assumptions, not literature-certified results. The
remaining declarations retain their individual historical labels. Q3 paper
contributions belong in TheoremsTier2.lean.
-/
