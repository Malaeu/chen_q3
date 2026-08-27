/-
Q3 Legacy A3 Raw-Kernel Bridge
==============================

This file exposes the legacy conditional A3 bridge:
  λ_min(T_M[a_star] - T_P) ≥ c_arch(K)/4

where:
- T_M[a_star] is the matrix constructed from the raw kernel `Q3.a_star`
- T_P is the prime sampling operator
- c_arch(K) is the raw-kernel compact infimum

The result is supplied by `Q3.A3_bridge_axiom`; this file does not prove its
analytic premise. The separate periodized symbol `_root_.P_A` is not the
object in the theorem statement, and no `P_A`-to-`c_arch` crosswalk is used.
-/

import Mathlib
import Q3.Basic.Defs
import Q3.Axioms

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Pointwise
open MeasureTheory

set_option maxHeartbeats 400000
set_option maxRecDepth 4000

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Q3.A3

/-! ## Definitions -/

/-- Total variation of a function on [0, 2π] -/
def totalVariation (a : ℝ → ℝ) : ℝ :=
  (eVariationOn a (Set.Icc 0 (2 * Real.pi))).toReal

/-- Modulus of continuity -/
def modulusOfContinuity (f : ℝ → ℝ) (δ : ℝ) : ℝ :=
  sSup {d : ℝ | ∃ x y : ℝ, |x - y| ≤ δ ∧ d = |f x - f y|}

-- c_arch and ToeplitzMatrix are defined in Q3 namespace in Axioms.lean

/-! ## Legacy raw-kernel compact-infimum assumption -/

/-- Explicit consumption of the quarantined legacy compact-infimum assumption. -/
lemma rawKernelCompactInfPos_ofLegacyAssumption
    (K : ℝ) (hK : K > 0) : Q3.c_arch K > 0 :=
  Q3.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption K hK

/-! ## Szegő-Böttcher Theory -/

/-- Szegő-Böttcher theorem: eigenvalues of Toeplitz matrix approach symbol values -/
theorem Szego_Bottcher (M : ℕ) (_hM : M ≥ 1) (P : ℝ → ℝ) (hP_cont : Continuous P)
    (hP_real : ∀ θ, P (-θ) = P θ) :
    ∀ ε > 0, ∃ N, ∀ m ≥ N,
      ∀ μ, (∃ v : Fin m → ℝ, v ≠ 0 ∧ (Q3.ToeplitzMatrix m P).mulVec v = μ • v) →
        ∃ θ ∈ Set.Icc 0 (2 * Real.pi), |μ - P θ| < ε :=
  Q3.Szego_Bottcher_convergence P hP_cont hP_real

/-! ## Main A3 Theorem -/

/-- **Legacy conditional A3 raw-kernel bridge**:

For the raw-kernel matrix in the displayed theorem statement and the prime
operator, the declaration `Q3.A3_bridge_axiom` supplies:

  λ_min(T_M[a_star] - T_P) ≥ c_arch(K)/4

This theorem is only a wrapper around `Q3.A3_bridge_axiom`. It neither derives
the bound from Szegő–Böttcher theory nor identifies `_root_.P_A` with
`Q3.a_star` or `Q3.c_arch`.
-/
theorem A3_bridge (K : ℝ) (hK : K ≥ 1) :
    ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
      ∀ (v : Fin M → ℝ), v ≠ 0 →
        (∑ i, ∑ j, v i * v j * (Q3.ToeplitzMatrix M (Q3.a_star) i j -
          Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
          Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t)))) /
        (∑ i, v i ^ 2) ≥ Q3.c_arch K / 4 :=
  Q3.A3_bridge_axiom K hK

/-- Corollary: The spectral gap ensures Q ≥ 0 on finite approximations -/
theorem A3_spectral_gap (K : ℝ) (hK : K ≥ 1) :
    ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
      ∀ (v : Fin M → ℝ),
        (∑ i, ∑ j, v i * v j * Q3.ToeplitzMatrix M (Q3.a_star) i j) -
        (∑ i, ∑ j, v i * v j *
          (Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
           Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t)))) ≥
        Q3.c_arch K / 4 * (∑ i, v i ^ 2) := by
  obtain ⟨M₀, t, ht, hM⟩ := A3_bridge K hK
  use M₀, t, ht
  intro M hM_ge v
  by_cases hv : v = 0
  · simp [hv]
  · have h_rayleigh := hM M hM_ge v hv
    have h_sq_pos : 0 < ∑ i, v i ^ 2 := by
      apply Finset.sum_pos'
      · exact fun i _ => sq_nonneg _
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        exact ⟨i, Finset.mem_univ i, pow_two_pos_of_ne_zero hi⟩
    -- Convert Rayleigh quotient to product form: a/b ≥ c and b > 0 implies a ≥ c*b
    have h_mul := (le_div_iff₀ h_sq_pos).mp h_rayleigh
    -- The goal follows by algebraic manipulation of sums
    simp only [← Finset.sum_sub_distrib, ← mul_sub] at h_mul ⊢
    convert h_mul using 2

end Q3.A3

end
