# Rayleigh periodization: integral_P_A_eq_arch_term

## Goal
Provide a Lean proof for the lemma below (no `sorry`, no `exact?`).
This is the single bottleneck lemma in `Q3/Proofs/Rayleigh_Q_identification.lean`.

```lean
import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import A3_FLOOR_v22_stage4_floor

open scoped BigOperators Real Classical
open MeasureTheory

noncomputable section

namespace Q3.Proofs.RayleighQId

-- g and P_A are defined in A3_FLOOR_v22_stage4_floor.lean
-- w is defined in A3_FLOOR_v20_bounds_core.lean
-- Q3.arch_term and Q3.fejer_heat_window are in Q3.Basic.Defs

/-- Periodization theorem: integral of P_A over one period equals arch_term. -/
theorem integral_P_A_eq_arch_term (B t : ℝ) (hB : 0 < B) :
    ∫ θ in (-1/2 : ℝ)..(1/2), P_A B t θ =
      Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) := by
  -- fill proof

end Q3.Proofs.RayleighQId
```

## Available lemmas (already in the file; you may use them directly)

```lean
-- continuous + compact support
lemma continuous_g (B t : ℝ) : Continuous (fun ξ => g B t ξ)
lemma g_support (B t ξ : ℝ) (hB : 0 < B) (h : B ≤ |ξ|) : g B t ξ = 0

-- periodized sum is finite on [-1/2,1/2]
lemma g_shift_zero_of_large_m (B t θ : ℝ) (m : ℤ) (hB : 0 < B)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (⌈B⌉ : ℤ) + 1 < |m|) : g B t (θ + m) = 0

lemma P_A_tsum_eq_finite_sum (B t θ : ℝ) (hB : 0 < B)
    (hθ : θ ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), g B t (θ + m) =
    ∑ m ∈ Finset.Icc (-(⌈B⌉ + 1)) (⌈B⌉ + 1), g B t (θ + m)

-- arch term identity
lemma arch_term_eq_two_pi_integral_g (B t : ℝ) :
    Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) =
      2 * Real.pi * ∫ ξ, Q3.a ξ * w B t ξ
```

## Proof strategy (preferred)
1) On `[-1/2,1/2]`, rewrite the periodization sum to a finite sum using
   `P_A_tsum_eq_finite_sum` and `intervalIntegral.integral_congr`.
2) Use `intervalIntegral.integral_finset_sum` to swap integral and finite sum.
3) For each `m`, use `intervalIntegral.integral_comp_add_right` to change variables
   and rewrite the sum as a sum over shifted intervals.
4) Use the standard lemma `MeasureTheory.Integrable.hasSum_intervalIntegral`
   together with `tsum_eq_sum` and `g_shift_zero_of_large_m` to show the finite sum
   equals `∫ g`.
5) Finish by rewriting `P_A` and using `arch_term_eq_two_pi_integral_g`.

## Tactic policy
- Use explicit lemmas, avoid `exact?` and heavy `aesop`.
- Prefer `suffices` for goal reduction.
- If a `ring` step fails, use `ring_nf`.
