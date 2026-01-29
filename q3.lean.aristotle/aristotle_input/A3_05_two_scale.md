# A3 Two-Scale Selection Lemma

## Goal
Prove that the archimedean floor is preserved under two-scale smoothing: both the symbol-side (t_sym) and RKHS-side (t_rkhs) smoothing maintain positive lower bounds.

## Definitions

```lean
-- BV function (bounded variation)
def IsBV (f : ℝ → ℝ) : Prop := BoundedVariationOn f Set.univ

-- Mollifier kernel (even, C¹, integrates to 1)
structure MollifierKernel (K : ℝ → ℝ) : Prop where
  continuous : Continuous K
  even : ∀ x, K (-x) = K x
  integral_one : ∫ x, K x = 1
  compactSupport : HasCompactSupport K

-- Smoothed symbol via convolution
noncomputable def smooth_symbol (a K : ℝ → ℝ) (t : ℝ) (θ : ℝ) : ℝ :=
  ∫ x, a x * K ((θ - x) / t) / t

-- Arc on torus
def Arc (Γ : Set ℝ) : Prop := ∃ θ₀ ℓ, ℓ > 0 ∧ Γ = Set.Icc (θ₀ - ℓ/2) (θ₀ + ℓ/2)

-- Symbol floor on arc
noncomputable def floor_on_arc (a : ℝ → ℝ) (Γ : Set ℝ) : ℝ := ⨅ θ ∈ Γ, a θ
```

## Main Lemma to Prove

```lean
/-- Two-scale selection: small t_sym preserves half of the floor -/
lemma two_scale_selection (a : ℝ → ℝ) (K : ℝ → ℝ) (Γ : Set ℝ)
    (ha : IsBV a) (hK : MollifierKernel K) (hΓ : Arc Γ)
    (h_floor : floor_on_arc a Γ > 0) :
    ∃ t_sym > 0, floor_on_arc (smooth_symbol a K t_sym) Γ ≥ floor_on_arc a Γ / 2 := by
  sorry

/-- Moreover, for t_rkhs ≥ t_sym, the RKHS kernel maintains uniform floor -/
lemma two_scale_rkhs_floor (a K : ℝ → ℝ) (Γ : Set ℝ) (t_sym t_rkhs : ℝ)
    (ha : IsBV a) (hK : MollifierKernel K) (hΓ : Arc Γ)
    (h_sym : floor_on_arc (smooth_symbol a K t_sym) Γ > 0)
    (h_rkhs : t_rkhs ≥ t_sym) :
    ∃ c_star > 0, ∀ θ ∈ Γ, smooth_symbol a K t_rkhs θ ≥ c_star := by
  sorry
```

## Proof Sketch

### For two_scale_selection:

1. **Uniform convergence**: As t → 0, a * K_t → a uniformly
   - Standard mollifier approximation theory
   - Use: smooth_symbol a K t → a uniformly as t → 0⁺

2. **Preserve positivity**: Since a * K_t → a uniformly and min_Γ a > 0,
   for small enough t_sym: min_Γ (a * K_t_sym) ≥ (1/2) min_Γ a

3. **Explicit t_sym choice**: Take t_sym small enough that
   ‖a * K_t - a‖_∞ < (1/2) min_Γ a

### For two_scale_rkhs_floor:

1. **RKHS floor from trace-cap**: The Gram estimates in trace-cap bound give
   explicit positivity for the RKHS kernel at scale t_rkhs

2. **Comparison**: Since t_rkhs ≥ t_sym, the RKHS smoothing is at least as strong,
   keeping the same positivity budget

3. **Independence of scales**: The key insight is that t_sym and t_rkhs operate
   on different parts of the analysis (symbol vs Gram matrix) and can be chosen
   independently

## Notes

- The two scales are architecturally independent:
  - t_sym: enters Fejér×heat convolution for P_A
  - t_rkhs: enters RKHS Gram matrix for ‖T_P‖

- Use `MeasureTheory.tendsto_integral_of_dominated_convergence` for uniform convergence

- The BV condition ensures TV(a) < ∞, which controls Lipschitz constant after smoothing
