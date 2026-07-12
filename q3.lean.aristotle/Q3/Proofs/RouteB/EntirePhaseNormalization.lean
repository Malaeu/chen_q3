import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- A finite linear combination of candidate entire summands. -/
def finiteEntireCombination {ι : Type*}
    (S : Finset ι) (a : ι → ℂ) (f : ι → ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ S, a k * f k z

/-- Finite linear combinations preserve entirety.  This is the generic Lean
core used by the fixed-window transform once its exact summands are pinned. -/
theorem differentiable_finiteEntireCombination {ι : Type*}
    (S : Finset ι) (a : ι → ℂ) (f : ι → ℂ → ℂ)
    (hf : ∀ k ∈ S, Differentiable ℂ (f k)) :
    Differentiable ℂ (finiteEntireCombination S a f) := by
  unfold finiteEntireCombination
  apply Differentiable.fun_sum
  intro k hk
  have hkdiff : Differentiable ℂ (f k) := hf k hk
  fun_prop

/-- Reflection, an exponential phase, and a constant normalization applied to
an entire function. -/
def phaseScaledReflection
    (phase scale : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  scale * Complex.exp (phase * z) * f (-z)

/-- The exact closure operation used in source-transform/determinant
crosswalks preserves entirety. -/
theorem differentiable_phaseScaledReflection
    (phase scale : ℂ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (phaseScaledReflection phase scale f) := by
  unfold phaseScaledReflection
  fun_prop

/-- A nonzero exponential phase and nonzero scalar introduce no new zeros;
reflection only moves the argument from `z` to `-z`. -/
theorem phaseScaledReflection_eq_zero_iff
    (phase scale z : ℂ) (f : ℂ → ℂ) (hscale : scale ≠ 0) :
    phaseScaledReflection phase scale f z = 0 ↔ f (-z) = 0 := by
  unfold phaseScaledReflection
  simp [hscale]

#print axioms differentiable_finiteEntireCombination
#print axioms differentiable_phaseScaledReflection
#print axioms phaseScaledReflection_eq_zero_iff

end Q3.RouteB
