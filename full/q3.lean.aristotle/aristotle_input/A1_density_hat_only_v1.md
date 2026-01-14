# A1 Hat Interpolation Only (Fallback Request)

Goal: prove only `hat_interpolation_approx`. This is the smaller fallback if the full A1 density request is too large.

## Lean Context

```lean
import Mathlib

open scoped BigOperators Real Classical

noncomputable def FejerKernel (B : ℝ) (x : ℝ) : ℝ := max 0 (1 - |x| / B)
```

## Target Lemma

```lean
/-- Hat interpolation approximation: for continuous f, ||h - f||∞ ≤ ε
    using midpoint grid and FejerKernel hats. -/
lemma hat_interpolation_approx (K : ℝ) (hK : K > 0) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc (-K) K))
    (hf_supp : Function.support f ⊆ Set.Icc (-K) K)
    (ε : ℝ) (hε : ε > 0) :
    ∃ (n : ℕ) (τ : Fin n → ℝ) (δ : ℝ),
      n > 0 ∧ δ > 0 ∧
      (∀ i, τ i ∈ Set.Icc (-K) K) ∧
      (∀ i, |τ i| + δ ≤ K) ∧
      ∀ x ∈ Set.Icc (-K) K,
        |∑ i, f (τ i) * FejerKernel δ (x - τ i) - f x| < ε := by
  -- Use uniform continuity on compact [-K,K].
  -- Choose δ small and a midpoint grid τ_i = -K + (i+1/2)δ.
  -- Show only two hats are nonzero at each x; their weights sum to 1.
  -- Bound by modulus of continuity to get the ε-approximation.
  sorry
```

## Notes / Hints

- You may introduce helper lemmas for: partition-of-unity of hats, two-hat support,
  or bounding `∑ i FejerKernel δ (x - τ i)` on `[-K,K]`.
- Keep the proof Lean-accepted (no `sorry`, no `exact?`).
