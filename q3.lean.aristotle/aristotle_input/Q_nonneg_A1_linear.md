# Q_nonneg_A1: Linearity of Q over Finite Sums

## Goal
Prove that the Q functional distributes over finite sums with nonnegative coefficients.

## Lean Statement
```lean
import Mathlib
import Q3.Basic.Defs

open scoped BigOperators

lemma Q_finset_sum {α : Type*} (s : Finset α) (c : α → ℝ) (f : α → ℝ → ℝ) :
    Q3.Q (fun x => ∑ i in s, c i * f i x) =
      ∑ i in s, c i * Q3.Q (f i) := by
  sorry
```

## Definitions (from Q3/Basic/Defs.lean)
```lean
def arch_term (Φ : ℝ → ℝ) : ℝ := ∫ ξ, a_star ξ * Φ ξ
def prime_term (Φ : ℝ → ℝ) : ℝ := ∑' n, w_Q n * Φ (xi_n n)
def Q (Φ : ℝ → ℝ) : ℝ := arch_term Φ - prime_term Φ
```

## Proof Strategy
1. Unfold `Q` into `arch_term - prime_term`
2. For `arch_term`: use `integral_finset_sum` (linearity of integral)
3. For `prime_term`: use `tsum_finset_sum` (interchange sum/tsum)
4. Combine using `Finset.sum_sub_distrib`

## Available Mathlib Lemmas
- `MeasureTheory.integral_finset_sum` — ∫ (∑ᵢ fᵢ) = ∑ᵢ ∫ fᵢ
- `tsum_finset_sum` — ∑' n (∑ᵢ fᵢ n) = ∑ᵢ ∑' n fᵢ n (with summability)
- `Finset.sum_sub_distrib` — ∑ᵢ (aᵢ - bᵢ) = (∑ᵢ aᵢ) - (∑ᵢ bᵢ)

## Policy
- Use `suffices` for goal reduction
- Avoid `exact?` - use explicit lemma names
- Minimize `aesop` - prefer `simp`, `ring`, `congr`
- Factor out arch_term and prime_term linearity separately
