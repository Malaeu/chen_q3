# Q_nonneg_A2: Nonnegativity of Prime Sum

## Goal
Prove that the finite prime sum over nodes is nonnegative for fejer_heat_window.

## Lean Statement
```lean
import Mathlib
import Q3.Basic.Defs

open scoped BigOperators

variable (K B t : ℝ) [Fintype (Q3.Nodes K)]

lemma prime_sum_nonneg (hB : B > 0) (ht : t > 0) :
    0 ≤ ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  sorry
```

## Definitions
```lean
def w_Q (n : ℕ) : ℝ := 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

def fejer_heat_window (B t : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t * ξ^2)

lemma w_Q_nonneg (n : ℕ) : 0 ≤ w_Q n  -- already proven

lemma fejer_heat_window_nonneg (B t ξ : ℝ) : 0 ≤ fejer_heat_window B t ξ  -- already proven
```

## Proof Strategy
1. Apply `Finset.sum_nonneg`
2. For each term: show `w_Q n * fejer_heat_window B t ξ ≥ 0`
3. Use `mul_nonneg` with `w_Q_nonneg` and `fejer_heat_window_nonneg`

## Available Lemmas
- `Finset.sum_nonneg` — if all terms ≥ 0, then sum ≥ 0
- `mul_nonneg` — if a ≥ 0 and b ≥ 0, then a * b ≥ 0
- `Q3.w_Q_nonneg` — w_Q n ≥ 0
- `Q3.fejer_heat_window_nonneg` — fejer_heat_window B t ξ ≥ 0

## Policy
- Use `suffices` for goal reduction
- Avoid `exact?`
- Prefer `positivity` tactic where applicable
- This is a short proof (< 10 lines expected)
