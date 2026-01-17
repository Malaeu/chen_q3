# Q_finite = Q when K ≥ B

## Goal

Prove that the finite Q equals the full Q functional when K ≥ B.

```lean
lemma Q_finite_eq_Q_large_K (K B t : ℝ) (hK : K ≥ B) (hB : B > 0) (ht : t > 0)
    [Fintype (Q3.Nodes K)] :
    Q_finite K B t = Q3.Q (Q3.fejer_heat_window B t)
```

## Key Definitions

```lean
-- Q_finite sums only over nodes in [-K, K]
def Q_finite (K B t : ℝ) [Fintype (Q3.Nodes K)] : ℝ :=
  Q3.arch_term (Q3.fejer_heat_window B t) - prime_term_finite K B t

-- prime_term_finite sums over nodes in [-K, K]
def prime_term_finite (K B t : ℝ) [Fintype (Q3.Nodes K)] : ℝ :=
  ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)

-- Full Q sums over all n ≥ 2
Q3.Q (Φ : ℝ → ℝ) : ℝ := Q3.arch_term Φ - Q3.prime_term Φ

-- Full prime_term sums over all n ≥ 2
Q3.prime_term (Φ : ℝ → ℝ) : ℝ := ∑' n : {k : ℕ // 2 ≤ k}, Q3.w_Q n * Φ (Q3.xi_n n)

-- Nodes K = { n : ℕ // 2 ≤ n ∧ Q3.xi_n n ∈ Set.Icc (-K) K }
def Nodes (K : ℝ) : Type := { n : ℕ // 2 ≤ n ∧ Q3.xi_n n ∈ Set.Icc (-K) K }

-- fejer_heat_window B t ξ = max(0, 1 - |ξ|/B) * exp(-4π²t·ξ²)
-- It has support in [-B, B]
```

## Key Insight

The window `fejer_heat_window B t` has support in `[-B, B]`.
For nodes n with `|xi_n n| > K ≥ B`, we have `fejer_heat_window B t (xi_n n) = 0`.

This means the full sum `Q3.prime_term Φ` equals the finite sum `prime_term_finite K B t`:
- Terms with `|xi_n| ≤ K` are captured by nodes in `Nodes K`
- Terms with `|xi_n| > K ≥ B` contribute 0

## Proof Strategy

1. Show: `Q3.prime_term Φ = prime_term_finite K B t` when K ≥ B

2. This follows because:
   - For n ∈ Nodes K: term contributes to both sums
   - For n ∉ Nodes K: either n < 2 (no contribution) or |xi_n| > K ≥ B, so Φ(xi_n) = 0

3. Unfold Q_finite and Q, show they have the same arch_term and prime_term.

## Available Lemmas

```lean
-- fejer_heat_window vanishes outside [-B, B]
lemma fejer_heat_window_support (B t ξ : ℝ) (hB : B > 0) (hξ : |ξ| > B) :
    Q3.fejer_heat_window B t ξ = 0

-- This should be easy to prove from:
-- fejer_heat_window = max(0, 1 - |ξ|/B) * exp(...)
-- When |ξ| > B: 1 - |ξ|/B < 0, so max(0, ...) = 0
```

## Key Calculation

```
Q3.prime_term Φ = ∑' n : {k // 2 ≤ k}, w_Q(n) * Φ(xi_n)

Split into two parts:
  = ∑' n : {k // 2 ≤ k ∧ |xi_k| ≤ K}, w_Q(n) * Φ(xi_n)   -- captured by Nodes K
  + ∑' n : {k // 2 ≤ k ∧ |xi_k| > K}, w_Q(n) * Φ(xi_n)   -- tail

For the tail:
  |xi_n| > K ≥ B implies Φ(xi_n) = 0, so tail = 0

Therefore:
  Q3.prime_term Φ = ∑ n : Nodes K, w_Q(n) * Φ(xi_n) = prime_term_finite K B t
```

## Mathlib Lemmas to Use

```lean
-- For splitting sums:
tsum_subtype_add_tsum_subtype_compl -- split tsum into two parts

-- For showing terms are zero:
tsum_eq_zero_of_not_summable
tsum_eq_single -- if only one term is nonzero

-- For finite sums equaling tsums:
tsum_eq_sum -- when terms vanish outside finite set
Finset.sum_congr -- for showing sums are equal
```

## Proof Sketch

```lean
lemma Q_finite_eq_Q_large_K (K B t : ℝ) (hK : K ≥ B) (hB : B > 0) (ht : t > 0)
    [Fintype (Q3.Nodes K)] :
    Q_finite K B t = Q3.Q (Q3.fejer_heat_window B t) := by
  -- Both have the same arch_term
  unfold Q_finite Q3.Q
  congr 1
  -- Need: prime_term_finite K B t = Q3.prime_term Φ
  unfold prime_term_finite Q3.prime_term
  -- The infinite sum equals the finite sum because:
  -- For n with |xi_n| > K ≥ B: Φ(xi_n) = 0
  symm
  apply tsum_eq_sum
  intro n hn
  -- n is in complement of Nodes K, so either n < 2 (no such n in sum) or |xi_n| > K
  -- Since |xi_n| > K ≥ B, Φ(xi_n) = 0
  have hxi : |Q3.xi_n n| > K := ...  -- from n ∉ Nodes K
  have hxi_B : |Q3.xi_n n| > B := lt_of_lt_of_le (lt_of_not_le ...) hK
  rw [fejer_heat_window_support B t _ hB hxi_B, mul_zero]
```

## xi_n Properties

```lean
-- xi_n n = log(n) / (2π)
-- xi_n is monotone increasing for n ≥ 1
-- So nodes with small xi_n have small n, nodes with large xi_n have large n
```

## Warning: Type Coercions

The sum types are tricky:
- `Q3.Nodes K` is `{n : ℕ // 2 ≤ n ∧ xi_n n ∈ Icc (-K) K}`
- `{k : ℕ // 2 ≤ k}` is just naturals ≥ 2

To go between them, need to show that for n ∉ Nodes K with 2 ≤ n:
- Either xi_n n < -K (impossible since xi_n n = log(n)/(2π) ≥ 0 for n ≥ 1)
- Or xi_n n > K ≥ B, hence Φ(xi_n n) = 0

## Tactic Preferences

AVOID: `exact?`, heavy `aesop`, long `have` chains
PREFER: `simp`, `nlinarith`, `positivity`, `gcongr`, `ext`
