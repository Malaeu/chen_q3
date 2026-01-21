# Q Lipschitz on W_K — Full Proof

## Setup

Let K > 0 be a compact parameter. We work in ℝ.

### Definitions

```lean
-- Spectral coordinate
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

-- Prime weight
def w_Q (n : ℕ) : ℝ := 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n

-- Archimedean kernel (positive, continuous)
def a_star (ξ : ℝ) : ℝ  -- Assume: a_star continuous, a_star ξ > 0 for all ξ

-- Archimedean term
def arch_term (Φ : ℝ → ℝ) : ℝ := ∫ ξ, a_star ξ * Φ ξ

-- Prime term (sum over n ≥ 2)
def prime_term (Φ : ℝ → ℝ) : ℝ := ∑' n, w_Q n * Φ (xi_n n)

-- Q functional
def Q (Φ : ℝ → ℝ) : ℝ := arch_term Φ - prime_term Φ

-- W_K: continuous, even, nonnegative functions supported in [-K, K]
def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | ContinuousOn Φ (Set.Icc (-K) K) ∧
       Function.support Φ ⊆ Set.Icc (-K) K ∧
       (∀ x, Φ (-x) = Φ x) ∧
       (∀ x, 0 ≤ Φ x)}

-- Active nodes: those with ξ_n ∈ [-K, K]
def ActiveNodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

-- Weight sum over active nodes
def W_sum (K : ℝ) : ℝ := ∑' n, if n ∈ ActiveNodes K then w_Q n else 0
```

## Theorem Statement

For any K > 0, Q is Lipschitz on W_K:

```lean
theorem Q_Lipschitz_on_W_K (K : ℝ) (hK : K > 0) :
    ∃ L > 0, ∀ Φ₁ ∈ W_K K, ∀ Φ₂ ∈ W_K K,
      |Q Φ₁ - Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K}
```

## Proof

### Step 1: Decompose Q difference

Since Q = arch_term - prime_term:

```
Q(Φ₁) - Q(Φ₂) = [arch_term(Φ₁) - arch_term(Φ₂)] - [prime_term(Φ₁) - prime_term(Φ₂)]
```

By triangle inequality:
```
|Q(Φ₁) - Q(Φ₂)| ≤ |arch_term(Φ₁) - arch_term(Φ₂)| + |prime_term(Φ₁) - prime_term(Φ₂)|
```

### Step 2: Bound arch_term difference

```
arch_term(Φ₁) - arch_term(Φ₂) = ∫ a*(ξ) · (Φ₁(ξ) - Φ₂(ξ)) dξ
```

Since Φ₁, Φ₂ are supported in [-K, K]:
```
|arch_term(Φ₁) - arch_term(Φ₂)| ≤ ∫_{-K}^{K} |a*(ξ)| · |Φ₁(ξ) - Φ₂(ξ)| dξ
                                 ≤ ∫_{-K}^{K} a*(ξ) dξ · ‖Φ₁ - Φ₂‖_∞
```

Let M_a = max_{|ξ|≤K} a*(ξ). This exists and is finite by continuity of a* on compact [-K,K].

```
|arch_term(Φ₁) - arch_term(Φ₂)| ≤ 2K · M_a · ‖Φ₁ - Φ₂‖_∞
```

### Step 3: Bound prime_term difference

```
prime_term(Φ₁) - prime_term(Φ₂) = Σ_{n≥2} w_Q(n) · (Φ₁(ξ_n) - Φ₂(ξ_n))
```

**Key observation:** Only finitely many nodes ξ_n lie in [-K, K].

Since ξ_n = log(n)/(2π), we have |ξ_n| ≤ K ⟺ n ≤ exp(2πK).

For n ∉ ActiveNodes(K): both Φ₁(ξ_n) = 0 and Φ₂(ξ_n) = 0 (outside support).

Therefore:
```
|prime_term(Φ₁) - prime_term(Φ₂)| ≤ Σ_{n ∈ ActiveNodes(K)} w_Q(n) · |Φ₁(ξ_n) - Φ₂(ξ_n)|
                                   ≤ Σ_{n ∈ ActiveNodes(K)} w_Q(n) · ‖Φ₁ - Φ₂‖_∞
                                   = W_sum(K) · ‖Φ₁ - Φ₂‖_∞
```

### Step 4: Combine bounds

Define Lipschitz constant:
```
L_Q(K) := 2K · M_a + W_sum(K)
```

Then:
```
|Q(Φ₁) - Q(Φ₂)| ≤ |arch_diff| + |prime_diff|
                ≤ (2K · M_a + W_sum(K)) · ‖Φ₁ - Φ₂‖_∞
                = L_Q(K) · ‖Φ₁ - Φ₂‖_∞
```

### Step 5: Show L_Q(K) > 0

- K > 0 by assumption
- M_a = max a*(ξ) > 0 since a*(ξ) > 0 for all ξ (axiom a_star_pos)
- W_sum(K) ≥ 0 (sum of nonnegative terms)

Therefore L_Q(K) = 2K · M_a + W_sum(K) > 0. ∎

## Expected Lean Proof Structure

```lean
theorem Q_Lipschitz_on_W_K (K : ℝ) (hK : K > 0) :
    ∃ L > 0, ∀ Φ₁ ∈ W_K K, ∀ Φ₂ ∈ W_K K,
      |Q Φ₁ - Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
  -- Define L_Q(K) = 2K · M_a + W_sum(K)
  let M_a := sSup {a_star ξ | ξ ∈ Set.Icc (-K) K}
  let L := 2 * K * M_a + W_sum K
  use L
  constructor
  · -- Show L > 0
    have hM_pos : M_a > 0 := by
      -- a_star is continuous, positive, so sup on compact is positive
      sorry
    have hW_nonneg : W_sum K ≥ 0 := by
      -- W_sum is sum of nonnegative terms
      sorry
    linarith
  · intro Φ₁ hΦ₁ Φ₂ hΦ₂
    -- Triangle inequality for Q = arch - prime
    have h_arch : |arch_term Φ₁ - arch_term Φ₂| ≤ 2 * K * M_a * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
      sorry
    have h_prime : |prime_term Φ₁ - prime_term Φ₂| ≤ W_sum K * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by
      sorry
    calc |Q Φ₁ - Q Φ₂| = |arch_term Φ₁ - arch_term Φ₂ - (prime_term Φ₁ - prime_term Φ₂)| := by
           unfold Q; ring_nf
      _ ≤ |arch_term Φ₁ - arch_term Φ₂| + |prime_term Φ₁ - prime_term Φ₂| := abs_sub_abs_le_abs_sub _ _
      _ ≤ (2 * K * M_a + W_sum K) * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} := by linarith
```

## Key Lemmas Needed from Mathlib

1. `IsCompact.sSup_lt_iff` — supremum on compact set
2. `ContinuousOn.image_eq_iUnion_inter_Ioo` — continuous image properties
3. `tsum_le_tsum` — sum comparison
4. `abs_sub_abs_le_abs_sub` — triangle inequality variant
5. `MeasureTheory.integral_mono` — integral bounds
