# Node Spacing Lemma — Full Proof

## Setup

Let K ≥ 1 be a compact parameter.

### Definitions

```lean
-- Spectral coordinate: ξ_n = log(n)/(2π)
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

-- Node set: all n with |ξ_n| ≤ K and n ≥ 2
def Nodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

-- Maximum node index
def N_K (K : ℝ) : ℕ := Nat.floor (Real.exp (2 * Real.pi * K))

-- Minimum node spacing
def delta_K (K : ℝ) : ℝ := 1 / (2 * Real.pi * (N_K K + 1))
```

## Theorem Statement

Adjacent spectral nodes are separated by at least δ_K:

```lean
theorem node_spacing (K : ℝ) (hK : K ≥ 1) :
    ∀ (n₁ n₂ : ℕ), n₁ ∈ Nodes K → n₂ ∈ Nodes K → n₁ < n₂ →
      xi_n n₂ - xi_n n₁ ≥ delta_K K
```

## Proof

### Step 1: Express spacing in terms of ratio

For n₁ < n₂:
```
ξ_{n₂} - ξ_{n₁} = log(n₂)/(2π) - log(n₁)/(2π)
                = (log(n₂) - log(n₁))/(2π)
                = log(n₂/n₁)/(2π)
```

### Step 2: Bound the ratio from below

Since n₁ < n₂ are both natural numbers, we have n₂ ≥ n₁ + 1.

Therefore:
```
n₂/n₁ ≥ (n₁ + 1)/n₁ = 1 + 1/n₁
```

Since n₁ ∈ Nodes K, we have n₁ ≤ N_K = ⌊exp(2πK)⌋.

Therefore:
```
1/n₁ ≥ 1/N_K
n₂/n₁ ≥ 1 + 1/N_K
```

### Step 3: Apply log inequality

For x > 0, we have: log(1 + x) ≥ x/(1 + x)

With x = 1/N_K > 0:
```
log(1 + 1/N_K) ≥ (1/N_K)/(1 + 1/N_K) = 1/(N_K + 1)
```

### Step 4: Combine bounds

```
ξ_{n₂} - ξ_{n₁} = log(n₂/n₁)/(2π)
                ≥ log(1 + 1/N_K)/(2π)
                ≥ 1/((N_K + 1) · 2π)
                = δ_K
```

∎

## Expected Lean Proof

```lean
theorem node_spacing (K : ℝ) (hK : K ≥ 1) :
    ∀ (n₁ n₂ : ℕ), n₁ ∈ Nodes K → n₂ ∈ Nodes K → n₁ < n₂ →
      xi_n n₂ - xi_n n₁ ≥ delta_K K := by
  intro n₁ n₂ hn₁ hn₂ hlt
  unfold xi_n delta_K N_K
  -- ξ_{n₂} - ξ_{n₁} = log(n₂/n₁)/(2π)
  have h1 : Real.log n₂ / (2 * Real.pi) - Real.log n₁ / (2 * Real.pi) =
            Real.log (n₂ / n₁) / (2 * Real.pi) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    ring
  rw [h1]
  -- n₂ ≥ n₁ + 1 since n₁ < n₂ and both are ℕ
  have h2 : (n₂ : ℝ) ≥ n₁ + 1 := by
    have : n₂ ≥ n₁ + 1 := Nat.succ_le_of_lt hlt
    exact_mod_cast this
  -- n₂/n₁ ≥ 1 + 1/n₁
  have h3 : (n₂ : ℝ) / n₁ ≥ 1 + 1 / n₁ := by
    have hn₁_pos : (0 : ℝ) < n₁ := by
      have := hn₁.2  -- n₁ ≥ 2
      exact_mod_cast (by omega : (2 : ℕ) > 0).trans_le this
    field_simp
    linarith
  -- n₁ ≤ N_K
  have h4 : (n₁ : ℝ) ≤ Nat.floor (Real.exp (2 * Real.pi * K)) := by
    have := hn₁.1  -- |ξ_{n₁}| ≤ K
    -- This means log(n₁)/(2π) ≤ K, so n₁ ≤ exp(2πK)
    sorry
  -- log(1 + 1/N_K) ≥ 1/(N_K + 1)
  have h5 : Real.log (1 + 1 / (Nat.floor (Real.exp (2 * Real.pi * K)) : ℝ)) ≥
            1 / ((Nat.floor (Real.exp (2 * Real.pi * K)) : ℝ) + 1) := by
    apply Real.log_one_plus_inv_ge_inv_add_one
    exact_mod_cast Nat.floor_pos.mpr (Real.exp_pos _).le
  -- Combine everything
  calc Real.log (n₂ / n₁) / (2 * Real.pi)
      ≥ Real.log (1 + 1 / n₁) / (2 * Real.pi) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply Real.log_le_log (by positivity)
          exact h3
    _ ≥ Real.log (1 + 1 / (Nat.floor (Real.exp (2 * Real.pi * K)) : ℝ)) / (2 * Real.pi) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply Real.log_le_log (by positivity)
          apply add_le_add_left
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact h4
    _ ≥ 1 / ((Nat.floor (Real.exp (2 * Real.pi * K)) : ℝ) + 1) / (2 * Real.pi) := by
          apply div_le_div_of_nonneg_right h5 (by positivity)
    _ = 1 / (2 * Real.pi * ((Nat.floor (Real.exp (2 * Real.pi * K)) : ℝ) + 1)) := by
          field_simp; ring
```

## Key Lemmas Needed

1. `Real.log_div` — log(a/b) = log(a) - log(b)
2. `Real.log_le_log` — monotonicity of log
3. `Real.log_one_plus_inv_ge_inv_add_one` — log(1+1/x) ≥ 1/(x+1) for x > 0
4. `Nat.succ_le_of_lt` — n₁ < n₂ → n₁ + 1 ≤ n₂
5. `Nat.floor_pos` — floor of positive is positive
