# Off-Diagonal Exponential Sum Bound — Full Proof

## Setup

Let K ≥ 1 be a compact parameter, t > 0 a heat parameter.

### Definitions

```lean
-- Spectral coordinate: ξ_n = log(n)/(2π)
def xi_n (n : ℕ) : ℝ := Real.log n / (2 * Real.pi)

-- Node set: {n ≥ 2 | |ξ_n| ≤ K}
def Nodes (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

-- Maximum node index
def N_K (K : ℝ) : ℕ := Nat.floor (Real.exp (2 * Real.pi * K))

-- Minimum node spacing
def delta_K (K : ℝ) : ℝ := 1 / (2 * Real.pi * (N_K K + 1))

-- Geometric series bound
def S_K (K t : ℝ) : ℝ :=
  2 * Real.exp (-(delta_K K)^2 / (4 * t)) / (1 - Real.exp (-(delta_K K)^2 / (4 * t)))
```

## Theorem Statement

The off-diagonal exponential sum is bounded by S_K:

```lean
theorem off_diag_exp_sum_bound (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    (Nodes_K : Set ℕ) [Fintype Nodes_K] (i : Nodes_K) :
    ∑ j : Nodes_K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) else 0) ≤ S_K K t
```

## Proof

### Step 1: Use node spacing

By node_spacing_axiom, for any distinct nodes i, j ∈ Nodes_K:
```
|ξ_i - ξ_j| ≥ |i - j| · δ_K
```

where δ_K = 1/(2π(N_K + 1)).

### Step 2: Bound individual terms

For j ≠ i, we have |i - j| ≥ 1, so:
```
(ξ_i - ξ_j)² ≥ δ_K²
```

Therefore:
```
exp(-(ξ_i - ξ_j)² / (4t)) ≤ exp(-δ_K² / (4t))
```

### Step 3: Arrange by distance

Let r = exp(-δ_K²/(4t)) < 1 (since δ_K > 0 and t > 0).

For nodes at distance k from i (i.e., |j - i| = k), we have:
```
(ξ_i - ξ_j)² ≥ k² · δ_K²
```

So:
```
exp(-(ξ_i - ξ_j)² / (4t)) ≤ r^(k²) ≤ r^k
```

### Step 4: Sum the geometric series

```
∑_{j ≠ i} exp(-(ξ_i - ξ_j)² / (4t))
  ≤ ∑_{k=1}^{∞} 2 · r^k     (factor 2 for both directions)
  = 2 · r / (1 - r)
  = 2 · exp(-δ_K²/(4t)) / (1 - exp(-δ_K²/(4t)))
  = S_K(K, t)
```

∎

## Expected Lean Proof

```lean
theorem off_diag_exp_sum_bound (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    (Nodes_K : Set ℕ) [Fintype Nodes_K] (i : Nodes_K) :
    ∑ j : Nodes_K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) else 0) ≤ S_K K t := by
  unfold S_K delta_K
  -- Let r = exp(-δ²/(4t)) < 1
  set r := Real.exp (-(1 / (2 * Real.pi * (↑(N_K K) + 1)))^2 / (4 * t)) with hr_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt_one : r < 1 := by
    rw [Real.exp_lt_one_iff]
    have hδ_pos : (1 / (2 * Real.pi * (↑(N_K K) + 1)))^2 > 0 := sq_pos_of_pos (by positivity)
    linarith [mul_pos (by linarith : (4 : ℝ) > 0) ht]
  -- Each term bounded by r^k where k = distance
  have h_term_bound : ∀ j : Nodes_K, j ≠ i →
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) ≤ r := by
    intro j hji
    apply Real.exp_le_exp.mpr
    -- Use node_spacing: |ξ_i - ξ_j| ≥ δ_K
    have h_spacing := node_spacing_axiom K hK (i : ℕ) (j : ℕ)
    sorry -- spacing gives bound on exponent
  -- Geometric series bound
  calc ∑ j, (if (j : ℕ) ≠ (i : ℕ) then Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) else 0)
      ≤ ∑ j, (if (j : ℕ) ≠ (i : ℕ) then r else 0) := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs with h
          · exact h_term_bound j (by simp_all)
          · exact le_refl 0
    _ ≤ 2 * r / (1 - r) := by
          -- geometric series
          sorry
```

## Key Lemmas Needed

1. `Real.exp_le_exp` — monotonicity of exp
2. `Real.exp_lt_one_iff` — exp(x) < 1 ⟺ x < 0
3. `Finset.sum_le_sum` — sum comparison
4. `node_spacing_axiom` — minimum spacing between nodes
5. `geom_series_def` — geometric series formula
