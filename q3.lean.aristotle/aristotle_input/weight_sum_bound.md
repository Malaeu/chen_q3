# Weight Sum Bound for RKHS Cap

## Goal

Prove that the sum of prime operator weights is bounded by 1/25.

This closes the `h_weight_sum` hypothesis needed by `rkhs_cap_rayleigh_tcap`.

---

## Mathematical Background

The prime operator compression has coefficients:
```
coeff(n) = 2 * Λ(n) / √n * exp(-4π² * t * (log n)²)
```

Where:
- Λ(n) = von Mangoldt function (log p if n = p^k, else 0)
- Λ(n) ≤ log n for all n
- t = t_rkhs_cap ≥ 1 (we use t = 40 for safety margin)

**Key insight:** For n ≥ 3 and t ≥ 1:
```
exp(-4π² * (log n)²) ≤ n^{-10}
```

Because 4π² ≈ 39.5 > 10, so 4π²(log n)² ≥ 10 * log n when log n ≥ 1.

This makes the sum exponentially small:
```
∑_{n≥2} (log n)/√n * n^{-10} = ∑_{n≥2} (log n)/n^{10.5} < 0.0003
```

---

## Definitions

```lean
import Mathlib

open scoped BigOperators
open Finset Real Nat

set_option maxHeartbeats 0

noncomputable section

-- Upper bound for weight sum
def rho_one : ℝ := 1 / 25

-- Heat parameter (t_rkhs_cap = 40)
def t_rkhs_cap : ℝ := 40

-- 4π² constant
def four_pi_sq : ℝ := 4 * Real.pi ^ 2

-- Weight function: 2 * Λ(n) / √n * exp(-4π² * t * (log n)²)
-- For our bound, we use Λ(n) ≤ log n
def weight_upper_bound (t : ℝ) (n : ℕ) : ℝ :=
  if n < 2 then 0
  else 2 * Real.log n / Real.sqrt n * Real.exp (-four_pi_sq * t * (Real.log n)^2)
```

---

## Key Lemmas to Prove

### Lemma 1: Exponential decay bound

For n ≥ 3 and any t ≥ 1:
```lean
lemma exp_decay_bound {n : ℕ} (hn : 3 ≤ n) (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-four_pi_sq * t * (Real.log n)^2) ≤ (n : ℝ)^(-10 : ℝ) := by
  -- Key: 4π² ≈ 39.5 > 10
  -- For n ≥ 3: log n ≥ 1
  -- So: 4π² * t * (log n)² ≥ 4π² * (log n) ≥ 10 * log n
  -- Thus: exp(-4π² * t * (log n)²) ≤ exp(-10 * log n) = n^{-10}
  sorry
```

### Lemma 2: Individual weight bound for n ≥ 3

```lean
lemma weight_bound_large_n {n : ℕ} (hn : 3 ≤ n) (t : ℝ) (ht : 1 ≤ t) :
    weight_upper_bound t n ≤ 2 * Real.log n / (n : ℝ)^(10.5 : ℝ) := by
  -- weight ≤ 2 * log n / √n * n^{-10} = 2 * log n / n^{10.5}
  sorry
```

### Lemma 3: Tail sum convergence

```lean
lemma tail_sum_bound :
    ∑' n : {k : ℕ // 3 ≤ k}, (2 * Real.log n / (n : ℝ)^(10.5 : ℝ)) < 0.001 := by
  -- This sum converges rapidly; log n / n^{10.5} → 0 very fast
  -- Σ_{n≥3} log n / n^{10.5} < Σ_{n≥3} 1/n^{9.5} < 1/(8.5 * 2^{8.5}) < 0.0005
  sorry
```

### Lemma 4: First terms explicit bound (n = 2)

```lean
lemma weight_n2_bound (t : ℝ) (ht : 1 ≤ t) :
    weight_upper_bound t 2 < 0.00001 := by
  -- weight(2) = 2 * log 2 / √2 * exp(-4π² * t * (log 2)²)
  -- log 2 ≈ 0.693, √2 ≈ 1.414
  -- For t ≥ 1: 4π² * (log 2)² ≈ 39.5 * 0.48 ≈ 19
  -- exp(-19) ≈ 5.6 × 10^{-9}
  -- So weight(2) ≈ 2 * 0.693 / 1.414 * 5.6e-9 ≈ 5.5e-9
  sorry
```

---

## Main Theorem

```lean
/-- The sum of weight upper bounds is less than 1/25 for t ≥ 1 -/
theorem weight_sum_le_rho_one (t : ℝ) (ht : 1 ≤ t) :
    ∑' n : ℕ, weight_upper_bound t n ≤ rho_one := by
  -- Split: n < 2 (zero), n = 2 (tiny), n ≥ 3 (exponentially small)
  -- Total < 0.00001 + 0.001 < 0.002 << 1/25 = 0.04
  sorry

/-- Specialized version for t_rkhs_cap = 40 -/
theorem weight_sum_at_tcap :
    ∑' n : ℕ, weight_upper_bound t_rkhs_cap n ≤ rho_one := by
  exact weight_sum_le_rho_one t_rkhs_cap (by norm_num : (1 : ℝ) ≤ 40)
```

---

## Proof Strategy

1. **Split the sum:** n < 2, n = 2, n ≥ 3

2. **n < 2:** Zero by definition

3. **n = 2:**
   - Explicit computation: exp(-4π² * (log 2)²) ≈ exp(-19) ≈ 5.6e-9
   - Use `norm_num` or `interval` tactic

4. **n ≥ 3:**
   - Use exp_decay_bound to get n^{-10} factor
   - Sum ∑ log(n)/n^{10.5} converges very rapidly
   - Bound by integral or explicit finite sum + tail

5. **Combine:** Total << 1/25

---

## Notes

- All bounds are extremely loose — actual sum ≈ 6×10⁻⁹
- We only need to show sum < 1/25 = 0.04
- The exponential decay makes this "trivial" numerically
- Key Mathlib lemmas: `Real.exp_neg`, `Real.rpow_neg`, summability lemmas

end
