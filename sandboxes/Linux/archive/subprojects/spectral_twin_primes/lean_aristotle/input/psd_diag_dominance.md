# PSD Diagonal Dominance — Elementary Proof

## Goal
Prove that for a positive semi-definite kernel and non-negative weights, the full quadratic form dominates its diagonal.

## Definitions

```lean4
-- Gaussian kernel (strictly positive for ALL arguments)
def K (t : ℝ) (ξ_p ξ_q : ℝ) : ℝ := 2 * Real.pi * t * Real.exp (-(ξ_p - ξ_q)^2 / (4 * t))

-- Twin weights (non-negative)
def lambda (p : ℕ) : ℝ := if is_twin_prime p then Real.log p * Real.log (p + 2) else 0

-- Full energy (quadratic form)
def E_full (X : ℕ) (t : ℝ) (ξ : ℕ → ℝ) : ℝ :=
  ∑ p in twins_up_to X, ∑ q in twins_up_to X, lambda p * lambda q * K t (ξ p) (ξ q)

-- Diagonal energy
def E_diag (X : ℕ) (t : ℝ) (ξ : ℕ → ℝ) : ℝ :=
  ∑ p in twins_up_to X, (lambda p)^2 * K t (ξ p) (ξ p)
```

## Axioms (Elementary Facts)

### Axiom 1: Gaussian is strictly positive
For all t > 0 and all ξ_p, ξ_q ∈ ℝ:
```
K(t, ξ_p, ξ_q) = 2πt · exp(-(ξ_p - ξ_q)²/(4t)) > 0
```
The exponential function is always positive, and 2πt > 0 for t > 0.

### Axiom 2: Twin weights are non-negative
For all p:
```
lambda(p) ≥ 0
```
Because lambda(p) = log(p) · log(p+2) ≥ 0 for p ≥ 1, and = 0 for non-twins.

### Axiom 3: Diagonal value
On the diagonal (ξ_p = ξ_q):
```
K(t, ξ_p, ξ_p) = 2πt · exp(0) = 2πt
```

## Theorems to Prove

### Theorem 1: kernel_positive
```lean4
theorem kernel_positive (t : ℝ) (ht : t > 0) (x y : ℝ) : K t x y > 0 := by
  -- exp is always positive, 2πt > 0
  sorry
```

### Theorem 2: cross_term_nonneg
For non-negative weights and positive kernel, each cross term is non-negative:
```lean4
theorem cross_term_nonneg (t : ℝ) (ht : t > 0) (λp λq : ℝ) (hλp : λp ≥ 0) (hλq : λq ≥ 0)
    (ξp ξq : ℝ) : λp * λq * K t ξp ξq ≥ 0 := by
  -- Product of non-negatives with positive kernel
  sorry
```

### Theorem 3: sum_cross_terms_nonneg
The sum of all off-diagonal terms is non-negative:
```lean4
theorem sum_cross_terms_nonneg (X : ℕ) (t : ℝ) (ht : t > 0) (ξ : ℕ → ℝ) :
    ∑ p in twins_up_to X, ∑ q in twins_up_to X,
      (if p ≠ q then lambda p * lambda q * K t (ξ p) (ξ q) else 0) ≥ 0 := by
  -- Sum of non-negative terms
  sorry
```

### Theorem 4: diag_dominance (MAIN)
```lean4
theorem diag_dominance (X : ℕ) (t : ℝ) (ht : t > 0) (ξ : ℕ → ℝ) :
    E_full X t ξ ≥ E_diag X t ξ := by
  -- E_full = E_diag + (off-diagonal terms)
  -- Off-diagonal terms ≥ 0 by sum_cross_terms_nonneg
  -- Therefore E_full ≥ E_diag
  sorry
```

## Proof Outline

The proof is elementary:

1. **Split the sum:**
   ```
   E_full = Σᵢⱼ λᵢλⱼKᵢⱼ = Σᵢ λᵢ²Kᵢᵢ + Σᵢ≠ⱼ λᵢλⱼKᵢⱼ = E_diag + E_off
   ```

2. **Show E_off ≥ 0:**
   - Each term λᵢλⱼKᵢⱼ for i≠j
   - λᵢ ≥ 0 (twin weight)
   - λⱼ ≥ 0 (twin weight)
   - Kᵢⱼ > 0 (Gaussian strictly positive)
   - Therefore λᵢλⱼKᵢⱼ ≥ 0

3. **Conclude:**
   ```
   E_full = E_diag + E_off ≥ E_diag + 0 = E_diag  ✓
   ```

## Hints for Lean4

- Use `Finset.sum_nonneg` for sums of non-negative terms
- Use `Real.exp_pos` for positivity of exponential
- Use `mul_nonneg` for products of non-negatives
- The split can be done via `Finset.sum_filter` with predicate `p = q` vs `p ≠ q`

## Expected Output

This is a 5-line proof in essence:
```
K > 0           (Gaussian positive)
λ ≥ 0           (weights non-negative)
λᵢλⱼKᵢⱼ ≥ 0     (product of non-negatives with positive)
Σᵢ≠ⱼ(...) ≥ 0   (sum of non-negatives)
E_full ≥ E_diag (QED)
```
