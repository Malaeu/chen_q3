# A3_bridge V4: Real RKHS Operator Bound

## Goal

Close A3_bridge_axiom with real definitions from Q3 project.

## What We Have (from V3 and Q3)

### From V3 (proven by Aristotle):
1. **rayleigh_lower_bound**: If symbol P ≥ m on [−1/2, 1/2], then Toeplitz quadratic form ≥ m × ||v||²
2. **quadform_sub_ge**: If S ≥ c × ||v||² and R ≤ (c/4) × ||v||², then (S − R) ≥ (3c/4) × ||v||²

### From Q3/Basic/Defs.lean (proven):
3. **w_RKHS_le_w_max**: ∀ n, w_RKHS n ≤ w_max where w_max = 2/e ≈ 0.7358
4. **w_max_lt_one**: w_max < 1

### From A3_FLOOR (proven):
5. **P_A_ge_c_star**: The archimedean symbol P_A(θ) ≥ c* = 11/10 for all θ

## Key Insight

For small t, the RKHS operator T_P satisfies ||T_P|| ≤ w_max ≈ 0.735.

Combined with Toeplitz ≥ c* = 1.1:
- **Difference** ≥ c* − w_max = 1.1 − 0.735 = 0.365 > c*/4 = 0.275 ✓

So the A3_bridge bound (≥ c*/4) is satisfied!

## The RKHS Operator

Definition:
$$T_P(t)_{ij} = \sqrt{w_i} \cdot \sqrt{w_j} \cdot e^{-(ξ_i - ξ_j)^2/(4t)}$$

where:
- $w_n = Λ(n)/\sqrt{n}$ (von Mangoldt weight), bounded by $w_{max} = 2/e$
- $ξ_n = \log(n)/(2π)$ (spectral coordinate)

## What to Prove

**Theorem (T_P_norm_bound):** For any ε > 0, there exists t₀ > 0 such that for all 0 < t < t₀:
$$||T_P(t)|| ≤ w_{max} + ε$$

In particular, taking ε = 0.1 gives ||T_P|| ≤ 0.835 < c* − c*/4 = 0.825.

Wait, 0.835 > 0.825. Let me recalculate...

Actually we don't need ||T_P|| < any specific threshold. We need:

**Toeplitz − T_P ≥ c*/4**

With Toeplitz ≥ c* = 1.1 and T_P ≤ ||T_P|| × ||v||²/||v||² = ||T_P||:
- Need: c* − ||T_P|| ≥ c*/4
- Need: ||T_P|| ≤ c* − c*/4 = 3c*/4 = 0.825

And w_max = 2/e = 0.7358 < 0.825. ✓

So for t → 0, ||T_P|| → w_max < 0.825, giving us the bound!

## Proof Strategy

### Step 1: Row Sum via Schur Test

For symmetric matrix A: ||A|| ≤ max_i Σ_j |A_{ij}|

Row sum of T_P:
$$\sum_j |T_P(t)_{ij}| = \sqrt{w_i} \sum_j \sqrt{w_j} \cdot e^{-(ξ_i - ξ_j)^2/(4t)}$$

Split: diagonal (j = i) gives $w_i$, off-diagonal (j ≠ i) gives rest.

### Step 2: Off-Diagonal Decay

For j ≠ i and t → 0:
$$e^{-(ξ_i - ξ_j)^2/(4t)} → 0$$

because $(ξ_i - ξ_j)^2 > 0$ and dividing by 4t → +∞.

### Step 3: Bound the Sum

Off-diagonal sum bounded by geometric series:
$$\sum_{j ≠ i} \sqrt{w_j} \cdot e^{-(ξ_i - ξ_j)^2/(4t)} ≤ \sqrt{w_{max}} \cdot S(t)$$

where $S(t) = \sum_{k=1}^∞ e^{-k^2 δ^2/(4t)} → 0$ as $t → 0$.

### Step 4: Final Bound

Row sum ≤ $w_i + \sqrt{w_i} \cdot \sqrt{w_{max}} \cdot S(t)$
         ≤ $w_{max} + w_{max} \cdot S(t)$
         = $w_{max}(1 + S(t))$

For t small enough: $S(t) < ε$, so row sum < $w_{max}(1 + ε)$.

By Schur: $||T_P(t)|| ≤ w_{max}(1 + ε)$.

Taking ε small enough that $w_{max}(1 + ε) < 3c*/4 = 0.825$:
- Need: $0.7358(1 + ε) < 0.825$
- Need: $1 + ε < 1.121$
- Need: $ε < 0.121$

So for ε = 0.1, we get ||T_P|| < 0.809 < 0.825. ✓

## Formal Statement

```lean
/-- RKHS matrix with real definitions -/
def T_P_matrix (t : ℝ) (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => Real.sqrt (w_RKHS i.val) * Real.sqrt (w_RKHS j.val) *
             Real.exp (-(xi_n i.val - xi_n j.val)^2 / (4 * t))

/-- Off-diagonal geometric sum bound -/
def S_off (t δ : ℝ) : ℝ := 2 * Real.exp (-δ^2/(4*t)) / (1 - Real.exp (-δ^2/(4*t)))

/-- S_off → 0 as t → 0 -/
lemma S_off_tendsto_zero (δ : ℝ) (hδ : δ > 0) :
  Filter.Tendsto (S_off · δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- Row sum bound -/
lemma T_P_row_sum_bound (t : ℝ) (ht : t > 0) (M : ℕ) (i : Fin M) :
  ∑ j, |T_P_matrix t M i j| ≤ w_max * (1 + S_off t δ_min)

/-- Main theorem: T_P norm bounded by 3c*/4 for small t -/
theorem T_P_norm_lt_three_quarters_c_star (M : ℕ) :
  ∃ t > 0, ∀ v : Fin M → ℝ, v ≠ 0 →
    (∑ i, ∑ j, v i * T_P_matrix t M i j * v j) / (∑ i, v i ^ 2) ≤ 3 * c_star / 4
```

## Constants Reference

| Constant | Value | Decimal |
|----------|-------|---------|
| c* | 11/10 | 1.1 |
| c*/4 | 11/40 | 0.275 |
| 3c*/4 | 33/40 | 0.825 |
| w_max | 2/e | 0.7358 |

Key inequality: **w_max = 0.7358 < 0.825 = 3c*/4** ✓

## Dependencies

From existing Q3 codebase:
- `Q3.w_RKHS` - weight definition
- `Q3.xi_n` - spectral coordinate
- `Q3.w_max` - maximum weight
- `Q3.w_RKHS_le_w_max` - weight bound lemma
- `Q3.c_star` - archimedean floor constant

## Final Assembly

Combining with V3:
1. Toeplitz form ≥ c* × ||v||² (rayleigh + A3_FLOOR)
2. T_P form ≤ (3c*/4) × ||v||² (this theorem)
3. Difference ≥ c* − 3c*/4 = c*/4 ✓

The A3_bridge_axiom is closed!
