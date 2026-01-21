# A3 Bridge Closure (v2 - Corrected)

## Goal

Prove A3_bridge_data_uniform using Rayleigh lower bound.
NO Szegő-Böttcher needed!

## Key Result Already Proven

### Rayleigh Lower Bound (rayleigh_v1.lean)

For Toeplitz matrix T with symbol P, if P(θ) ≥ m for all θ ∈ [-1/2, 1/2]:
```
Rayleigh quotient of T ≥ m
```

Specifically:
```lean
theorem rayleigh_lower_bound
    (M : ℕ) (hM : M > 0)
    (P : ℝ → ℝ) (hP_cont : Continuous P)
    (m : ℝ) (hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2), m ≤ P θ)
    (v : Fin M → ℝ) (hv : v ≠ 0) :
    (Toeplitz quadratic form).re / (∑ i, v i ^ 2) ≥ m
```

### A3_FLOOR (proven)

```
P_A(θ) ≥ c* = 11/10 for all θ
```

## What to Prove

```lean
theorem A3_bridge_closure :
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (Toeplitz[a_star](i,j) - RKHS_kernel(i,j,t))) /
    (∑ i, v i ^ 2) ≥ c_star / 4
```

where c_star = 11/10.

## Proof Strategy

### Step 1: Toeplitz Term (from Rayleigh + A3_FLOOR)

By Rayleigh lower bound with P = a_star (archimedean symbol):
```
(Toeplitz quadratic form) / ||v||² ≥ min(P_A) ≥ c* = 1.1
```

### Step 2: RKHS Term Bound

The RKHS kernel matrix T_P has entries:
```
T_P[i,j] = √(w_RKHS(i)) √(w_RKHS(j)) exp(-(ξᵢ - ξⱼ)² / (4t))
```

Key: the term `exp(-(ξᵢ - ξⱼ)² / (4t))` where t is in DENOMINATOR.

**For t SMALL (not large!):**
- exp(-big/(4×small)) = exp(-∞) → 0 for i ≠ j
- Off-diagonal terms vanish

**Operator norm bound:**
```
||T_P|| ≤ w_max × (1 + S(t))
```
where:
- w_max = 2/e ≈ 0.735 (max of w_RKHS)
- S(t) = ∑_{k≠0} exp(-δ²k²/(4t)) → 0 as t → 0⁺

For small enough t: ||T_P|| ≤ 3c*/4 = 0.825

### Step 3: Combine

```
(Toeplitz - RKHS) / ||v||²
  ≥ (Toeplitz / ||v||²) - ||T_P||
  ≥ c* - 3c*/4
  = c*/4 = 0.275 ✓
```

## Key Lemmas

### Lemma 1: Toeplitz Rayleigh Bound

```lean
lemma toeplitz_rayleigh_ge_c_star (M : ℕ) (hM : M > 0) (v : Fin M → ℝ) (hv : v ≠ 0) :
    (∑ i, ∑ j, v i * ToeplitzEntry_a_star M i j * v j) / (∑ i, v i ^ 2) ≥ c_star := by
  -- Apply rayleigh_lower_bound with P = a_star and m = c_star
  -- Uses A3_FLOOR: a_star(θ) ≥ c_star for all θ
  sorry
```

### Lemma 2: RKHS Operator Norm Bound for Small t

```lean
lemma RKHS_norm_small (ε : ℝ) (hε : ε > 0) :
    ∃ t > 0, ∀ K ≥ 1, ∀ M : ℕ, ∀ v : Fin M → ℝ,
    (∑ i, ∑ j, v i * RKHS_kernel i j t * v j) / (∑ i, v i ^ 2) ≤ ε := by
  -- Choose t small enough that off-diagonal terms are negligible
  -- S(t) = 2×exp(-δ²/(4t))/(1-exp(-δ²/(4t))) → 0 as t → 0⁺
  sorry
```

### Lemma 3: Main Theorem

```lean
theorem A3_bridge_from_Rayleigh : A3_bridge_data_uniform := by
  -- Choose t such that ||T_P|| ≤ 3c*/4
  -- Then Toeplitz - RKHS ≥ c* - 3c*/4 = c*/4
  obtain ⟨t, ht_pos, hRKHS⟩ := RKHS_norm_small (3 * c_star / 4) (by norm_num)
  refine ⟨1, t, ht_pos, ?_⟩
  intro M hM v hv
  have hToep := toeplitz_rayleigh_ge_c_star M (Nat.one_le_iff_ne_zero.mp hM) v hv
  -- Combine bounds
  linarith [hRKHS 1 (le_refl 1) M v]
```

## Mathlib Dependencies

- `MeasureTheory.integral_mono` — integral monotonicity
- `Real.exp_neg_tendsto_atTop` — exponential decay
- `Matrix.innerProduct` — quadratic forms
- `Finset.sum_le_sum` — sum bounds
- Schur test for operator norm

## Constants

| Symbol | Value | Decimal |
|--------|-------|---------|
| c* | 11/10 | 1.1 |
| c*/4 | 11/40 | 0.275 |
| 3c*/4 | 33/40 | 0.825 |
| w_max | 2/e | 0.735 |

## Note

This proof does NOT use Szegő-Böttcher theorem!
The Rayleigh lower bound gives λ_min ≥ min(symbol) DIRECTLY.
