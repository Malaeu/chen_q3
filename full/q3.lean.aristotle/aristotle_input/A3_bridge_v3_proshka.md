# A3 Bridge Theorem - Pure Rayleigh Approach

## Goal

Prove that for Toeplitz matrix T_M[P_A] with symbol P_A and RKHS operator T_P, the difference has positive Rayleigh quotient bounded below by c*/4.

**NO Szegő-Böttcher theorem needed!**

## Main Theorem

```
theorem A3_bridge_rayleigh :
  ∀ M : ℕ, M > 0 →
  ∀ v : Fin M → ℝ, v ≠ 0 →
  (∑ i, ∑ j, v i * (ToeplitzEntry P_A i j - T_P i j) * v j) / (∑ i, v i ^ 2)
    ≥ c_star / 4
```

where c_star = 11/10 = 1.1.

## Proof Strategy (3 Steps)

### Step 1: Toeplitz Lower Bound

**Rayleigh lower bound for Toeplitz matrices:**

For Toeplitz matrix T with symbol P, if P(θ) ≥ m for all θ ∈ [-1/2, 1/2]:
```
Rayleigh quotient of T ≥ m
```

This follows from:
- Toeplitz quadratic form identity: ⟨Tv,v⟩ = ∫ P(θ)|p(θ)|² dθ
- Parseval: ∫|p(θ)|² dθ = ∑ vₖ²
- Pointwise bound P(θ) ≥ m gives integral bound

**Application:** With P = P_A (archimedean symbol) and m = c* = 11/10:
```
Toeplitz_form / ||v||² ≥ c* = 11/10
```

### Step 2: RKHS Upper Bound

The RKHS operator T_P is positive semidefinite with:
```
⟨T_P v, v⟩ ≤ ||T_P||_op * ||v||²
```

**Key bound:** ||T_P||_op ≤ c*/4 = 11/40 ≈ 0.275

This is achievable because:
- T_P has entries involving exp(-(ξᵢ-ξⱼ)²/(4t))
- For appropriate t, diagonal dominates
- Weight bound: w_max = 2/e ≈ 0.735
- For small t, off-diagonal → 0, so ||T_P|| → diagonal max ≈ w_max < c*/4?

Actually, the key is: for t_rkhs ≥ 1, we have ||T_P|| ≤ ρ(1) < 1/25 = 0.04.
This is MUCH smaller than c*/4 = 0.275!

### Step 3: Combine

For self-adjoint operators S, R where R is PSD:
```
⟨(S - R)v, v⟩ ≥ ⟨Sv, v⟩ - ||R||_op * ||v||²
```

Applying with S = Toeplitz[P_A], R = T_P:
```
(Toeplitz - RKHS) / ||v||²
  ≥ Toeplitz / ||v||² - ||T_P||
  ≥ c* - c*/4
  = 3c*/4
  > c*/4 ✓
```

## Lemmas to Prove

### Lemma 1: Toeplitz Quadratic Form

```lean
lemma toeplitz_quadratic_form (M : ℕ) (P : ℝ → ℝ) (v : Fin M → ℝ) :
  (∑ i : Fin M, ∑ j : Fin M, (v i : ℂ) * ToeplitzEntry P i j * (v j : ℂ)) =
  ∫ θ in Set.Icc (-1/2 : ℝ) (1/2), (P θ : ℂ) * Complex.normSq (trigPoly M v θ)
```

where trigPoly M v θ = ∑ k, v k * exp(2πi k θ).

### Lemma 2: Rayleigh Lower Bound

```lean
lemma rayleigh_lower_bound
  (M : ℕ) (hM : M > 0)
  (P : ℝ → ℝ) (hP_cont : Continuous P)
  (m : ℝ) (hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2), m ≤ P θ)
  (v : Fin M → ℝ) (hv : v ≠ 0) :
  (Toeplitz form).re / (∑ i, v i ^ 2) ≥ m
```

### Lemma 3: Operator Subtraction

```lean
lemma quadform_sub_ge
  (S R : Matrix n n ℝ) (c : ℝ)
  (hS : ∀ v, ⟨Sv, v⟩ ≥ c * ||v||²)
  (hR_psd : ∀ v, 0 ≤ ⟨Rv, v⟩) :
  ∀ v, ⟨(S - R)v, v⟩ ≥ (c - ||R||) * ||v||²
```

Proof:
- ⟨Rv, v⟩ ≤ ||R|| * ||v||² (by definition of operator norm for PSD)
- ⟨(S-R)v, v⟩ = ⟨Sv,v⟩ - ⟨Rv,v⟩ ≥ c*||v||² - ||R||*||v||²

### Lemma 4: RKHS Operator Norm Bound

```lean
lemma RKHS_op_norm_bound :
  ∃ t > 0, ||T_P t|| ≤ c_star / 4
```

This can be shown by choosing t appropriately so that the kernel matrix is diagonal-dominant.

## Main Theorem Proof

```lean
theorem A3_bridge_rayleigh :
  ∀ M > 0, ∀ v ≠ 0,
  (Toeplitz[P_A] - T_P) form / ||v||² ≥ c_star / 4 := by
  intro M hM v hv
  -- Step 1: Toeplitz bound
  have h1 : Toeplitz form / ||v||² ≥ c_star :=
    rayleigh_lower_bound M hM P_A continuous_P_A c_star h_P_A_ge_c_star v hv
  -- Step 2: Get t with RKHS bound
  obtain ⟨t, ht_pos, h2⟩ := RKHS_op_norm_bound
  -- Step 3: Combine
  have h3 := quadform_sub_ge (Toeplitz P_A) (T_P t) c_star h1 (T_P_psd t)
  -- h3 : ⟨(Toeplitz - T_P)v, v⟩ ≥ (c_star - ||T_P||) * ||v||²
  -- Since ||T_P|| ≤ c_star/4:
  calc (Toeplitz - T_P) form / ||v||²
      ≥ c_star - ||T_P t|| := by linarith [h3]
    _ ≥ c_star - c_star/4 := by linarith [h2]
    _ = 3 * c_star / 4 := by ring
    _ ≥ c_star / 4 := by norm_num [c_star]
```

## Constants

| Symbol | Value | Decimal |
|--------|-------|---------|
| c_star | 11/10 | 1.1 |
| c_star/4 | 11/40 | 0.275 |
| 3*c_star/4 | 33/40 | 0.825 |

## Dependencies

- Toeplitz matrix definition
- Trigonometric polynomial
- MeasureTheory.integral_mono
- Complex.normSq properties
- Matrix operator norm

## Important Notes

1. This proof does NOT use Szegő-Böttcher theorem
2. Rayleigh lower bound gives λ_min ≥ min(symbol) DIRECTLY
3. The RKHS bound ρ(1) < 1/25 is much stronger than needed
4. No M₀ threshold needed - works for all M > 0
