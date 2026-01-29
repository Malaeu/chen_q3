# A3 Bridge Axiom Closure

## Goal

Prove the A3 bridge theorem: for Toeplitz matrix T with symbol P_A minus RKHS kernel matrix T_P, the Rayleigh quotient is bounded below by c*/4 where c* = 11/10.

## What We Have (Already Proven)

### 1. Rayleigh Lower Bound for Toeplitz Matrices

For a Toeplitz matrix T with symbol P : ℝ → ℝ, if P(θ) ≥ m for all θ ∈ [-1/2, 1/2], then the Rayleigh quotient satisfies:

```
(∑ᵢ ∑ⱼ vᵢ Tᵢⱼ vⱼ) / (∑ᵢ vᵢ²) ≥ m
```

This was proven in `rayleigh_v1.lean` using:
- Toeplitz quadratic form = ∫ P(θ) |p(θ)|² dθ where p is the trig polynomial
- Parseval identity: ∫ |p(θ)|² dθ = ∑ vₖ²
- Pointwise bound P(θ) ≥ m gives integral bound

### 2. A3_FLOOR: Symbol Lower Bound

The archimedean symbol P_A satisfies:
```
P_A(θ) ≥ c* = 11/10 for all θ ∈ [-1/2, 1/2]
```

This is proven in `A3_FLOOR_v22_stage4_floor.lean`.

### 3. RKHS Kernel Properties

The RKHS kernel matrix T_P with entries:
```
T_P[i,j] = √(w_RKHS(i)) √(w_RKHS(j)) exp(-(ξᵢ - ξⱼ)² / (4t))
```

where:
- w_RKHS(n) = Λ(n) / √n (von Mangoldt / sqrt)
- ξₙ = log n (node positions)
- t > 0 is heat parameter

Key bound: w_RKHS(n) ≤ w_max = 2/e for all n.

## What to Prove

### Main Theorem: A3_bridge_data_uniform

```lean
theorem A3_bridge_closure :
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzEntry_a_star i j - T_P i j t)) /
    (∑ i, v i ^ 2) ≥ c_star / 4
```

where c_star = 11/10.

## Proof Strategy

**Step 1: Toeplitz Term**
By Rayleigh lower bound + A3_FLOOR:
```
(Toeplitz(a_star) form) / ‖v‖² ≥ min(P_A) ≥ c* = 11/10
```

**Step 2: RKHS Term Upper Bound**
Choose t large enough so that the RKHS kernel is very small.

For the heat kernel exp(-(ξᵢ - ξⱼ)² / (4t)):
- As t → ∞, off-diagonal terms → 0 exponentially slow
- Diagonal terms = w_RKHS(i) (since exp(0) = 1)

Quadratic form bound:
```
(RKHS form) / ‖v‖² ≤ ‖T_P‖_op
```

We need: ‖T_P‖_op ≤ 3c*/4 = 33/40 ≈ 0.825

**Step 3: Combined**
```
(Toeplitz - RKHS) / ‖v‖² ≥ c* - 3c*/4 = c*/4
```

## Key Lemmas to Prove

### Lemma 1: RKHS Row Sum Bound

For the RKHS matrix T_P:
```
∑ⱼ |T_P[i,j]| ≤ w_max * (1 + S(t))
```
where S(t) = ∑_{k≠0} exp(-δ²k² / (4t)) is a convergent series.

For t large: S(t) → 0.

### Lemma 2: RKHS Operator Norm

By Schur test (row/column sum bound):
```
‖T_P‖_op ≤ max_row ∑ⱼ |T_P[i,j]| ≤ w_max * (1 + S(t))
```

Choose t such that w_max * (1 + S(t)) ≤ 3c*/4.

Since w_max = 2/e ≈ 0.735 and c* = 1.1:
- 3c*/4 = 0.825
- Need: 0.735 * (1 + S(t)) ≤ 0.825
- Need: 1 + S(t) ≤ 1.122
- Need: S(t) ≤ 0.122

This is achievable for large enough t.

### Lemma 3: Difference of Quadratic Forms

For positive semidefinite A with λ_min(A) ≥ a and B with ‖B‖_op ≤ b:
```
⟨v, (A - B)v⟩ / ⟨v,v⟩ ≥ a - b
```

## Definitions Needed

```lean
-- Toeplitz entry from archimedean symbol
def ToeplitzEntry_a_star (i j : ℕ) : ℝ :=
  ∫ θ in Set.Icc (-1/2 : ℝ) (1/2), a_star θ * Real.cos (2 * π * (i - j) * θ)

-- RKHS kernel matrix entry
def T_P (i j : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
  Real.exp (-(Real.log i - Real.log j)^2 / (4 * t))

-- c* constant
def c_star : ℝ := 11 / 10
```

## Mathlib Lemmas to Use

- `Matrix.norm_le_iff` - operator norm bounds
- `MeasureTheory.integral_mono` - integral monotonicity
- `Real.exp_neg_sq_tendsto_zero` - heat kernel decay
- Schur test for operator norm bounds
- `Finset.sum_le_sum` - sum bounds

## Notes

This proof combines:
1. Rayleigh theory (already proven in rayleigh_v1.lean)
2. A3_FLOOR (P_A ≥ c*)
3. RKHS operator norm control via heat parameter t

The key insight is choosing t LARGE to make RKHS term small, not just showing ‖T_P‖ < 1.
