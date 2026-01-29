# RKHS Cap for Rayleigh Quotient

## Goal

Prove that the Rayleigh quotient of the compressed prime operator T_P_comp is bounded by ρ(1) < 1/25.

This is the missing `h_cap` hypothesis needed by `A3_bridge_rayleigh_first` (V5).

---

## Core Statement

For any M and any nonzero vector v:
```
rayleighQ (T_P_comp K B 1 M) v ≤ 1/25
```

Where T_P_comp is a **rank-one sum** (PSD operator).

---

## Key Insight

T_P_comp is a sum of rank-one positive semidefinite matrices:
```
T_P_comp i j = Σ_n α_n * u_n[i] * u_n[j]
```
where α_n ≥ 0.

For such operators:
1. T_P_comp is PSD (positive semidefinite)
2. For PSD matrices: rayleighQ A v ≤ ||A|| ≤ trace(A)
3. trace(T_P_comp) = Σ_n α_n

So we just need: **Σ_n α_n < 1/25**

---

## Numeric Bound Plan (Proshka)

We do **not** need the exact integral for ρ(1). It is enough to show a clean upper bound:

1. **Exponential decay dominates**:
   For n ≥ 3, we have `log n ≥ 1`, and `4π² ≈ 39.5 > 10`, hence
   ```
   exp(-4π² (log n)²) ≤ exp(-10 log n) = n^-10.
   ```
2. **Tail bound**:
   This gives a convergent tail like `∑ n^-9.5` once you include `w_Q(n) ≈ log n / √n`.
3. **Finite head + tail**:
   Check small n explicitly (n = 2,3,4,...) and bound the tail with the p‑series.

Practical outcome:
```
∑ w_Q(n) * exp(-4π² (log n)²)  <<  1/25
```

This is sufficient for h_cap and avoids heavy analytic estimates.

---

## Definitions

```lean
open scoped BigOperators
open Finset

noncomputable section

def normSq {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  ∑ i, (v i) ^ (2 : ℕ)

def quadForm {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

def rayleighQ {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  quadForm A v / normSq v

-- Rank-one matrix from vector u with weight α
def rankOne {M : ℕ} (α : ℝ) (u : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => α * u i * u j

def rho_one : ℝ := (1 : ℝ) / 25
```

---

## Abstract Setup (parameterized)

```lean
variable (NodesK : Type) [Fintype NodesK]
variable (weight : NodesK → ℝ)        -- α_n weights
variable (basis_vec : NodesK → (M : ℕ) → Fin M → ℝ)  -- u_n vectors

-- Assume weights are nonnegative
variable (h_weight_nonneg : ∀ n, 0 ≤ weight n)

-- Assume basis vectors are normalized: ||u_n||² = 1
variable (h_basis_norm : ∀ n M, ∑ i : Fin M, (basis_vec n M i)^2 = 1)

-- Sum of weights is bounded
variable (h_weight_sum : ∑ n : NodesK, weight n ≤ rho_one)

-- T_P_comp as rank-one sum
def T_P_comp_abstract (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => ∑ n : NodesK, weight n * basis_vec n M i * basis_vec n M j
```

---

## Lemmas to Prove

### Lemma 1: Quadratic form of rank-one matrix

```lean
lemma quadForm_rankOne {M : ℕ} (α : ℝ) (u v : Fin M → ℝ) :
    quadForm (rankOne α u) v = α * (∑ i, u i * v i)^2 := by
  -- Expand definitions and use commutativity
  simp [quadForm, rankOne]
  ring_nf
  -- The double sum collapses to α * (Σ u_i v_i)²
  sorry
```

### Lemma 2: Rank-one quadratic form is nonnegative when α ≥ 0

```lean
lemma quadForm_rankOne_nonneg {M : ℕ} (α : ℝ) (u v : Fin M → ℝ) (hα : 0 ≤ α) :
    0 ≤ quadForm (rankOne α u) v := by
  rw [quadForm_rankOne]
  apply mul_nonneg hα
  apply sq_nonneg
```

### Lemma 3: Quadratic form of sum = sum of quadratic forms

```lean
lemma quadForm_sum {M : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
    quadForm (∑ i, A i) v = ∑ i, quadForm (A i) v := by
  simp [quadForm, Finset.sum_comm]
  -- Linear in the matrix argument
  sorry
```

### Lemma 4: Rayleigh quotient bounded by sum of weights (KEY!)

```lean
lemma rayleighQ_rankOne_sum_le
    {M : ℕ} {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (u : ι → Fin M → ℝ) (v : Fin M → ℝ)
    (hα : ∀ i, 0 ≤ α i)
    (hu : ∀ i, ∑ j : Fin M, (u i j)^2 = 1)
    (hv : v ≠ 0) :
    rayleighQ (fun i j => ∑ n, α n * u n i * u n j) v ≤ ∑ n, α n := by
  -- Key steps:
  -- 1. quadForm = Σ_n α_n * (Σ_i u_n[i] v[i])²
  -- 2. By Cauchy-Schwarz: (Σ_i u_n[i] v[i])² ≤ ||u_n||² * ||v||² = ||v||²
  -- 3. So quadForm ≤ Σ_n α_n * ||v||²
  -- 4. rayleighQ = quadForm / ||v||² ≤ Σ_n α_n
  sorry
```

---

## Main Theorem

```lean
theorem rkhs_cap_rayleigh
    (NodesK : Type) [Fintype NodesK]
    (weight : NodesK → ℝ)
    (basis_vec : NodesK → (M : ℕ) → Fin M → ℝ)
    (h_weight_nonneg : ∀ n, 0 ≤ weight n)
    (h_basis_norm : ∀ n M, ∑ i : Fin M, (basis_vec n M i)^2 = 1)
    (h_weight_sum : ∑ n : NodesK, weight n ≤ rho_one)
    : ∀ M : ℕ, ∀ v : Fin M → ℝ, v ≠ 0 →
        rayleighQ (T_P_comp_abstract NodesK weight basis_vec M) v ≤ rho_one := by
  intro M v hv
  calc rayleighQ (T_P_comp_abstract NodesK weight basis_vec M) v
      ≤ ∑ n : NodesK, weight n := rayleighQ_rankOne_sum_le _ _ v h_weight_nonneg h_basis_norm hv
    _ ≤ rho_one := h_weight_sum
```

---

## What Aristotle Should Output

A Lean file proving:

1. `quadForm_rankOne` — quadratic form of rank-one matrix
2. `quadForm_sum` — linearity of quadratic form
3. `rayleighQ_rankOne_sum_le` — KEY: Rayleigh quotient bounded by weight sum (uses Cauchy-Schwarz)
4. `rkhs_cap_rayleigh` — main theorem

The proof uses:
- Cauchy-Schwarz inequality: (Σ u_i v_i)² ≤ ||u||² ||v||²
- Fact that basis vectors are normalized
- Nonnegativity of weights

No Szegő-Böttcher. No complex analysis. Just linear algebra.

---

end
