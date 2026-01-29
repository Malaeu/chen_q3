# RKHS Cap at t_rkhs = 1 (Proshka's Chain)

## Goal

Prove that `rayleighQ (T_P_comp K B 1 M) ≤ 1/25` for the compressed prime operator.

This closes the `h_cap` hypothesis needed by V5 (A3_bridge_rayleigh_first).

---

## Core Chain (4 Steps)

```
rayleighQ T_P_comp ≤ ∑ weights    (Cauchy-Schwarz for rank-one sum)
                  ≤ ρ(1)          (integral domination)
                  < 1/25          (numeric bound)
```

---

## Definitions

```lean
import Mathlib

open scoped BigOperators
open Finset Real

set_option maxHeartbeats 0

noncomputable section

-- Rayleigh quotient (same as V5)
def normSq {M : ℕ} (v : Fin M → ℝ) : ℝ := ∑ i, (v i) ^ 2

def quadForm {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

def rayleighQ {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  quadForm A v / normSq v

-- Rank-one matrix: α * |u⟩⟨u|
def rankOne {M : ℕ} (α : ℝ) (u : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => α * u i * u j

-- T_P_comp as a sum of rank-one matrices (compression form)
-- T_P_comp i j = Σ_n α_n * u_n[i] * u_n[j]
-- where α_n = w_Q(n) * Φ_{B,t}(ξ_n) ≥ 0
-- and u_n is normalized: ||u_n||² = 1

variable {NodesK : Type} [Fintype NodesK] [DecidableEq NodesK]

-- Coefficient for each node (weight × window)
variable (coeff : NodesK → ℝ)
-- Basis vectors (normalized)
variable (basis : NodesK → (M : ℕ) → Fin M → ℝ)

-- Assumptions
variable (h_coeff_nonneg : ∀ n, 0 ≤ coeff n)
variable (h_basis_norm : ∀ n M, ∑ i : Fin M, (basis n M i)^2 = 1)

-- T_P_comp as rank-one sum
def T_P_comp_rankone (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => ∑ n : NodesK, coeff n * basis n M i * basis n M j

-- ρ(1) bound constant
def rho_one : ℝ := 1 / 25
```

---

## Important Notes (from Proshka review)

1. **Edge case M=0:** If M=0, then `Fin M` is empty, so `v ≠ 0` is vacuously false.
   The theorem is vacuously true. No `NeZero M` typeclass needed.

2. **Non-orthogonal basis:** The basis vectors are NOT orthogonal, but this is fine!
   We apply Cauchy-Schwarz to EACH term separately, not to the whole sum.
   The bound `rayleighQ ≤ Σ coeff` comes from per-term CS, not operator norm triangle.

3. **Match V5 definitions:** Use same `normSq`, `quadForm`, `rayleighQ` as V5.

---

## Key Lemmas to Prove

### Lemma 1: Inner product bound (Cauchy-Schwarz)

For normalized u (||u||² = 1) and any v:
```lean
lemma inner_sq_le_normSq {M : ℕ} (u v : Fin M → ℝ)
    (hu : ∑ i, (u i)^2 = 1) :
    (∑ i, u i * v i)^2 ≤ ∑ i, (v i)^2 := by
  -- Cauchy-Schwarz: (Σ u_i v_i)² ≤ ||u||² ||v||² = 1 × ||v||²
  sorry
```

### Lemma 2: Quadratic form of rank-one matrix

```lean
lemma quadForm_rankOne {M : ℕ} (α : ℝ) (u v : Fin M → ℝ) :
    quadForm (rankOne α u) v = α * (∑ i, u i * v i)^2 := by
  -- Expand: Σ_i Σ_j v_i (α u_i u_j) v_j = α (Σ_i u_i v_i)²
  sorry
```

### Lemma 3: Quadratic form of sum = sum of quadratic forms

```lean
lemma quadForm_sum {M : ℕ} {ι : Type*} [Fintype ι]
    (As : ι → Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
    quadForm (∑ n, As n) v = ∑ n, quadForm (As n) v := by
  -- Linear in matrix argument
  sorry
```

### Lemma 4: Rayleigh quotient of rank-one sum ≤ sum of coefficients (KEY!)

```lean
lemma rayleighQ_rankone_sum_le
    {M : ℕ} [NeZero M]
    (coeff : NodesK → ℝ) (basis : NodesK → Fin M → ℝ)
    (v : Fin M → ℝ)
    (h_coeff_nonneg : ∀ n, 0 ≤ coeff n)
    (h_basis_norm : ∀ n, ∑ i : Fin M, (basis n i)^2 = 1)
    (hv : v ≠ 0) :
    rayleighQ (fun i j => ∑ n : NodesK, coeff n * basis n i * basis n j) v
      ≤ ∑ n : NodesK, coeff n := by
  -- Strategy:
  -- 1. quadForm = Σ_n coeff_n * (Σ_i basis_n[i] v[i])²  (by Lemma 2, 3)
  -- 2. By Cauchy-Schwarz: (Σ_i basis_n[i] v[i])² ≤ ||v||² (by Lemma 1)
  -- 3. So quadForm ≤ Σ_n coeff_n * ||v||²
  -- 4. rayleighQ = quadForm / ||v||² ≤ Σ_n coeff_n
  sorry
```

---

## Main Theorem

```lean
/-- RKHS cap: rayleighQ of compression ≤ sum of coefficients ≤ 1/25 -/
theorem rkhs_cap_rayleigh_t1
    {M : ℕ} [NeZero M]
    (coeff : NodesK → ℝ) (basis : NodesK → Fin M → ℝ)
    (h_coeff_nonneg : ∀ n, 0 ≤ coeff n)
    (h_basis_norm : ∀ n, ∑ i : Fin M, (basis n i)^2 = 1)
    (h_coeff_sum : ∑ n : NodesK, coeff n ≤ rho_one)
    : ∀ v : Fin M → ℝ, v ≠ 0 →
        rayleighQ (fun i j => ∑ n : NodesK, coeff n * basis n i * basis n j) v
          ≤ rho_one := by
  intro v hv
  calc rayleighQ (fun i j => ∑ n : NodesK, coeff n * basis n i * basis n j) v
      ≤ ∑ n : NodesK, coeff n := rayleighQ_rankone_sum_le coeff basis v h_coeff_nonneg h_basis_norm hv
    _ ≤ rho_one := h_coeff_sum
```

---

## Proof Outline

**Step 1: quadForm of rank-one**
- `quadForm (α * |u⟩⟨u|) v = α * ⟨u,v⟩²`
- Direct expansion of double sum

**Step 2: Cauchy-Schwarz**
- `⟨u,v⟩² ≤ ||u||² ||v||²`
- When ||u||² = 1: `⟨u,v⟩² ≤ ||v||²`
- Use `inner_mul_le_norm_mul_norm` from Mathlib

**Step 3: Sum bound**
- `quadForm T_P_comp v = Σ_n coeff_n * ⟨basis_n, v⟩²`
- `≤ Σ_n coeff_n * ||v||²` (by Step 2)
- `= ||v||² * Σ_n coeff_n`

**Step 4: Rayleigh quotient**
- `rayleighQ = quadForm / ||v||²`
- `≤ (||v||² * Σ coeff) / ||v||²`
- `= Σ coeff`

**Step 5: Apply bound**
- Given `Σ coeff ≤ 1/25`, done.

---

## What Aristotle Should Produce

A Lean file with:
1. `inner_sq_le_normSq` — Cauchy-Schwarz for normalized vectors
2. `quadForm_rankOne` — quadratic form of rank-one matrix
3. `quadForm_sum` — linearity
4. `rayleighQ_rankone_sum_le` — KEY lemma
5. `rkhs_cap_rayleigh_t1` — main theorem

No integrals, no ρ(t) definition needed — that's handled by the hypothesis `h_coeff_sum`.

The proof uses only:
- Cauchy-Schwarz inequality
- Basic sum manipulation
- Normalization of basis vectors

---

## Notes

- This is SIMPLER than the previous request (no operator norm, no integrals)
- The bound `Σ coeff ≤ 1/25` is passed as hypothesis (already verified numerically: ~6×10⁻⁹)
- Pure linear algebra, no analysis

end
