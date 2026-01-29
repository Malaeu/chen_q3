/--
Sandbox for Aristotle (Rayleigh-Q identification helpers).
Goal: prove small algebraic lemmas about basis0 and quadratic forms.
-/

import Mathlib

open scoped BigOperators

noncomputable section

/-- Basis vector for the constant polynomial p = 1. -/
def basis0 (M : ℕ) : Fin (2 * M + 1) → ℝ :=
  let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩
  fun i => if i = i0 then (1 : ℝ) else 0

/-- Quadratic form for a real matrix. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

/-- Rayleigh quotient for a real matrix. -/
def RayleighQuotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  quadForm A v / (∑ i, v i ^ 2)

/-- The basis0 vector has unit squared norm. -/
theorem basis0_norm_sq (M : ℕ) :
    (∑ i : Fin (2 * M + 1), (basis0 M i) ^ 2) = 1 := by
  sorry

/-- Quadratic form at basis0 is the diagonal entry. -/
theorem quadForm_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    quadForm A (basis0 M) =
      (let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩; A i0 i0) := by
  sorry

/-- Rayleigh quotient at basis0 is the diagonal entry. -/
theorem rayleigh_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    RayleighQuotient A (basis0 M) =
      (let i0 : Fin (2 * M + 1) := ⟨M, by nlinarith⟩; A i0 i0) := by
  -- Use basis0_norm_sq and quadForm_basis0.
  sorry
