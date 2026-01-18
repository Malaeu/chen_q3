/-
Rayleigh basis0 helpers (shared).

This module isolates basis0 and its Rayleigh properties so it can be imported
without pulling in heavy Rayleigh/Q-identification dependencies.
-/

import Q3.Axioms

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.RayleighQId

/-- The index M is valid in Fin (2*M+1). -/
lemma M_lt_2M_add_1 (M : ℕ) : M < 2 * M + 1 := by omega

/-- Canonical middle index i0 = M in Fin (2*M+1). -/
def i0 (M : ℕ) : Fin (2 * M + 1) := ⟨M, M_lt_2M_add_1 M⟩

/-- Basis vector: 1 at position M, 0 elsewhere.
    Represents the constant polynomial p ≡ 1 in Fourier basis. -/
def basis0 (M : ℕ) : Fin (2 * M + 1) → ℝ :=
  fun i => if i.val = M then (1 : ℝ) else 0

/-- basis0 has unit squared norm. -/
theorem basis0_norm_sq (M : ℕ) :
    (∑ i : Fin (2 * M + 1), (basis0 M i) ^ 2) = 1 := by
  have h_zero : ∀ i : Fin (2 * M + 1), i ≠ i0 M → (basis0 M i) ^ 2 = 0 := by
    intro i hi
    simp only [basis0]
    have : i.val ≠ M := fun heq => hi (Fin.ext heq)
    simp [this]
  have h_one : (basis0 M (i0 M)) ^ 2 = 1 := by simp [basis0, i0]
  rw [Finset.sum_eq_single (i0 M)]
  · exact h_one
  · intro b _ hb; exact h_zero b hb
  · intro h; exfalso; exact h (Finset.mem_univ _)

/-- basis0 is nonzero. -/
theorem basis0_ne_zero (M : ℕ) : basis0 M ≠ 0 := by
  intro h
  have : basis0 M (i0 M) = 0 := by rw [h]; rfl
  simp [basis0, i0] at this

/-- Quadratic form of A at basis0 equals the diagonal entry A[i0, i0]. -/
theorem quadForm_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    (∑ i, ∑ j, basis0 M i * A i j * basis0 M j) = A (i0 M) (i0 M) := by
  have h_inner : ∀ i : Fin (2 * M + 1),
      (∑ j, basis0 M i * A i j * basis0 M j) =
        if i = i0 M then A (i0 M) (i0 M) else 0 := by
    intro i
    split_ifs with hi
    · subst hi
      rw [Finset.sum_eq_single (i0 M)]
      · simp [basis0, i0]
      · intro b _ hb
        have : b.val ≠ M := fun heq => hb (Fin.ext heq)
        simp [basis0, this]
      · intro h; exfalso; exact h (Finset.mem_univ _)
    · have : i.val ≠ M := fun heq => hi (Fin.ext heq)
      simp [basis0, this]
  simp_rw [h_inner]
  rw [Finset.sum_ite_eq']
  simp

/-- Rayleigh quotient of A at basis0 equals the diagonal entry A[i0, i0]. -/
theorem rayleigh_basis0 (M : ℕ) (A : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    Q3.RayleighQuotient A (basis0 M) = A (i0 M) (i0 M) := by
  simp only [Q3.RayleighQuotient]
  rw [quadForm_basis0, basis0_norm_sq]
  simp

/-- Rayleigh quotient of (A - B) at basis0 equals A[i0,i0] - B[i0,i0]. -/
theorem rayleigh_basis0_sub (M : ℕ)
    (A B : Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℝ) :
    Q3.RayleighQuotient (A - B) (basis0 M) =
      A (i0 M) (i0 M) - B (i0 M) (i0 M) := by
  rw [rayleigh_basis0]
  simp [Matrix.sub_apply]

end Q3.Proofs.RayleighQId
