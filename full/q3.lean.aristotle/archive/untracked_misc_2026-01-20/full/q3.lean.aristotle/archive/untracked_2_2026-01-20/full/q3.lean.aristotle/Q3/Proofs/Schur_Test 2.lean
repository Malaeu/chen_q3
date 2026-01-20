/-
Schur Test: Row Sum Bound ⟹ Operator Norm Bound
================================================

This file proves the Schur test using Mathlib's L∞ operator norm definition.

The classical Schur test states that for a symmetric matrix A:
  (∀ i, ∑ j |A i j| ≤ C) → ‖A‖ ≤ C

This follows directly from Matrix.linfty_opNorm_def which defines:
  ‖A‖ = sup_i (∑_j ‖A i j‖)

**Citation:**
- Schur, I. (1911). "Bemerkungen zur Theorie der beschränkten Bilinearformen"
- Horn & Johnson (2012). "Matrix Analysis", Theorem 5.6.9
-/

import Mathlib

open scoped Matrix Matrix.Norms.Operator

namespace Q3.Proofs

/-- Schur test: row sum bound implies operator norm bound.

For a matrix A, if all row sums ∑_j |A i j| ≤ C, then ‖A‖ ≤ C.
This follows directly from the definition of the L∞ operator norm.

**Note:** The symmetry hypothesis is included for compatibility with the
classical Schur test statement, but is not strictly needed for the L∞ norm bound.
-/
theorem Schur_test_proof {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (_hA : A.IsSymm)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ i, ∑ j, |A i j| ≤ C) :
    ‖A‖ ≤ C := by
  rw [Matrix.linfty_opNorm_def]
  have hsup : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ C.toNNReal := by
    apply Finset.sup_le
    intro i _
    rw [← NNReal.coe_le_coe, NNReal.coe_sum]
    simp only [coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal C hC]
    exact h i
  calc (↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) : ℝ)
      ≤ ↑C.toNNReal := by exact_mod_cast hsup
    _ = C := Real.coe_toNNReal C hC

end Q3.Proofs
