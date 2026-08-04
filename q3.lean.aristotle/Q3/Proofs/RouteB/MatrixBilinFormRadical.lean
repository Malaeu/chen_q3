import Q3.Proofs.RouteB.SimpleRadicalSpan
import Mathlib.LinearAlgebra.Matrix.BilinearForm

set_option linter.mathlibStandardSet false

noncomputable section

open Matrix

namespace Q3.RouteB

/-- The left radical of the bilinear form represented by `Q` is the kernel
of multiplication by `Qᵀ`. -/
theorem matrixToBilin_ker_eq_transposeMulVec_ker
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) :
    LinearMap.ker (Matrix.toBilin' Q) =
      LinearMap.ker Q.transpose.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    apply funext
    intro i
    have hi := LinearMap.congr_fun hx (Pi.single i 1)
    simpa only [Matrix.toBilin'_apply', dotProduct_mulVec,
      dotProduct_single, mul_one, ← Matrix.mulVec_transpose] using hi
  · intro hx
    apply LinearMap.ext
    intro y
    have hmul : Q.transpose *ᵥ x = 0 := by
      change Q.transpose *ᵥ x = 0 at hx
      exact hx
    rw [Matrix.toBilin'_apply', dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hmul, zero_dotProduct]
    rfl

/-- For a symmetric matrix, matrix-kernel simplicity identifies the full
left radical of its bilinear form with the named calibration line. -/
theorem matrixBilinForm_ker_eq_span_singleton_of_finrank_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ)
    (xi : n → ℝ)
    (hQ : Q.transpose = Q)
    (hxi : Matrix.mulVec Q xi = 0)
    (hxi0 : xi ≠ 0)
    (hker1 : Module.finrank ℝ (LinearMap.ker Q.mulVecLin) = 1) :
    LinearMap.ker (Matrix.toBilin' Q) = ℝ ∙ xi := by
  have hker : LinearMap.ker (Matrix.toBilin' Q) =
      LinearMap.ker Q.mulVecLin := by
    rw [matrixToBilin_ker_eq_transposeMulVec_ker Q, hQ]
  apply bilinForm_ker_eq_span_singleton_of_finrank_one
  · rw [hker, LinearMap.mem_ker]
    simpa using hxi
  · exact hxi0
  · rw [hker]
    exact hker1

#print axioms matrixToBilin_ker_eq_transposeMulVec_ker
#print axioms matrixBilinForm_ker_eq_span_singleton_of_finrank_one

end Q3.RouteB
