import Q3.Proofs.RouteB.MatrixBilinFormRadical
import Mathlib.LinearAlgebra.Quotient.Defs

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- The equality between the full bilinear radical and the calibration line
induces the canonical equivalence of their quotient carriers. -/
noncomputable def matrixBilinRadicalQuotEquivSpan
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ)
    (xi : n → ℝ)
    (hQ : Q.transpose = Q)
    (hxi : Matrix.mulVec Q xi = 0)
    (hxi0 : xi ≠ 0)
    (hker1 : Module.finrank ℝ (LinearMap.ker Q.mulVecLin) = 1) :
    ((n → ℝ) ⧸ LinearMap.ker (Matrix.toBilin' Q)) ≃ₗ[ℝ]
      ((n → ℝ) ⧸ ℝ ∙ xi) :=
  Submodule.quotEquivOfEq
    (LinearMap.ker (Matrix.toBilin' Q)) (ℝ ∙ xi)
    (matrixBilinForm_ker_eq_span_singleton_of_finrank_one
      Q xi hQ hxi hxi0 hker1)

/-- The canonical quotient equivalence preserves every ambient
representative. -/
@[simp] theorem matrixBilinRadicalQuotEquivSpan_mk
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ)
    (xi x : n → ℝ)
    (hQ : Q.transpose = Q)
    (hxi : Matrix.mulVec Q xi = 0)
    (hxi0 : xi ≠ 0)
    (hker1 : Module.finrank ℝ (LinearMap.ker Q.mulVecLin) = 1) :
    matrixBilinRadicalQuotEquivSpan Q xi hQ hxi hxi0 hker1
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : (n → ℝ) ⧸ ℝ ∙ xi) := by
  exact Submodule.quotEquivOfEq_mk
    (LinearMap.ker (Matrix.toBilin' Q)) (ℝ ∙ xi)
    (matrixBilinForm_ker_eq_span_singleton_of_finrank_one
      Q xi hQ hxi hxi0 hker1) x

#print axioms matrixBilinRadicalQuotEquivSpan_mk

end Q3.RouteB
