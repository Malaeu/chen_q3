import Q3.Proofs.RouteB.RankOneCorrectionQuotientIntertwining
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- An exact intertwining across a linear equivalence identifies the two
characteristic polynomials. -/
theorem charpoly_eq_of_linearEquiv_intertwining
    {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (e : V ≃ₗ[ℝ] W) (A : Module.End ℝ V) (B : Module.End ℝ W)
    (hinter : e.toLinearMap.comp A = B.comp e.toLinearMap) :
    B.charpoly = A.charpoly := by
  have hconj : e.conj A = B := by
    apply LinearMap.ext
    intro y
    have hy := LinearMap.congr_fun hinter (e.symm y)
    simpa [LinearEquiv.conj_apply] using hy
  rw [← hconj]
  exact e.charpoly_conj A

/-- The characteristic polynomial of the rank-one correction on the
calibration-line quotient is the characteristic polynomial of the same
ambient correction on the full bilinear-radical quotient. -/
theorem rankOneCorrectionQuotientEnd_charpoly_eq_quotientByRadicalEnd_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (T D : Matrix n n ℝ)
    (xi beta eta : n → ℝ)
    (hT : T.transpose = T)
    (hD : D.transpose = D)
    (hcomm :
      T * D - D * T =
        - Matrix.vecMulVec beta eta + Matrix.vecMulVec eta beta)
    (hTDxi : Matrix.mulVec T (Matrix.mulVec D xi) = -beta)
    (hnormalized : eta ⬝ᵥ xi = 1)
    (hTxi : Matrix.mulVec T xi = 0)
    (hker1 : Module.finrank ℝ (LinearMap.ker T.mulVecLin) = 1) :
    (rankOneCorrectionQuotientEnd D xi eta hnormalized).charpoly =
      (quotientByRadicalEnd (Matrix.toBilin' T)
        (rankOneCorrection D xi eta).mulVecLin
        (rankOneCorrection_isSelfAdjoint_toBilin
          T D xi beta eta hT hD hcomm hTDxi)).charpoly := by
  have hxi0 : xi ≠ 0 := by
    intro hxi
    subst xi
    simp at hnormalized
  exact charpoly_eq_of_linearEquiv_intertwining
    (matrixBilinRadicalQuotEquivSpan T xi hT hTxi hxi0 hker1)
    (quotientByRadicalEnd (Matrix.toBilin' T)
      (rankOneCorrection D xi eta).mulVecLin
      (rankOneCorrection_isSelfAdjoint_toBilin
        T D xi beta eta hT hD hcomm hTDxi))
    (rankOneCorrectionQuotientEnd D xi eta hnormalized)
    (matrixBilinRadicalQuotEquivSpan_intertwines_rankOneCorrection
      T D xi beta eta hT hD hcomm hTDxi hnormalized hTxi hxi0 hker1)

#print axioms charpoly_eq_of_linearEquiv_intertwining
#print axioms rankOneCorrectionQuotientEnd_charpoly_eq_quotientByRadicalEnd_charpoly

end Q3.RouteB
