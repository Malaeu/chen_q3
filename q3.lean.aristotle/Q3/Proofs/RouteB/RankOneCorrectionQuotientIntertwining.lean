import Q3.Proofs.RouteB.MatrixBilinRadicalQuotientEquiv
import Q3.Proofs.RouteB.RankOneCorrectionBilinSelfAdjoint
import Q3.Proofs.RouteB.RankOneCorrectionQuotientDescent
import Q3.Proofs.RouteB.QuotientByRadicalSelfAdjoint

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- The canonical equivalence from the full-radical quotient to the
calibration-line quotient intertwines the two endomorphisms induced by the
same rank-one corrected ambient map. -/
theorem matrixBilinRadicalQuotEquivSpan_intertwines_rankOneCorrection
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
    (hxi0 : xi ≠ 0)
    (hker1 : Module.finrank ℝ (LinearMap.ker T.mulVecLin) = 1) :
    (matrixBilinRadicalQuotEquivSpan T xi hT hTxi hxi0 hker1).toLinearMap.comp
        (quotientByRadicalEnd (Matrix.toBilin' T)
          (rankOneCorrection D xi eta).mulVecLin
          (rankOneCorrection_isSelfAdjoint_toBilin
            T D xi beta eta hT hD hcomm hTDxi)) =
      (rankOneCorrectionQuotientEnd D xi eta hnormalized).comp
        (matrixBilinRadicalQuotEquivSpan
          T xi hT hTxi hxi0 hker1).toLinearMap := by
  apply LinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on
    (LinearMap.ker (Matrix.toBilin' T)) q ?_
  intro x
  simp

#print axioms matrixBilinRadicalQuotEquivSpan_intertwines_rankOneCorrection

end Q3.RouteB
