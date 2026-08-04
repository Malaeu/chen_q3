import Q3.Proofs.RouteB.RankOneCorrectionQuotientCharpoly
import Q3.Proofs.RouteB.RankOneCorrectionQuotientCharpolyTransport

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

/-- The source Lagrange polynomial is the signed characteristic polynomial of
the rank-one correction induced on the full bilinear-radical quotient. -/
theorem sourceLagrangePolynomial_eq_signed_radical_quotient_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (T : Matrix n n ℝ)
    (lam xi beta : n → ℝ)
    (hT : T.transpose = T)
    (hcomm :
      T * Matrix.diagonal lam - Matrix.diagonal lam * T =
        - Matrix.vecMulVec beta (1 : n → ℝ) +
          Matrix.vecMulVec (1 : n → ℝ) beta)
    (hTDxi :
      Matrix.mulVec T (Matrix.mulVec (Matrix.diagonal lam) xi) = -beta)
    (hnormalized : (1 : n → ℝ) ⬝ᵥ xi = 1)
    (hTxi : Matrix.mulVec T xi = 0)
    (hker1 : Module.finrank ℝ (LinearMap.ker T.mulVecLin) = 1) :
    sourceLagrangePolynomial lam xi =
      -(Polynomial.C ((-1 : ℝ) ^ Fintype.card n) *
        (quotientByRadicalEnd (Matrix.toBilin' T)
          (rankOneCorrection
            (Matrix.diagonal lam) xi (1 : n → ℝ)).mulVecLin
          (rankOneCorrection_isSelfAdjoint_toBilin
            T (Matrix.diagonal lam) xi beta (1 : n → ℝ)
            hT (by simp) hcomm hTDxi)).charpoly) := by
  have hsource :=
    sourceLagrangePolynomial_eq_signed_quotient_charpoly
      lam xi hnormalized
  have htransport :=
    rankOneCorrectionQuotientEnd_charpoly_eq_quotientByRadicalEnd_charpoly
      T (Matrix.diagonal lam) xi beta (1 : n → ℝ)
      hT (by simp) hcomm hTDxi hnormalized hTxi hker1
  rw [htransport] at hsource
  simpa using hsource

#print axioms sourceLagrangePolynomial_eq_signed_radical_quotient_charpoly

end Q3.RouteB
