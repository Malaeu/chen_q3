import Q3.Proofs.RouteB.ProlateSourceCommutation

open Complex Filter MeasureTheory Metric Set
open scoped ContDiff ENat Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The finite Fourier action preserves every pointwise eigenspace of the
prolate differential expression whose eigenrelation holds on the source
interval.  This is a conditional transport theorem only: it neither constructs
nor selects any source prolate mode. -/
theorem finiteFourierAction_preserves_prolateWaveEigenrelation
    (lambda theta : ℝ) (hlambda : 0 < lambda)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 2 φ)
    (heigen : ∀ y ∈ Icc (-lambda) lambda,
      prolateWaveExpression lambda φ y = (theta : ℂ) * φ y) :
    ∀ x : ℝ,
      prolateWaveExpression lambda (finiteFourierAction lambda φ) x =
        (theta : ℂ) * finiteFourierAction lambda φ x := by
  intro x
  rw [finiteFourierAction_intertwines_prolateWaveExpression
    lambda hlambda φ hφ x]
  unfold finiteFourierAction
  calc
    (∫ y in Icc (-lambda) lambda,
        finiteFourierKernel x y * prolateWaveExpression lambda φ y) =
        ∫ y in Icc (-lambda) lambda,
          (theta : ℂ) * (finiteFourierKernel x y * φ y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      rw [heigen y hy]
      ring
    _ = (theta : ℂ) *
        ∫ y in Icc (-lambda) lambda,
          finiteFourierKernel x y * φ y := by
      rw [integral_const_mul]

#print axioms finiteFourierAction_preserves_prolateWaveEigenrelation

end Q3.RouteB.D0Pstar
