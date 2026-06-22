import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorTightProductSource

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Raw closed-form bridge for the nonfinal Step33A.1-A component product source.

This file connects the checked product-source expression to the named raw
integrand derivative closed form.  It still does not identify the nominal
Taylor product with the padded degree-45 assembled polynomial.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

theorem primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_eq_tightProductActual
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta =
      (((3 : Real) / 10) / Real.pi) *
        (step22OmegaArchWeightDerivClosedForm eta *
            (centeredBSplineImagTransformRealClosedForm 11
              ((3 : Real) / 10) eta) ^ 2 +
          Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta) := by
  unfold primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
  rw [deriv_centeredBSplineImagTransformRealClosedForm_sq]
  rw [centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm]

theorem primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightProductSource
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    |primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff eta *
              rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta +
            rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff eta *
              rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
                primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta)| <=
      primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
  have h :=
    primaryFiniteRow0Parent0Split100Sub0_tight_component_product_source hEta
  rw [primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_eq_tightProductActual]
  exact h

end Step33
end PSDpd
end Q3
