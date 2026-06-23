import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Cancellation-preserving normal-form support for the Step33A.1-A
combined-cancellation source rows.

This file does not emit source intervals and does not instantiate
`Step33Sub0CombinedCancellationSourceIntervalCert.Valid`.  It records the
Lean-checked algebra that is available before the remaining coefficient
alignment bridge:

* the cancellation-residual Cauchy source equals actual minus nominal in the
  repository's factorial-normalized center-jet convention;
* once the residual Taylor center jet is aligned with the same convention, the
  combined source reduces to active actual product minus the residual model row.

The missing nonconditional bridge is the coefficient extraction theorem from
`rawOmegaATaylorPolynomial` coefficients to normalized center jets.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- The actual component product is smooth to every row currently consumed by
the 16-row source interval target. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff_low
    (j : Fin 16) :
    ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ComponentProductActual := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hOmegaPrime :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16.of_le hj16
  have hOmega :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16.of_le hj16
  have hShapeSq :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hShapeSqDeriv :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)).of_le hj16
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
  exact (hOmegaPrime.mul hShapeSq).add (hOmega.mul hShapeSqDeriv)

/-- The nominal Taylor-polynomial component product is smooth to every row
currently consumed by the 16-row source interval target. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff_low
    (j : Fin 16) :
    ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hOmegaPrimePoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff).of_le hj16
  have hOmegaPoly :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff).of_le hj16
  have hShapeSqPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff).of_le hj16
  have hShapeSqDerivPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff).of_le hj16
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
  exact
    (hOmegaPrimePoly.mul hShapeSqPoly).add
      (hOmegaPoly.mul hShapeSqDerivPoly)

/-- Cancellation-residual Cauchy rows are actual product rows minus nominal
product rows in the same normalized center-jet convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
          j.1 -
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
          j.1 := by
  rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_centerJet_eq_cauchy j]
  rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductActual_centerJet_eq_cauchy j]
  rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_centerJet_eq_cauchy j]
  have hFun :
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual =
        fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
    funext eta
    rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductError_eq_cancellationResidual eta]
  rw [hFun]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_sub
    j.1
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
    (primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff_low j)
    (primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff_low j)]

/--
Conditional center-jet normal form for the combined source.

The hypothesis is exactly the remaining coefficient-alignment bridge:
`ResidualTaylorPoly` must expose the low rows as
`nominalScale * nominalProductCauchy - residualModelCoeff` in the same
factorial-normalized center-jet convention.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model_of_residualJet
    (j : Fin 16)
    (hResidualJet :
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly j.1 =
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
            j.1 -
          (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
            Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 -
        (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
          Real) := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
  rw [hResidualJet]
  rw [primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal j]
  ring

end Step33
end PSDpd
end Q3
