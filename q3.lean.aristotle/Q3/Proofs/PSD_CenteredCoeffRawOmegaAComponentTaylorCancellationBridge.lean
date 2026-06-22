import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorRows01234567891011ProductBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Cancellation-form bridge for the Step33A.1-A sub0 component product.

The rows0..11 product assembly budget is Lean-killed because the independent
product-error estimate contains the term
`OmegaTaylorRemainderAbs * ShapeSqDerivNominalAbsBudget`.  This file does not
claim a smaller bound.  It only records the exact algebraic regrouping that a
cancellation-preserving source must bound next.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual (eta : Real) :
    Real :=
  step22OmegaArchWeightDerivClosedForm eta

def primaryFiniteRow0Parent0Split100Sub0OmegaActual (eta : Real) : Real :=
  Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight eta

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActual (eta : Real) :
    Real :=
  (centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta) ^ 2

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff eta

def primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff eta

def primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta

def primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta +
    primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta

def primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta +
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta

def primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
    (eta : Real) : Real :=
  (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta -
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta) *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta +
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta *
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta -
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta) +
    (primaryFiniteRow0Parent0Split100Sub0OmegaActual eta -
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta) *
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta +
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta *
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta -
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta)

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductError_eq_cancellationResidual
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        eta := by
  dsimp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly]
  ring

theorem primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_eq_scale_componentProductActual
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta =
      (((3 : Real) / 10) / Real.pi) *
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta := by
  rw [primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_eq_tightProductActual]
  dsimp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual]

theorem primaryFiniteRow0Parent0Split100Sub0_nominalProduct_eq_componentProductNominal
    (eta : Real) :
    rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff eta *
        rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta +
      rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff eta *
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  rfl

end Step33
end PSDpd
end Q3
