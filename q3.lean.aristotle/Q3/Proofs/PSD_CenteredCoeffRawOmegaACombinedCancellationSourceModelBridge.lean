import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Source-model bridge scaffolding for the Step33A.1-A sub0 combined-cancellation
high-order Taylor route.

This file deliberately does not emit generated center-jet rows, order-16 rows,
or a `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid` payload.  It
records the first structural analytic bridge that is currently local: the whole
combined expression is `C^16` once the base Step22 Omega weight is available as
`C^16`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Cauchy-style convolution for normalized center jets.  The payload generator
may use this as the exact shape for component-product jets; it is only a
definition here, not a proof that any generated row is valid. -/
def primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution
    (n : Nat) (a b : Nat -> Real) : Real :=
  (Finset.range (n + 1)).sum (fun k => a k * b (n - k))

/-- The active center for the zero-cell combined-cancellation Taylor bridge. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter : Real :=
  (1 : Real) / 20

/-- Factorial-normalized center jet in the convention consumed by the
degree-15 combined-cancellation Taylor receiver. -/
def primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
    (f : Real -> Real) (n : Nat) : Real :=
  iteratedDeriv n f
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter /
    (Nat.factorial n : Real)

/-- Residual Taylor polynomial as a named source for component-level center
jets. -/
def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta

/-- Cauchy-source center jet for the actual component product.  This is the
generator-facing convention; all-order equality is the later product-Leibniz
obligation. -/
def primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaActual)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual)

/-- Cauchy-source center jet for the nominal polynomial component product. -/
def primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly)

/-- Cauchy-source center jet for the cancellation residual component product. -/
def primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta -
            primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly eta))
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta -
            primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly eta)) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0OmegaActual eta -
            primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly eta))
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual) +
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution n
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly)
      (primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta -
            primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly eta))

/-- Component-source center jet for the full combined-cancellation expression.
For `n = 0` this is Lean-checked below; for all rows this is the exact source
the later product-Leibniz bridge must justify. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
    (n : Nat) : Real :=
  primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly n +
    primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        n +
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) *
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
        n

/-- First exact component Cauchy row for the actual component product. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_centerJet0_eq_cauchy :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual 0 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual]

/-- First exact component Cauchy row for the nominal polynomial component
product. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_centerJet0_eq_cauchy :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal 0 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal]

/-- First exact component Cauchy row for the cancellation-residual component
product. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_centerJet0_eq_cauchy :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        0 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual]

/-- First exact center-jet row of the whole combined-cancellation expression in
the component-source convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet0_eq_componentSource :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
        0 =
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
        0 := by
  simp [
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet,
    primaryFiniteRow0Parent0Split100Sub0NormalizedJetConvolution,
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr,
    primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal]
  ring

/-- Local smoothness helper for the rational Taylor-polynomial surface used by
the combined source model. -/
theorem rawOmegaATaylorPolynomial_contDiff16
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat) :
    ContDiff Real 16 (rawOmegaATaylorPolynomial degree center coeff) := by
  unfold rawOmegaATaylorPolynomial
  fun_prop

/-- The base Step22 Omega weight is `C^16`, obtained from its differentiability
and the existing closed-form derivative smoothness certificate. -/
theorem step22OmegaArchWeight_contDiff16 :
    ContDiff Real 16
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight := by
  rw [show (16 : WithTop ENat) = (15 : WithTop ENat) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  constructor
  · exact fun eta =>
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt eta
  · constructor
    · intro h
      norm_num at h
    · have hDeriv :
          deriv CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight =
            step22OmegaArchWeightDerivClosedForm := by
        funext eta
        exact step22OmegaArchWeight_deriv_eq_closedForm eta
      have hClosed :
          ContDiff Real 15 step22OmegaArchWeightDerivClosedForm :=
        step22OmegaArchWeightDerivClosedForm_contDiff16.of_le (by norm_num)
      rw [hDeriv]
      exact hClosed

/--
The whole combined-cancellation expression is `C^16` once the base
`step22OmegaArchWeight` source is available as `C^16`.

This closes only the structural smoothness sub-obligation of
`Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid`; it does not provide
the center-jet rows or the uniform order-16 bound.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16_of_omega
    (hOmega :
      ContDiff Real 16
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight) :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr := by
  change
    ContDiff Real 16
      (fun eta : Real =>
        rawOmegaATaylorPolynomial
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta +
          primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs eta)
  simp only [
    primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs,
    primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual,
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly]
  have hResidualPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
  have hOmegaPrimePoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
  have hOmegaPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
  have hShapeSqPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff
  have hShapeSqDerivPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff
  have hOmegaPrime :
      ContDiff Real 16 step22OmegaArchWeightDerivClosedForm :=
    step22OmegaArchWeightDerivClosedForm_contDiff16
  have hShapeSqDeriv :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10))
  fun_prop

/--
Unconditional structural smoothness bridge for the whole combined-cancellation
expression. This still does not provide the center-jet rows or uniform order-16
bound required for a concrete `Valid` payload.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16 :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr :=
  primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16_of_omega
    step22OmegaArchWeight_contDiff16

end Step33
end PSDpd
end Q3
