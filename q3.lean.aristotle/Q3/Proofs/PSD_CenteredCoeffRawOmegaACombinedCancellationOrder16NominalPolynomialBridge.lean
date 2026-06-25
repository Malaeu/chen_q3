import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Nominal polynomial bridge for the Step33A.1-A direct scaled-remainder target.

This file extracts the rational nominal polynomial part of the collapsed direct
target.  It is only an algebraic coefficient crosswalk:

`collapsedExpression = activeScale * D^16(ComponentProductActual)
  - nominalOrder16Poly`.

It emits no Horner rows, no interval rows, no whole-expression remainder
certificate, and no Step33A.1-A closure claim.  In particular, it must not be
used to spend separate `actual` and `nominal` budgets.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- Rational degree-29 coefficients obtained by differentiating the nominal
degree-45 assembled product polynomial sixteen times. -/
def primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff
    (j : Fin 30) : Rat :=
  ((16 + j.1).descFactorial 16 : Rat) *
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff
      ⟨16 + j.1, by
        unfold primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        omega⟩

/-- The rational nominal order-16 polynomial in the repository's centered
Taylor convention. -/
def primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff eta

theorem primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Coeff_eq_nonzeroModelCoeff
    (j : Fin 30) :
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff j =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff j := by
  unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff
  unfold primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff
  unfold primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf
  unfold primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded
  have hnot : ¬ (16 + j.1 < 16) := by omega
  simp [hnot]

theorem primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_eq_nonzeroModelPoly
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
  unfold rawOmegaATaylorPolynomial
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Coeff_eq_nonzeroModelCoeff]

private theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff16_nominalBridge :
    ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal := by
  have hOmegaPrimePoly :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
  have hOmegaPoly :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
  have hShapeSqPoly :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff
  have hShapeSqDerivPoly :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
  exact
    (hOmegaPrimePoly.mul hShapeSqPoly).add
      (hOmegaPoly.mul hShapeSqDerivPoly)

theorem primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_eq
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta =
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
        iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  have hShift :
      iteratedDeriv 16
          (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff) eta =
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta := by
    unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
    exact
      primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolynomial_deriv16_eq_shifted29_public
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta
  have hAssembledFun :
      (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff) =
        fun eta : Real =>
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
    funext eta
    change
      rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta =
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta
    rw [primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct]
    rw [primaryFiniteRow0Parent0Split100Sub0_nominalProduct_eq_componentProductNominal]
  have hNominal :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff16_nominalBridge
  calc
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta =
        iteratedDeriv 16
          (rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff) eta :=
      hShift.symm
    _ = iteratedDeriv 16
        (fun eta : Real =>
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta)
        eta := by
          rw [hAssembledFun]
    _ = (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
        iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
          rw [iteratedDeriv_const_mul hNominal.contDiffAt]

/-- The collapsed direct target is the active actual derivative minus the
rational nominal order-16 polynomial.  This is a coefficient bridge only; the
future row generator still has to prove a single whole-expression remainder
bound for `CollapsedExpression`. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
        eta =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta := by
  rw [primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_eq]
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
  ring

end Step33
end PSDpd
end Q3
