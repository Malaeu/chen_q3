import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Raw second-derivative bridge at the first Step33A.1-A subchunk anchor.

This file does not prove the required raw second-derivative interval.  It
removes one exact algebraic layer from that task: the derivative at zero of the
combined cancellation expression is the true raw second derivative minus the
checked rational derivative of the full Taylor model.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondCoeff
    (i : Fin 15) : Rat :=
  ((i.1 + 1 : Nat) : Rat) *
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff
      ⟨i.1 + 1, by omega⟩

def primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat :
    Rat :=
  ∑ i : Fin 15,
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondCoeff i *
      ((-(1 : Rat) / 20) ^ i.1)

theorem primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat_eq :
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat =
      (15050077640090993308726559634073553 : Rat) /
        8192000000000000000000000000000000 := by
  native_decide

theorem primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff_eq_integratedSecondCoeff :
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff =
      integratedTaylorCoeff 14
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondCoeff
        (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff 0) := by
  funext i
  fin_cases i <;> native_decide

theorem primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondPoly_value_at_zero :
    rawOmegaATaylorPolynomial 14 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondCoeff
        (0 : Real) =
      (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat :
        Real) := by
  unfold rawOmegaATaylorPolynomial
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat
  norm_num only [Nat.reduceAdd, Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [Rat.cast_mul, Rat.cast_pow]

theorem primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodel_deriv_at_zero :
    deriv
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff)
        (0 : Real) =
      (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat :
        Real) := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff_eq_integratedSecondCoeff]
  rw [
    integratedTaylorPolynomial_deriv_eq_base 14 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondCoeff
      (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff 0)
      (0 : Real)]
  exact
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondPoly_value_at_zero

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationIntervalExpr_eq_rawDerivClosedForm_sub_model
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta =
      primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta := by
  calc
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta =
        deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual eta := by
          rw [
            primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_combinedCancellationIntervalExpr]
    _ = primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta := by
          rw [
            primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm]

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationIntervalExpr_deriv_at_zero_eq_raw_second_minus_modelSecond :
    deriv primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
        (0 : Real) =
      deriv
        (fun t : Real =>
          deriv
            (fun eta : Real =>
              Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                11 ((3 : Real) / 10) 0 eta)
            t)
        (0 : Real) -
        (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat :
          Real) := by
  have hfun :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr =
        fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
            rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta := by
    funext eta
    exact
      primaryFiniteRow0Parent0Split100Sub0_combinedCancellationIntervalExpr_eq_rawDerivClosedForm_sub_model
        eta
  rw [hfun]
  change
    deriv
      (primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff)
      (0 : Real) =
      deriv
        (fun t : Real =>
          deriv
            (fun eta : Real =>
              Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                11 ((3 : Real) / 10) 0 eta)
            t)
        (0 : Real) -
        (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelSecondAtZeroRat :
          Real)
  rw [deriv_sub]
  · rw [primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodel_deriv_at_zero]
    have hrawfun :
        primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm =
          fun t : Real =>
            deriv
              (fun eta : Real =>
                Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                  11 ((3 : Real) / 10) 0 eta)
              t := by
      funext t
      rw [primaryFiniteRow0Parent0Split100Sub0_raw_integrand_deriv_eq_closedForm]
    rw [hrawfun]
  · exact
      primaryFiniteRow0Parent0Split100Sub0_raw_integrand_deriv_closedForm_differentiableAt_zero
  · exact
      rawOmegaATaylorPolynomial_differentiableAt 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff
        (0 : Real)

end Step33
end PSDpd
end Q3
