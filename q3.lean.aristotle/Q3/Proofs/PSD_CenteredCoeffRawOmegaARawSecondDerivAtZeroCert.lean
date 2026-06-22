import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport

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
open Step33Sub0OmegaPrimeTaylorRemainderCert
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

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSq_at_zero_eq :
    (fun eta : Real =>
      (centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta) ^ 2)
      (0 : Real) =
      ((269291841030051840000 : Real) /
        (452937348578601132294 : Real)) := by
  dsimp only
  rw [primaryK11ShapeClosedForm_eq_sinc_eta_div_40]
  simp
  simpa [inv_pow] using primaryK11ShapeNormalizer_sq_exact

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSq_second_deriv_at_zero_eq :
    let S : Real -> Real :=
      fun eta : Real =>
        (centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta) ^ 2
    deriv (fun t : Real => deriv S t) (0 : Real) =
      -((269291841030051840000 : Real) /
        (90587469715720226458800 : Real)) := by
  dsimp only
  let D : Real := (Real.sqrt (bsplineScale 11 * bsplineAutocorrNorm 11))⁻¹
  let U : Real -> Real := fun eta : Real => realSinc (eta / 40)
  let F : Real -> Real := fun eta : Real => D ^ 2 * (U eta) ^ 24
  have hSqFun :
      (fun eta : Real =>
        (centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta) ^ 2) =
        F := by
    funext eta
    rw [primaryK11ShapeClosedForm_eq_sinc_eta_div_40]
    simp [F, U, D]
    ring
  rw [hSqFun]
  have hU0 : U (0 : Real) = 1 := by
    simp [U]
  have hUderiv0 : deriv U (0 : Real) = 0 := by
    have hcomp :
        deriv (fun eta : Real => realSinc (eta / 40)) (0 : Real) =
          deriv realSinc (0 / 40) * deriv (fun eta : Real => eta / 40) (0 : Real) := by
      have hsincDiff :
          DifferentiableAt Real realSinc ((fun eta : Real => eta / 40) (0 : Real)) :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.realSinc_differentiableAt _
      have hargDiff : DifferentiableAt Real (fun eta : Real => eta / 40) (0 : Real) := by
        fun_prop
      simpa using deriv_comp (0 : Real) hsincDiff hargDiff
    rw [hcomp]
    rw [show (0 : Real) / 40 = 0 by norm_num]
    rw [show deriv (fun eta : Real => eta / 40) (0 : Real) = (1 / 40 : Real) by
      norm_num]
    rw [deriv_realSinc_zero]
    norm_num
  have hUderivDeriv0 :
      deriv (fun t : Real => deriv U t) (0 : Real) = -(1 / 4800 : Real) := by
    have hDerivUFun :
        (fun t : Real => deriv U t) =
          fun t : Real => deriv realSinc (t / 40) * (1 / 40 : Real) := by
      funext t
      have hsincDiff :
          DifferentiableAt Real realSinc ((fun eta : Real => eta / 40) t) :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.realSinc_differentiableAt _
      have hargDiff : DifferentiableAt Real (fun eta : Real => eta / 40) t := by
        fun_prop
      have hcomp := deriv_comp t hsincDiff hargDiff
      simpa [U] using hcomp
    rw [hDerivUFun]
    rw [deriv_mul_const]
    · rw [show deriv (fun t : Real => deriv realSinc (t / 40)) (0 : Real) =
          deriv (fun x : Real => deriv realSinc x) (0 / 40) *
            deriv (fun t : Real => t / 40) (0 : Real) by
        have hbase :
            DifferentiableAt Real (fun x : Real => deriv realSinc x)
              ((fun t : Real => t / 40) 0) := by
          simpa using deriv_realSinc_differentiableAt_zero
        have harg : DifferentiableAt Real (fun t : Real => t / 40) (0 : Real) := by
          fun_prop
        simpa using deriv_comp (0 : Real) hbase harg]
      rw [show (0 : Real) / 40 = 0 by norm_num]
      rw [show deriv (fun t : Real => t / 40) (0 : Real) = (1 / 40 : Real) by
        norm_num]
      rw [deriv_realSinc_deriv_at_zero]
      norm_num
    · have hbase :
          DifferentiableAt Real (fun x : Real => deriv realSinc x)
            ((fun t : Real => t / 40) 0) := by
        simpa using deriv_realSinc_differentiableAt_zero
      have harg : DifferentiableAt Real (fun t : Real => t / 40) (0 : Real) := by
        fun_prop
      exact hbase.comp (0 : Real) harg
  have hFderivFun :
      (fun t : Real => deriv F t) =
        fun t : Real => D ^ 2 * (24 * (U t) ^ 23 * deriv U t) := by
    funext t
    have hUDiff : DifferentiableAt Real U t := by
      dsimp [U]
      fun_prop
    unfold F
    rw [deriv_const_mul]
    · rw [deriv_fun_pow hUDiff 24]
      ring
    · exact hUDiff.pow 24
  rw [hFderivFun]
  have hInnerDiff1 : DifferentiableAt Real (fun t : Real => (U t) ^ 23) (0 : Real) := by
    have hUDiff : DifferentiableAt Real U (0 : Real) := by
      dsimp [U]
      fun_prop
    exact hUDiff.pow 23
  have hInnerDiff2 : DifferentiableAt Real (fun t : Real => deriv U t) (0 : Real) := by
    have hDerivUFun :
        (fun t : Real => deriv U t) =
          fun t : Real => deriv realSinc (t / 40) * (1 / 40 : Real) := by
      funext t
      have hsincDiff :
          DifferentiableAt Real realSinc ((fun eta : Real => eta / 40) t) :=
        Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.realSinc_differentiableAt _
      have hargDiff : DifferentiableAt Real (fun eta : Real => eta / 40) t := by
        fun_prop
      have hcomp := deriv_comp t hsincDiff hargDiff
      simpa [U] using hcomp
    rw [hDerivUFun]
    have hbase :
        DifferentiableAt Real (fun x : Real => deriv realSinc x)
          ((fun t : Real => t / 40) 0) := by
      simpa using deriv_realSinc_differentiableAt_zero
    have harg : DifferentiableAt Real (fun t : Real => t / 40) (0 : Real) := by
      fun_prop
    exact (hbase.comp (0 : Real) harg).mul (differentiableAt_const (1 / 40 : Real))
  rw [deriv_const_mul]
  · have hprod :
        deriv (fun t : Real => 24 * (U t) ^ 23 * deriv U t) (0 : Real) =
          24 *
            (deriv (fun t : Real => (U t) ^ 23) (0 : Real) * deriv U (0 : Real) +
              (U (0 : Real)) ^ 23 * deriv (fun t : Real => deriv U t) (0 : Real)) := by
      have hconst :
          DifferentiableAt Real (fun t : Real => (24 : Real) * (U t) ^ 23) (0 : Real) := by
        exact (differentiableAt_const (24 : Real)).mul hInnerDiff1
      change
        deriv ((fun t : Real => (24 : Real) * (U t) ^ 23) *
            fun t : Real => deriv U t) (0 : Real) =
          24 *
            (deriv (fun t : Real => (U t) ^ 23) (0 : Real) * deriv U (0 : Real) +
              (U (0 : Real)) ^ 23 * deriv (fun t : Real => deriv U t) (0 : Real))
      rw [deriv_mul hconst hInnerDiff2]
      rw [deriv_const_mul]
      · ring
      · exact hInnerDiff1
    rw [hprod]
    rw [hU0, hUderiv0, hUderivDeriv0]
    rw [primaryK11ShapeNormalizer_sq_exact]
    norm_num
  · have hinner :
        DifferentiableAt Real (fun t : Real => 24 * (U t) ^ 23 * deriv U t)
          (0 : Real) := by
      exact ((differentiableAt_const (24 : Real)).mul hInnerDiff1).mul hInnerDiff2
    exact hinner

theorem primaryFiniteRow0Parent0Split100Sub0_omegaSecondClosedForm_at_zero_interval :
    (32 : Real) <= deriv step22OmegaArchWeightDerivClosedForm (0 : Real) ∧
      deriv step22OmegaArchWeightDerivClosedForm (0 : Real) <= (33 : Real) := by
  have hApprox :
      ‖deriv step22OmegaArchWeightDerivClosedForm (0 : Real) -
          (-1 / 2 : Real) *
            (Finset.range 2).sum
              (fun n : Nat =>
                iteratedDeriv 1
                  (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) (0 : Real))‖ <=
        (1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant 1 (k + 2)) := by
    simpa [iteratedDeriv_one] using
      (omegaPrimeClosedForm_iteratedDeriv_sub_prefix_norm_le_half_shifted_tsum_majorant_of_le16
        1 2 (by norm_num) (0 : Real))
  have hPrefix :
      (-1 / 2 : Real) *
          (Finset.range 2).sum
            (fun n : Nat =>
              iteratedDeriv 1
                (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) (0 : Real)) =
        (4032 / 125 : Real) := by
    norm_num [Finset.sum_range_succ, omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
      omegaPrimeOrder16SeriesBase, Complex.normSq,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hTail :
      (1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant 1 (k + 2)) <=
        (4 / 25 : Real) := by
    have h := omegaPrimeCenterJet_shifted_tsum_budget_le_generated_bound_of_le15
      1 2 (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hNorm :
      ‖deriv step22OmegaArchWeightDerivClosedForm (0 : Real) -
          (4032 / 125 : Real)‖ <= (4 / 25 : Real) := by
    rw [← hPrefix]
    exact hApprox.trans hTail
  have hAbs :
      |deriv step22OmegaArchWeightDerivClosedForm (0 : Real) -
          (4032 / 125 : Real)| <= (4 / 25 : Real) := by
    simpa [Real.norm_eq_abs] using hNorm
  have hBounds := abs_le.mp hAbs
  constructor <;> linarith

theorem primaryFiniteRow0Parent0Split100Sub0_omega_second_deriv_at_zero_interval :
    let Ω : Real -> Real :=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
    (32 : Real) <= deriv (fun t : Real => deriv Ω t) (0 : Real) ∧
      deriv (fun t : Real => deriv Ω t) (0 : Real) <= (33 : Real) := by
  dsimp only
  rw [step22OmegaArchWeight_second_deriv_at_zero_eq_closedForm]
  exact primaryFiniteRow0Parent0Split100Sub0_omegaSecondClosedForm_at_zero_interval

theorem primaryFiniteRow0Parent0Split100Sub0_raw_second_deriv_at_zero_eq_omega_shape_constants :
    let Ω : Real -> Real :=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
    deriv
        (fun t : Real =>
          deriv
            (fun eta : Real =>
              Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22PositiveAxisOmegaAIntegrand
                11 ((3 : Real) / 10) 0 eta)
            t)
        (0 : Real)
      =
      (((3 : Real) / 10) / Real.pi) *
        (deriv (fun t : Real => deriv Ω t) (0 : Real) *
            ((269291841030051840000 : Real) /
              (452937348578601132294 : Real)) +
          Ω (0 : Real) *
            (-((269291841030051840000 : Real) /
              (90587469715720226458800 : Real)))) := by
  rw [primaryFiniteRow0Parent0Split100Sub0_raw_second_deriv_at_zero_decomp]
  dsimp only
  have hS0 :
      centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) (0 : Real) ^ 2 =
        ((269291841030051840000 : Real) /
          (452937348578601132294 : Real)) := by
    simpa using primaryFiniteRow0Parent0Split100Sub0_shapeSq_at_zero_eq
  have hS1 :
      deriv
          (fun eta : Real =>
            centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta ^ 2)
          (0 : Real) = 0 := by
    simpa using primaryFiniteRow0Parent0Split100Sub0_shapeSq_deriv_at_zero
  have hS2 :
      deriv
          (fun t : Real =>
            deriv
              (fun eta : Real =>
                centeredBSplineImagTransformRealClosedForm 11 ((3 : Real) / 10) eta ^ 2)
              t)
          (0 : Real) =
        -((269291841030051840000 : Real) /
          (90587469715720226458800 : Real)) := by
    simpa using primaryFiniteRow0Parent0Split100Sub0_shapeSq_second_deriv_at_zero_eq
  rw [hS0, hS1, hS2]
  ring

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
