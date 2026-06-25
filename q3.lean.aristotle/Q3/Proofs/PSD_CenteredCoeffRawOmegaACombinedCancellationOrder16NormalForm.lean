import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectModelPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Order-16 normal form for the Step33A.1-A sub0 combined-cancellation source.

This file does not provide a numerical bound. It records the exact bridge from
the assembled order-16 source to the 17th derivative of the single raw product
`OmegaActual * ShapeSqActual`, so the next certificate can bound the true
cancellation-preserving expression instead of separated absolute rows.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0RawProductActual (eta : Real) :
    Real :=
  primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta

def primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant
    (omegaAbs shapeSqAbs : Nat -> Real) : Real :=
  ∑ i ∈ Finset.range (17 + 1),
    (Nat.choose 17 i : Real) * omegaAbs i * shapeSqAbs (17 - i)

def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
    (k : Nat) : Real :=
  if _hk : k < 18 then
    if _hk16 : k <= 16 then
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant k
    else
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant 16
  else
    0

def primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17
    (k : Nat) : Real :=
  if _hk : k < 18 then
    if _hk16 : k <= 16 then
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant k
    else
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
        16
  else
    0

private theorem primaryFiniteRow0Parent0Split100Sub0_center_mem_normalForm :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter ∈
      Set.Icc (0 : Real) ((1 : Real) / 10) := by
  norm_num [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter]

private theorem step22OmegaArchWeight_contDiff17_normalForm :
    ContDiff Real 17
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight := by
  rw [show (17 : WithTop ENat) = (16 : WithTop ENat) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  constructor
  · exact fun eta =>
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt
        eta
  · constructor
    · intro h
      norm_num at h
    · have hDeriv :
          deriv Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight =
            step22OmegaArchWeightDerivClosedForm := by
        funext eta
        exact step22OmegaArchWeight_deriv_eq_closedForm eta
      rw [hDeriv]
      exact step22OmegaArchWeightDerivClosedForm_contDiff16

private theorem primaryFiniteRow0Parent0Split100Sub0RawProductActual_contDiff17 :
    ContDiff Real 17 primaryFiniteRow0Parent0Split100Sub0RawProductActual := by
  have hOmega :
      ContDiff Real 17 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff17_normalForm
  have hShape :
      ContDiff Real 17 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  simpa [primaryFiniteRow0Parent0Split100Sub0RawProductActual] using
    hOmega.mul hShape

private theorem
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17_nonneg
    (k : Nat) (hk : k <= 17) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17 k := by
  have hk18 : k < 18 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
  simp [hk18]
  by_cases hk16 : k <= 16
  · simp [hk16]
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
        primaryFiniteRow0Parent0Split100Sub0_center_mem_normalForm k hk16
    exact (norm_nonneg _).trans h
  · have hk_eq : k = 17 := by omega
    simp [hk_eq]
    have h :=
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
        primaryFiniteRow0Parent0Split100Sub0_center_mem_normalForm 16
        (by norm_num)
    exact (norm_nonneg _).trans h

theorem primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs17
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 17) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17 k := by
  have hk18 : k < 18 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
  simp [hk18]
  by_cases hk16 : k <= 16
  · simp [hk16]
    exact
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
        eta heta k hk16
  · have hk_eq : k = 17 := by omega
    simp [hk_eq]
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv_succ_eq_omegaPrime
        16 eta
    have hBase :=
      primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
        eta heta 16 (by norm_num)
    rw [show 17 = 16 + 1 by norm_num, hShift]
    exact hBase

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs17
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 17) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17
        k := by
  have hk18 : k < 18 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17
  simp [hk18]
  by_cases hk16 : k <= 16
  · simp [hk16]
    exact
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_centeredTaylor
        eta heta k hk16
  · have hk_eq : k = 17 := by omega
    simp [hk_eq]
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ
        16 eta
    have hBase :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_centeredTaylor
        eta heta 16 (by norm_num)
    change
      ‖iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
          16 at hBase
    rw [hShift] at hBase
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqActual] using hBase

private theorem primaryFiniteRow0Parent0Split100Sub0_product_order17_abs_of_factor_bounds
    {f g : Real -> Real} {fAbs gAbs : Nat -> Real} {eta : Real}
    (hf : ContDiff Real 17 f)
    (hg : ContDiff Real 17 g)
    (hfAbsNonneg : ∀ k : Nat, k <= 17 -> 0 <= fAbs k)
    (hfAbs :
      ∀ k : Nat, k <= 17 -> ‖iteratedDeriv k f eta‖ <= fAbs k)
    (hgAbs :
      ∀ k : Nat, k <= 17 -> ‖iteratedDeriv k g eta‖ <= gAbs k) :
    ‖iteratedDeriv 17 (fun t : Real => f t * g t) eta‖ <=
      ∑ i ∈ Finset.range (17 + 1),
        (Nat.choose 17 i : Real) * fAbs i * gAbs (17 - i) := by
  have hmulF :
      ‖iteratedFDeriv Real 17 (fun y : Real => f y * g y) eta‖ <=
        ∑ i ∈ Finset.range (17 + 1),
          (Nat.choose 17 i : Real) *
            ‖iteratedFDeriv Real i f eta‖ *
            ‖iteratedFDeriv Real (17 - i) g eta‖ := by
    exact norm_iteratedFDeriv_mul_le
      (𝕜 := Real) (f := f) (g := g) hf hg eta (n := 17) (by simp)
  have hmulD :
      ‖iteratedDeriv 17 (fun y : Real => f y * g y) eta‖ <=
        ∑ i ∈ Finset.range (17 + 1),
          (Nat.choose 17 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (17 - i) g eta‖ := by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hmulF
  have hsum :
      (∑ i ∈ Finset.range (17 + 1),
          (Nat.choose 17 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (17 - i) g eta‖) <=
        ∑ i ∈ Finset.range (17 + 1),
          (Nat.choose 17 i : Real) * fAbs i * gAbs (17 - i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i <= 17 :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hni_le : 17 - i <= 17 := Nat.sub_le 17 i
    have hchoose_nonneg : 0 <= (Nat.choose 17 i : Real) := by positivity
    have hprod :
        ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (17 - i) g eta‖ <=
          fAbs i * gAbs (17 - i) := by
      exact mul_le_mul
        (hfAbs i hi_le)
        (hgAbs (17 - i) hni_le)
        (norm_nonneg _)
        (hfAbsNonneg i hi_le)
    calc
      (Nat.choose 17 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (17 - i) g eta‖ =
          (Nat.choose 17 i : Real) *
            (‖iteratedDeriv i f eta‖ *
              ‖iteratedDeriv (17 - i) g eta‖) := by ring
      _ <= (Nat.choose 17 i : Real) * (fAbs i * gAbs (17 - i)) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nonneg
      _ = (Nat.choose 17 i : Real) * fAbs i * gAbs (17 - i) := by ring
  exact le_trans hmulD hsum

theorem primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_factor_derivative_abs
    {omegaAbs shapeSqAbs : Nat -> Real}
    (hOmegaAbsNonneg :
      ∀ k : Nat, k <= 17 -> 0 <= omegaAbs k)
    (hOmegaAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 17 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual
              eta‖ <= omegaAbs k)
    (hShapeSqAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 17 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              eta‖ <= shapeSqAbs k) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant
          omegaAbs shapeSqAbs := by
  intro eta hEta
  exact
    primaryFiniteRow0Parent0Split100Sub0_product_order17_abs_of_factor_bounds
      (f := primaryFiniteRow0Parent0Split100Sub0OmegaActual)
      (g := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
      (fAbs := omegaAbs)
      (gAbs := shapeSqAbs)
      (eta := eta)
      (by
        simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
          step22OmegaArchWeight_contDiff17_normalForm)
      (by
        unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
        fun_prop)
      hOmegaAbsNonneg
      (fun k hk => hOmegaAbs eta hEta k hk)
      (fun k hk => hShapeSqAbs eta hEta k hk)

theorem primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_centeredTaylor17 :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant
          primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17 := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_factor_derivative_abs
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs17
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs17

private theorem iteratedDeriv_deriv_eq_succ
    (n : Nat) (f : Real -> Real) (eta : Real) :
    iteratedDeriv n (fun x : Real => deriv f x) eta =
      iteratedDeriv (n + 1) f eta := by
  induction n generalizing eta with
  | zero =>
      rw [iteratedDeriv_succ]
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv n (fun x : Real => deriv f x) =
            iteratedDeriv (n + 1) f := by
        funext x
        exact ih x
      rw [hfun]
      rw [← iteratedDeriv_succ]

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_eq_rawProductDeriv
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
      deriv primaryFiniteRow0Parent0Split100Sub0RawProductActual eta := by
  have hOmegaDiff :
      DifferentiableAt Real
        primaryFiniteRow0Parent0Split100Sub0OmegaActual eta := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt
        eta
  have hShapeDiff :
      DifferentiableAt Real
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0ShapeSqActual]
    exact
      (Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.centeredBSplineImagTransformRealClosedForm_differentiableAt
        11 ((3 : Real) / 10) eta).pow 2
  have hOmegaDeriv :
      deriv primaryFiniteRow0Parent0Split100Sub0OmegaActual eta =
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta := by
    change
      deriv Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight
          eta =
        step22OmegaArchWeightDerivClosedForm eta
    exact step22OmegaArchWeight_deriv_eq_closedForm eta
  have hShapeDeriv :
      deriv primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta =
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta := by
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ
        0 eta
    simpa [
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      iteratedDeriv_succ] using hShift.symm
  have hProd :
      deriv primaryFiniteRow0Parent0Split100Sub0RawProductActual eta =
        deriv primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
            primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta +
          primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
            deriv primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta := by
    simpa [primaryFiniteRow0Parent0Split100Sub0RawProductActual] using
      deriv_mul hOmegaDiff hShapeDiff
  rw [hProd, hOmegaDeriv, hShapeDeriv]
  rfl

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_rawProduct17
    (eta : Real) :
    iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
      iteratedDeriv 17
        primaryFiniteRow0Parent0Split100Sub0RawProductActual eta := by
  have hfun :
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActual =
        fun x : Real =>
          deriv primaryFiniteRow0Parent0Split100Sub0RawProductActual x := by
    funext x
    exact
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_eq_rawProductDeriv
        x
  rw [hfun]
  simpa using
    iteratedDeriv_deriv_eq_succ 16
      primaryFiniteRow0Parent0Split100Sub0RawProductActual eta

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_rawProduct17
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
        eta =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0RawProductActual eta := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual,
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_rawProduct17]

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_rawProduct17_abs
    (raw17Abs : Real)
    (hRaw17 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ <=
          raw17Abs)
    (hBudget :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| * raw17Abs <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp := by
  apply
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_rawProduct17]
  calc
    ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ =
        |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| *
          ‖iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ := by
          rw [norm_mul, Real.norm_eq_abs]
    _ <=
        |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| * raw17Abs :=
          mul_le_mul_of_nonneg_left (hRaw17 eta hEta)
            (abs_nonneg primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff)
    _ <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real) := hBudget

theorem
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_centeredTaylor_rawProduct17_budget
    (hBudget :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| *
          primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant
            primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
            primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17 <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs :
          Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_rawProduct17_abs
      (primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17)
      primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_centeredTaylor17
      hBudget

end Step33
end PSDpd
end Q3
