import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorMajorant

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Order-16 factor-derivative receiver for the Step33A.1-A sub0 combined source.

This file is a proof interface only.  It does not provide the numerical factor
derivative bounds; it proves that once those four proof-grade factor bounds are
available in the active actual-product normalization, they feed the checked
order-16 component-source bridge.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Leibniz majorant for the order-16 derivative of the active actual product. -/
def primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
    (omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs : Nat -> Real) :
    Real :=
  (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Real) * omegaPrimeAbs i * shapeSqAbs (16 - i)) +
    (∑ i ∈ Finset.range (16 + 1),
      (Nat.choose 16 i : Real) * omegaAbs i * shapeSqDerivAbs (16 - i))

private theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff16_receiver :
    ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductActual := by
  have hOmegaPrime :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16
  have hOmega :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16
  have hShapeSq :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hShapeSqDeriv :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
  exact (hOmegaPrime.mul hShapeSq).add (hOmega.mul hShapeSqDeriv)

private theorem primaryFiniteRow0Parent0Split100Sub0_product_order16_abs_of_factor_bounds
    {f g : Real -> Real} {fAbs gAbs : Nat -> Real} {eta : Real}
    (hf : ContDiff Real 16 f)
    (hg : ContDiff Real 16 g)
    (hfAbsNonneg : ∀ k : Nat, k <= 16 -> 0 <= fAbs k)
    (hfAbs :
      ∀ k : Nat, k <= 16 -> ‖iteratedDeriv k f eta‖ <= fAbs k)
    (hgAbs :
      ∀ k : Nat, k <= 16 -> ‖iteratedDeriv k g eta‖ <= gAbs k) :
    ‖iteratedDeriv 16 (fun t : Real => f t * g t) eta‖ <=
      ∑ i ∈ Finset.range (16 + 1),
        (Nat.choose 16 i : Real) * fAbs i * gAbs (16 - i) := by
  have hmulF :
      ‖iteratedFDeriv Real 16 (fun y : Real => f y * g y) eta‖ <=
        ∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) *
            ‖iteratedFDeriv Real i f eta‖ *
            ‖iteratedFDeriv Real (16 - i) g eta‖ := by
    exact norm_iteratedFDeriv_mul_le
      (𝕜 := Real) (f := f) (g := g) hf hg eta (n := 16) (by simp)
  have hmulD :
      ‖iteratedDeriv 16 (fun y : Real => f y * g y) eta‖ <=
        ∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (16 - i) g eta‖ := by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hmulF
  have hsum :
      (∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (16 - i) g eta‖) <=
        ∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) * fAbs i * gAbs (16 - i) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i <= 16 :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hni_le : 16 - i <= 16 := Nat.sub_le 16 i
    have hchoose_nonneg : 0 <= (Nat.choose 16 i : Real) := by positivity
    have hprod :
        ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (16 - i) g eta‖ <=
          fAbs i * gAbs (16 - i) := by
      exact mul_le_mul
        (hfAbs i hi_le)
        (hgAbs (16 - i) hni_le)
        (norm_nonneg _)
        (hfAbsNonneg i hi_le)
    calc
      (Nat.choose 16 i : Real) *
            ‖iteratedDeriv i f eta‖ *
            ‖iteratedDeriv (16 - i) g eta‖ =
          (Nat.choose 16 i : Real) *
            (‖iteratedDeriv i f eta‖ *
              ‖iteratedDeriv (16 - i) g eta‖) := by ring
      _ <= (Nat.choose 16 i : Real) * (fAbs i * gAbs (16 - i)) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nonneg
      _ = (Nat.choose 16 i : Real) * fAbs i * gAbs (16 - i) := by ring
  exact le_trans hmulD hsum

/--
Receiver from proof-grade factor derivative bounds to a proof-grade order-16
bound for the active actual component product.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_factor_derivative_abs
    {omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs : Nat -> Real}
    (hOmegaPrimeAbsNonneg :
      ∀ k : Nat, k <= 16 -> 0 <= omegaPrimeAbs k)
    (hOmegaAbsNonneg :
      ∀ k : Nat, k <= 16 -> 0 <= omegaAbs k)
    (hOmegaPrimeAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
              eta‖ <= omegaPrimeAbs k)
    (hOmegaAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual
              eta‖ <= omegaAbs k)
    (hShapeSqAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              eta‖ <= shapeSqAbs k)
    (hShapeSqDerivAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
              eta‖ <= shapeSqDerivAbs k) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
          omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs := by
  intro eta hEta
  let omegaPrime :=
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
  let omega :=
    primaryFiniteRow0Parent0Split100Sub0OmegaActual
  let shapeSq :=
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  let shapeSqDeriv :=
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
  have hOmegaPrimeCont :
      ContDiff Real 16 omegaPrime := by
    simpa [omegaPrime, primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual]
      using step22OmegaArchWeightDerivClosedForm_contDiff16
  have hOmegaCont :
      ContDiff Real 16 omega := by
    simpa [omega, primaryFiniteRow0Parent0Split100Sub0OmegaActual]
      using step22OmegaArchWeight_contDiff16
  have hShapeSqCont :
      ContDiff Real 16 shapeSq := by
    have hShapeSq :
        ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
      unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
      fun_prop
    simpa [shapeSq] using hShapeSq
  have hShapeSqDerivCont :
      ContDiff Real 16 shapeSqDeriv := by
    simpa [shapeSqDeriv,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)
  have hProd1 :
      ‖iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta‖ <=
        ∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) * omegaPrimeAbs i * shapeSqAbs (16 - i) :=
    primaryFiniteRow0Parent0Split100Sub0_product_order16_abs_of_factor_bounds
      hOmegaPrimeCont hShapeSqCont hOmegaPrimeAbsNonneg
      (fun k hk => by
        simpa [omegaPrime] using hOmegaPrimeAbs eta hEta k hk)
      (fun k hk => by
        simpa [shapeSq] using hShapeSqAbs eta hEta k hk)
  have hProd2 :
      ‖iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta‖ <=
        ∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) * omegaAbs i * shapeSqDerivAbs (16 - i) :=
    primaryFiniteRow0Parent0Split100Sub0_product_order16_abs_of_factor_bounds
      hOmegaCont hShapeSqDerivCont hOmegaAbsNonneg
      (fun k hk => by
        simpa [omega] using hOmegaAbs eta hEta k hk)
      (fun k hk => by
        simpa [shapeSqDeriv] using hShapeSqDerivAbs eta hEta k hk)
  have hAdd :
      iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
        iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta +
          iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta := by
    unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
    change
      iteratedDeriv 16
          ((fun t : Real => omegaPrime t * shapeSq t) +
            fun t : Real => omega t * shapeSqDeriv t) eta =
        iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta +
          iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta
    rw [iteratedDeriv_add
      (hOmegaPrimeCont.mul hShapeSqCont).contDiffAt
      (hOmegaCont.mul hShapeSqDerivCont).contDiffAt]
  calc
    ‖iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ =
        ‖iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta +
          iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta‖ := by
        rw [hAdd]
    _ <=
        ‖iteratedDeriv 16 (fun t : Real => omegaPrime t * shapeSq t) eta‖ +
          ‖iteratedDeriv 16 (fun t : Real => omega t * shapeSqDeriv t) eta‖ :=
        norm_add_le _ _
    _ <=
        (∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) * omegaPrimeAbs i * shapeSqAbs (16 - i)) +
        (∑ i ∈ Finset.range (16 + 1),
          (Nat.choose 16 i : Real) * omegaAbs i * shapeSqDerivAbs (16 - i)) :=
        add_le_add hProd1 hProd2
    _ =
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
          omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs := by
        rfl

/--
Receiver from factor derivative bounds and an active-scale absolute bound to a
symmetric absolute bound for the checked order-16 component source.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_abs_of_factor_derivative_abs
    {omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs : Nat -> Real}
    {activeScaleAbs order16Abs : Real}
    (hOmegaPrimeAbsNonneg :
      ∀ k : Nat, k <= 16 -> 0 <= omegaPrimeAbs k)
    (hOmegaAbsNonneg :
      ∀ k : Nat, k <= 16 -> 0 <= omegaAbs k)
    (hOmegaPrimeAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
              eta‖ <= omegaPrimeAbs k)
    (hOmegaAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual
              eta‖ <= omegaAbs k)
    (hShapeSqAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              eta‖ <= shapeSqAbs k)
    (hShapeSqDerivAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
              eta‖ <= shapeSqDerivAbs k)
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        activeScaleAbs)
    (hBudget :
      activeScaleAbs *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
            omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs <=
        order16Abs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta‖ <= order16Abs := by
  intro eta hEta
  have hProduct :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_factor_derivative_abs
      hOmegaPrimeAbsNonneg hOmegaAbsNonneg hOmegaPrimeAbs hOmegaAbs
      hShapeSqAbs hShapeSqDerivAbs eta hEta
  have hScaleAbsNonneg : 0 <= activeScaleAbs :=
    (abs_nonneg primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff).trans
      hActiveScaleAbs
  calc
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
        eta‖ =
        ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ := by
        rw [
          primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual]
    _ =
        |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| *
          ‖iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ := by
        rw [norm_mul, Real.norm_eq_abs]
    _ <=
        activeScaleAbs *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
            omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs :=
        mul_le_mul hActiveScaleAbs hProduct (norm_nonneg _) hScaleAbsNonneg
    _ <= order16Abs := hBudget

/--
Same receiver, stated in the signed interval form consumed by
`Step33Sub0CombinedCancellationSourceIntervalCert.Valid`.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_factor_derivative_abs
    {omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs : Nat -> Real}
    {activeScaleAbs order16Abs : Real}
    (hOmegaPrimeAbsNonneg :
      ∀ k : Nat, k <= 16 -> 0 <= omegaPrimeAbs k)
    (hOmegaAbsNonneg :
      ∀ k : Nat, k <= 16 -> 0 <= omegaAbs k)
    (hOmegaPrimeAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
              eta‖ <= omegaPrimeAbs k)
    (hOmegaAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual
              eta‖ <= omegaAbs k)
    (hShapeSqAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
              eta‖ <= shapeSqAbs k)
    (hShapeSqDerivAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ k : Nat, k <= 16 ->
          ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual
              eta‖ <= shapeSqDerivAbs k)
    (hActiveScaleAbs :
      |primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff| <=
        activeScaleAbs)
    (hBudget :
      activeScaleAbs *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant
            omegaPrimeAbs omegaAbs shapeSqAbs shapeSqDerivAbs <=
        order16Abs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      -order16Abs <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <= order16Abs := by
  intro eta hEta
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_abs_of_factor_derivative_abs
      hOmegaPrimeAbsNonneg hOmegaAbsNonneg hOmegaPrimeAbs hOmegaAbs
      hShapeSqAbs hShapeSqDerivAbs hActiveScaleAbs hBudget eta hEta
  rw [Real.norm_eq_abs] at hAbs
  exact abs_le.mp hAbs

end Step33
end PSDpd
end Q3
