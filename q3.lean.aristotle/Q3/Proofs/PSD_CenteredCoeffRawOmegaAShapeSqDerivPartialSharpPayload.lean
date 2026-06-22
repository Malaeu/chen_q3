import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorTightBudgetKill
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivCoeffRows

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Partial-sharp ShapeSqDeriv payload for Step33A.1-A sub0.

This file spends only the currently checked ShapeSqDeriv center rows `0` and
`1`.  Rows `2..15` and the order-16 bound still fall back to the previous
coarse proof budget.  The final theorem records that this partial sharpening
is still far too wide for the active residual interval, so the live gap is the
remaining rows `2..15` / order-16 source, not the already checked rows `0,1`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Same coefficient stream as the active generated ShapeSqDeriv Taylor source. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff :
    Fin 16 -> Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated

/-- Row `0` and row `1` use checked center-jet rows; rows `2..15` remain coarse. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs
    (j : Fin 16) : Rat :=
  if j.1 = 0 then
    (3 : Rat) / 40
  else if j.1 = 1 then
    (1 : Rat) / 25
  else
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget + 1

/-- Order-16 still uses the previous coarse source. -/
def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpOrder16Abs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpTaylorRemainderAbs :
    Real :=
  (∑ j : Fin 16,
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs
          j : Real) *
        ((1 : Real) / 20) ^ j.1) +
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpOrder16Abs :
      Real) *
      ((1 : Real) / 20) ^ 16 / (Nat.factorial 16 : Real)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_partialSharpCoeff_eq_generated :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated := by
  rfl

/-- Proof-grade partial-sharp ShapeSqDeriv interval certificate.

The proof spends the checked power-series rows `0` and `1`; all later rows and
the order-16 bound are inherited from the previously checked coarse certificate.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_partialSharp_valid :
    (ShapeSqDerivTaylorIntervalCert.singleAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpOrder16Abs).Valid := by
  refine ShapeSqDerivTaylorIntervalCert.Valid.of_single_abs ?hNonneg ?hCenter ?hOrder
  · intro j
    by_cases h0 : j.1 = 0
    · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
        h0]
    · by_cases h1 : j.1 = 1
      · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
          h0, h1]
      · norm_num
          [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
           h0, h1, primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]
  · have hOldInputs :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
    intro j
    by_cases h0 : j.1 = 0
    · have hj : j = ⟨0, by norm_num⟩ := Fin.ext h0
      subst j
      have hrow :=
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff0_interval_generated
      have hjet :=
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff
          ⟨0, by norm_num⟩
      rw [Real.norm_eq_abs, hjet, abs_le]
      constructor
      · norm_num
          [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCenter_generated,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated] at hrow ⊢
        linarith [hrow.1]
      · norm_num
          [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCenter_generated,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated] at hrow ⊢
        linarith [hrow.2]
    · by_cases h1 : j.1 = 1
      · have hj : j = ⟨1, by norm_num⟩ := Fin.ext h1
        subst j
        have hrow :=
          primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff1_interval_generated
        have hjet :=
          primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff
            ⟨1, by norm_num⟩
        rw [Real.norm_eq_abs, hjet, abs_le]
        constructor
        · norm_num
            [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCenter_generated,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated] at hrow ⊢
          linarith [hrow.1]
        · norm_num
            [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCenter_generated,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated] at hrow ⊢
          linarith [hrow.2]
      · simpa
          [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
           ShapeSqDerivTaylorIntervalCert.singleAbs,
           ShapeSqDerivTaylorIntervalCert.single, h0, h1] using hOldInputs.1 j
  · have hOldInputs :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
    intro eta heta
    simpa
      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpOrder16Abs,
       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs,
       ShapeSqDerivTaylorIntervalCert.singleAbs,
       ShapeSqDerivTaylorIntervalCert.single] using
      hOldInputs.2 eta heta

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivPartialSharpTaylorSource :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta -
        rawOmegaATaylorPolynomial 15 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpTaylorRemainderAbs := by
  exact
    ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource
      (data := ShapeSqDerivTaylorIntervalCert.singleAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeff
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpOrder16Abs)
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpTaylorRemainderAbs)
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_partialSharp_valid
      (by
        unfold
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpTaylorRemainderAbs
        rfl)

/-- Even after spending checked rows `0` and `1`, the residual core width is
still larger than the active target width.  The remaining live source gap is
therefore rows `2..15` plus the order-16 bound. -/
theorem primaryFiniteRow0Parent0Split100Sub0_partialSharpShapeSqDerivRows2To15_width_fail :
    ((1866608532757 : Real) / 500000000000000000000000000000 -
        (-(94119513411 : Real) / 500000000000000000000000000000)) <
      2 * ((primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs :
          Real) *
        (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
          Real) *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpTaylorRemainderAbs) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPartialSharpOrder16Abs,
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
    Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderAbs,
    Fin.sum_univ_succ
  ]

end Step33
end PSDpd
end Q3
