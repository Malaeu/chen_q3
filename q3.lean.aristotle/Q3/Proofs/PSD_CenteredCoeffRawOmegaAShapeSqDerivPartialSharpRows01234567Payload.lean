import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows0123456Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Partial-sharp ShapeSqDeriv payload for rows `0`, `1`, `2`, `3`, `4`, `5`, `6`, and
`7`.

Rows `0..6` reuse the checked rows0123456 source.  Row `7` uses the same coarse
shape-derivative majorant at exact product order `n = 8`, divided by `7!`.
Rows `8..15` and order `16` remain coarse.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs :
    Rat :=
  ((2 : Rat) ^ (24 : Nat) * (24 : Rat) ^ (8 : Nat)) / 5040 + 1

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff :
    Fin 16 -> Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs
    (j : Fin 16) : Rat :=
  if j.1 = 0 then
    (3 : Rat) / 40
  else if j.1 = 1 then
    (1 : Rat) / 25
  else if j.1 = 2 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow2CoarseCoeffErrorAbs
  else if j.1 = 3 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow3CoarseCoeffErrorAbs
  else if j.1 = 4 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow4CoarseCoeffErrorAbs
  else if j.1 = 5 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow5CoarseCoeffErrorAbs
  else if j.1 = 6 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow6CoarseCoeffErrorAbs
  else if j.1 = 7 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs
  else
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget + 1

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Order16Abs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567TaylorRemainderAbs :
    Real :=
  (∑ j : Fin 16,
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs
          j : Real) *
        ((1 : Real) / 20) ^ j.1) +
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Order16Abs :
      Real) *
      ((1 : Real) / 20) ^ 16 / (Nat.factorial 16 : Real)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567Coeff_eq_generated :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated := by
  rfl

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet7_coarseSmall_abs :
    ‖iteratedDeriv 7 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
        ((1 : Real) / 20) / (Nat.factorial 7 : Real) -
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff
        ⟨7, by norm_num⟩ : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs :
        Real) := by
  let shape : Real -> Real :=
    fun t : Real =>
      (centeredBSplineImagTransformRealClosedForm
        11 ((3 : Real) / 10) t) ^ 2
  have hcenter :
      ((1 : Real) / 20) ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
    norm_num
  have hProduct :
      ‖iteratedDeriv 8 shape ((1 : Real) / 20)‖ <=
        (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (8 : Nat) := by
    have hraw :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs
        (n := 8)
        (M := primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs)
        (eta := ((1 : Real) / 20))
        (by
          intro k hk
          unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRationalAbs
          unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeRatAbs
          positivity)
        (by
          intro k hk
          exact
            primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational
              ((1 : Real) / 20) hcenter k (by omega))
    have hsum :=
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq 8
    simpa [shape, hsum] using hraw
  have hShift :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ
      7 ((1 : Real) / 20)
  have hDiv :
      ‖iteratedDeriv 7 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
          ((1 : Real) / 20) / (Nat.factorial 7 : Real)‖ <=
        ((2 : Real) ^ (24 : Nat) * (24 : Real) ^ (8 : Nat)) / 5040 := by
    have hraw :=
      div_le_div_of_nonneg_right hProduct (by norm_num : (0 : Real) <= 5040)
    rw [hShift]
    norm_num [shape] at hraw ⊢
    exact hraw
  have hTarget :
      ‖iteratedDeriv 7 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
          ((1 : Real) / 20) / (Nat.factorial 7 : Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs :
          Real) := by
    exact le_trans hDiv (by
      norm_num
        [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs])
  simpa
    [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated]
    using hTarget

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567_valid :
    (ShapeSqDerivTaylorIntervalCert.singleAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Order16Abs).Valid := by
  refine ShapeSqDerivTaylorIntervalCert.Valid.of_single_abs ?hNonneg ?hCenter ?hOrder
  · intro j
    by_cases h0 : j.1 = 0
    · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
        h0]
    · by_cases h1 : j.1 = 1
      · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
          h0, h1]
      · by_cases h2 : j.1 = 2
        · norm_num
            [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow2CoarseCoeffErrorAbs,
             h0, h1, h2]
        · by_cases h3 : j.1 = 3
          · norm_num
              [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow3CoarseCoeffErrorAbs,
               h0, h1, h2, h3]
          · by_cases h4 : j.1 = 4
            · norm_num
                [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow4CoarseCoeffErrorAbs,
                 h0, h1, h2, h3, h4]
            · by_cases h5 : j.1 = 5
              · norm_num
                  [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow5CoarseCoeffErrorAbs,
                   h0, h1, h2, h3, h4, h5]
              · by_cases h6 : j.1 = 6
                · norm_num
                    [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow6CoarseCoeffErrorAbs,
                     h0, h1, h2, h3, h4, h5, h6]
                · by_cases h7 : j.1 = 7
                  · norm_num
                      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs,
                     h0, h1, h2, h3, h4, h5, h6, h7]
                  · norm_num
                      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                       h0, h1, h2, h3, h4, h5, h6, h7,
                       primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]
  · have hRows0123456 :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123456_valid
    have hOldInputs :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
    intro j
    by_cases h0 : j.1 = 0
    · simpa
         [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456Coeff,
         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456CoeffErrorAbs,
         ShapeSqDerivTaylorIntervalCert.singleAbs,
         ShapeSqDerivTaylorIntervalCert.single, h0] using hRows0123456.1 j
    · by_cases h1 : j.1 = 1
      · simpa
           [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456Coeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456CoeffErrorAbs,
           ShapeSqDerivTaylorIntervalCert.singleAbs,
           ShapeSqDerivTaylorIntervalCert.single, h0, h1] using hRows0123456.1 j
      · by_cases h2 : j.1 = 2
        · simpa
             [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456Coeff,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456CoeffErrorAbs,
             ShapeSqDerivTaylorIntervalCert.singleAbs,
             ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2] using
            hRows0123456.1 j
        · by_cases h3 : j.1 = 3
          · simpa
               [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456Coeff,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456CoeffErrorAbs,
               ShapeSqDerivTaylorIntervalCert.singleAbs,
               ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3] using
              hRows0123456.1 j
          · by_cases h4 : j.1 = 4
            · simpa
                 [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456Coeff,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456CoeffErrorAbs,
                 ShapeSqDerivTaylorIntervalCert.singleAbs,
                 ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4] using
                hRows0123456.1 j
            · by_cases h5 : j.1 = 5
              · simpa
                   [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456Coeff,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456CoeffErrorAbs,
                   ShapeSqDerivTaylorIntervalCert.singleAbs,
                   ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5] using
                  hRows0123456.1 j
              · by_cases h6 : j.1 = 6
                · simpa
                    [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456Coeff,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows0123456CoeffErrorAbs,
                     ShapeSqDerivTaylorIntervalCert.singleAbs,
                     ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6] using
                    hRows0123456.1 j
                · by_cases h7 : j.1 = 7
                  · have hj : j = ⟨7, by norm_num⟩ := Fin.ext h7
                    subst j
                    simpa
                      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                       h0, h1, h2, h3, h4, h5, h6, h7]
                      using
                        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet7_coarseSmall_abs
                  · simpa
                      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff,
                       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
                       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff,
                       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
                       ShapeSqDerivTaylorIntervalCert.singleAbs,
                       ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6, h7] using
                      hOldInputs.1 j
  · have hOldInputs :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
    intro eta heta
    simpa
      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Order16Abs,
       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs,
       ShapeSqDerivTaylorIntervalCert.singleAbs,
       ShapeSqDerivTaylorIntervalCert.single] using
      hOldInputs.2 eta heta

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567TaylorSource :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta -
        rawOmegaATaylorPolynomial 15 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567TaylorRemainderAbs := by
  exact
    ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource
      (data := ShapeSqDerivTaylorIntervalCert.singleAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Coeff
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Order16Abs)
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567TaylorRemainderAbs)
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567_valid
      (by
        unfold
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567TaylorRemainderAbs
        rfl)

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567ShapeSqDerivRows8To15_width_fail :
    ((1866608532757 : Real) / 500000000000000000000000000000 -
        (-(94119513411 : Real) / 500000000000000000000000000000)) <
      2 * ((primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs :
          Real) *
        (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
          Real) *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567TaylorRemainderAbs) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567TaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567CoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567Order16Abs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow2CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow3CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow4CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow5CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow6CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
    Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderAbs,
    Fin.sum_univ_succ
  ]

end Step33
end PSDpd
end Q3
