import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012345678910Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Partial-sharp ShapeSqDeriv payload for rows `0`, `1`, `2`, `3`, `4`, `5`, `6`,
`7`, `8`, `9`, `10`, and `11`.

Rows `0..10` reuse the checked rows012345678910 source.  Row `11` uses the same
coarse shape-derivative majorant at exact product order `n = 12`, divided by
`11!`.  Rows `12..15` and order `16` remain coarse.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs :
    Rat :=
  ((2 : Rat) ^ (24 : Nat) * (24 : Rat) ^ (12 : Nat)) / 39916800 + 1

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff :
    Fin 16 -> Rat :=
  primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
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
  else if j.1 = 8 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow8CoarseCoeffErrorAbs
  else if j.1 = 9 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow9CoarseCoeffErrorAbs
  else if j.1 = 10 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow10CoarseCoeffErrorAbs
  else if j.1 = 11 then
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs
  else
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget + 1

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget

def primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs :
    Real :=
  (∑ j : Fin 16,
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
          j : Real) *
        ((1 : Real) / 20) ^ j.1) +
    (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs :
      Real) *
      ((1 : Real) / 20) ^ 16 / (Nat.factorial 16 : Real)

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011Coeff_eq_generated :
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff =
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated := by
  rfl

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet11_coarseSmall_abs :
    ‖iteratedDeriv 11 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
        ((1 : Real) / 20) / (Nat.factorial 11 : Real) -
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
        ⟨11, by norm_num⟩ : Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs :
        Real) := by
  let shape : Real -> Real :=
    fun t : Real =>
      (centeredBSplineImagTransformRealClosedForm
        11 ((3 : Real) / 10) t) ^ 2
  have hcenter :
      ((1 : Real) / 20) ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
    norm_num
  have hProduct :
      ‖iteratedDeriv 12 shape ((1 : Real) / 20)‖ <=
        (2 : Real) ^ (24 : Nat) * (24 : Real) ^ (12 : Nat) := by
    have hraw :=
      primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs
        (n := 12)
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
      primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeProductSum_eq 12
    simpa [shape, hsum] using hraw
  have hShift :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ
      11 ((1 : Real) / 20)
  have hDiv :
      ‖iteratedDeriv 11 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
          ((1 : Real) / 20) / (Nat.factorial 11 : Real)‖ <=
        ((2 : Real) ^ (24 : Nat) * (24 : Real) ^ (12 : Nat)) / 39916800 := by
    have hraw :=
      div_le_div_of_nonneg_right hProduct (by norm_num : (0 : Real) <= 39916800)
    rw [hShift]
    norm_num [shape] at hraw ⊢
    exact hraw
  have hTarget :
      ‖iteratedDeriv 11 primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv
          ((1 : Real) / 20) / (Nat.factorial 11 : Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs :
          Real) := by
    exact le_trans hDiv (by
      norm_num
        [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs])
  simpa
    [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated]
    using hTarget

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011_valid :
    (ShapeSqDerivTaylorIntervalCert.singleAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs).Valid := by
  refine ShapeSqDerivTaylorIntervalCert.Valid.of_single_abs ?hNonneg ?hCenter ?hOrder
  · intro j
    by_cases h0 : j.1 = 0
    · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
        h0]
    · by_cases h1 : j.1 = 1
      · norm_num [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
          h0, h1]
      · by_cases h2 : j.1 = 2
        · norm_num
            [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow2CoarseCoeffErrorAbs,
             h0, h1, h2]
        · by_cases h3 : j.1 = 3
          · norm_num
              [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow3CoarseCoeffErrorAbs,
               h0, h1, h2, h3]
          · by_cases h4 : j.1 = 4
            · norm_num
                [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow4CoarseCoeffErrorAbs,
                 h0, h1, h2, h3, h4]
            · by_cases h5 : j.1 = 5
              · norm_num
                  [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow5CoarseCoeffErrorAbs,
                   h0, h1, h2, h3, h4, h5]
              · by_cases h6 : j.1 = 6
                · norm_num
                    [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow6CoarseCoeffErrorAbs,
                     h0, h1, h2, h3, h4, h5, h6]
                · by_cases h7 : j.1 = 7
                  · norm_num
                      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs,
                     h0, h1, h2, h3, h4, h5, h6, h7]
                  · by_cases h8 : j.1 = 8
                    · norm_num
                        [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow8CoarseCoeffErrorAbs,
                         h0, h1, h2, h3, h4, h5, h6, h7, h8]
                    · by_cases h9 : j.1 = 9
                      · norm_num
                          [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow9CoarseCoeffErrorAbs,
                           h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
                      · by_cases h10 : j.1 = 10
                        · norm_num
                            [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow10CoarseCoeffErrorAbs,
                             h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
                        · by_cases h11 : j.1 = 11
                          · norm_num
                              [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs,
                               h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                          · norm_num
                              [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                               h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                               primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget]
  · have hRows012345678910 :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345678910_valid
    have hOldInputs :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
    intro j
    by_cases h0 : j.1 = 0
    · simpa
         [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
         ShapeSqDerivTaylorIntervalCert.singleAbs,
         ShapeSqDerivTaylorIntervalCert.single, h0] using hRows012345678910.1 j
    · by_cases h1 : j.1 = 1
      · simpa
           [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
           ShapeSqDerivTaylorIntervalCert.singleAbs,
           ShapeSqDerivTaylorIntervalCert.single, h0, h1] using hRows012345678910.1 j
      · by_cases h2 : j.1 = 2
        · simpa
             [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
             ShapeSqDerivTaylorIntervalCert.singleAbs,
             ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2] using
            hRows012345678910.1 j
        · by_cases h3 : j.1 = 3
          · simpa
               [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
               ShapeSqDerivTaylorIntervalCert.singleAbs,
               ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3] using
              hRows012345678910.1 j
          · by_cases h4 : j.1 = 4
            · simpa
                 [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
                 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
                 ShapeSqDerivTaylorIntervalCert.singleAbs,
                 ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4] using
                hRows012345678910.1 j
            · by_cases h5 : j.1 = 5
              · simpa
                   [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
                   primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
                   ShapeSqDerivTaylorIntervalCert.singleAbs,
                   ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5] using
                  hRows012345678910.1 j
              · by_cases h6 : j.1 = 6
                · simpa
                    [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
                     primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
                     ShapeSqDerivTaylorIntervalCert.singleAbs,
                     ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6] using
                    hRows012345678910.1 j
                · by_cases h7 : j.1 = 7
                  · simpa
                      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
                       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
                       ShapeSqDerivTaylorIntervalCert.singleAbs,
                       ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6, h7] using
                      hRows012345678910.1 j
                  · by_cases h8 : j.1 = 8
                    · simpa
                        [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
                         primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
                         ShapeSqDerivTaylorIntervalCert.singleAbs,
                         ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6, h7, h8] using
                        hRows012345678910.1 j
                    · by_cases h9 : j.1 = 9
                      · simpa
                          [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
                           primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
                           ShapeSqDerivTaylorIntervalCert.singleAbs,
                           ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] using
                          hRows012345678910.1 j
                      · by_cases h10 : j.1 = 10
                        · simpa
                            [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910Coeff,
                             primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows012345678910CoeffErrorAbs,
                             ShapeSqDerivTaylorIntervalCert.singleAbs,
                             ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] using
                            hRows012345678910.1 j
                        · by_cases h11 : j.1 = 11
                          · have hj : j = ⟨11, by norm_num⟩ := Fin.ext h11
                            subst j
                            simpa
                              [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                               h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
                              using
                                primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet11_coarseSmall_abs
                          · simpa
                              [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff,
                               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
                               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff,
                               primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeffErrorAbs,
                               ShapeSqDerivTaylorIntervalCert.singleAbs,
                               ShapeSqDerivTaylorIntervalCert.single, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] using
                              hOldInputs.1 j
  · have hOldInputs :=
      ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs
        primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
    intro eta heta
    simpa
      [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs,
       primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightOrder16Abs,
       ShapeSqDerivTaylorIntervalCert.singleAbs,
       ShapeSqDerivTaylorIntervalCert.single] using
      hOldInputs.2 eta heta

theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567891011TaylorSource :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta -
        rawOmegaATaylorPolynomial 15 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs := by
  exact
    ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource
      (data := ShapeSqDerivTaylorIntervalCert.singleAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Coeff
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs)
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs)
      primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011_valid
      (by
        unfold
          primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs
        rfl)

theorem primaryFiniteRow0Parent0Split100Sub0_rows01234567891011ShapeSqDerivRows12To15_width_pass :
    2 * ((primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs :
          Real) *
        (primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs :
          Real) *
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs) <=
      ((1866608532757 : Real) / 500000000000000000000000000000 -
        (-(94119513411 : Real) / 500000000000000000000000000000)) := by
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0NominalScaleErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0OmegaTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorUpper,
    primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorLower,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011TaylorRemainderAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011CoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRows01234567891011Order16Abs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow2CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow3CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow4CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow5CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow6CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow7CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow8CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow9CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow10CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivRow11CoarseCoeffErrorAbs,
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqBudget,
    Q3.PSDpd.Step33.Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderAbs,
    Fin.sum_univ_succ
  ]

end Step33
end PSDpd
end Q3
