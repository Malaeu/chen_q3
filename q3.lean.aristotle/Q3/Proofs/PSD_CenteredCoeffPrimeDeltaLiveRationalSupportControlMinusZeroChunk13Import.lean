import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
zero-off-declared support facts, index chunk 13: 13..13.
-/

noncomputable section

open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffAnalyticP0Import
open CenteredCoeffPrimeEntryHboxImport
open CenteredCoeffPrimeDeltaLivePayloadImport
open CenteredCoeffPrimePositivePartTightImport
open CenteredCoeffEntryHboxImport


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx13_of_delta_le_p10
    {δInt : Int}
    (hδle : δInt ≤ (10 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex13) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex13
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((10 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex13) ≤ (((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex13) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((10 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex13) / controlK9Ell) ≤ ((((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex13) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex13) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : ((62 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex13 := by
          change ((62 : Real) / 20) ≤ (((2 : Nat) : Real) * ((1609437912434100374600759333226187639525601354268517721912647891474178987707657764630133878093179 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex13) ≤ ((((10 : Int) : Real) / 4) - ((62 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((10 : Int) : Real) / 4)
        have hdiv_bound : ((((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex13) / ((3 : Real) / 10)) ≤ (((((10 : Int) : Real) / 4) - ((62 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx13_of_p16_le_delta
    {δInt : Int}
    (hδge : (16 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex13) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex13
    (by
      have hδreal : ((16 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13) := by
        have hdiv : (((16 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13) / controlK9Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13 ≤ ((68 : Real) / 20) := by
          change (((2 : Nat) : Real) * ((1609437912434100374600759333226187639525601354268517721912647891474178987707657764630133878093180 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((68 : Real) / 20)
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((16 : Int) : Real) / 4) - ((68 : Real) / 20)) ≤ (((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13) := by
          exact sub_le_sub_left hshift (((16 : Int) : Real) / 4)
        have hdiv_bound : (((((16 : Int) : Real) / 4) - ((68 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex13) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRMinusZeroOffDeclared_idx13
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex13.1 ∉ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex13) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (10 : Int)
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx13_of_delta_le_p10 hleft
  by_cases hright : (16 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx13_of_p16_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (11 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (15 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
