import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
zero-off-declared support facts, index chunk 22: 22..22.
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


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx22_of_delta_le_p13
    {δInt : Int}
    (hδle : δInt ≤ (13 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex22
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((13 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) ≤ (((13 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((13 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / controlK9Ell) ≤ ((((13 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((13 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : ((77 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex22 := by
          change ((77 : Real) / 20) ≤ (((2 : Nat) : Real) * ((1945910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587871 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((13 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) ≤ ((((13 : Int) : Real) / 4) - ((77 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((13 : Int) : Real) / 4)
        have hdiv_bound : ((((13 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / ((3 : Real) / 10)) ≤ (((((13 : Int) : Real) / 4) - ((77 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx22_of_p18_le_delta
    {δInt : Int}
    (hδge : (18 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex22
    (by
      have hδreal : ((18 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((18 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) := by
        have hdiv : (((18 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((18 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((18 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / controlK9Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22 ≤ ((78 : Real) / 20) := by
          change (((2 : Nat) : Real) * ((1945910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587872 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((78 : Real) / 20)
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((18 : Int) : Real) / 4) - ((78 : Real) / 20)) ≤ (((18 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) := by
          exact sub_le_sub_left hshift (((18 : Int) : Real) / 4)
        have hdiv_bound : (((((18 : Int) : Real) / 4) - ((78 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((18 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRMinusZeroOffDeclared_idx22
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex22.1 ∉ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (13 : Int)
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx22_of_delta_le_p13 hleft
  by_cases hright : (18 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx22_of_p18_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (14 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (17 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
