import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
zero-off-declared support facts, index chunk 4: 4..4.
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


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx4_of_delta_le_p5
    {δInt : Int}
    (hδle : δInt ≤ (5 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex4
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((5 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex4) ≤ (((5 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex4) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((5 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex4) / primaryK11Ell) ≤ ((((5 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex4) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((5 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex4) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : ((37 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex4 := by
          change ((37 : Real) / 20) ≤ (((1 : Nat) : Real) * ((1945910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587871 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((5 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex4) ≤ ((((5 : Int) : Real) / 4) - ((37 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((5 : Int) : Real) / 4)
        have hdiv_bound : ((((5 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex4) / ((3 : Real) / 10)) ≤ (((((5 : Int) : Real) / 4) - ((37 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx4_of_p11_le_delta
    {δInt : Int}
    (hδge : (11 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex4
    (by
      have hδreal : ((11 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((11 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4) := by
        have hdiv : (((11 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((11 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((11 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4) / primaryK11Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4 ≤ ((43 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((1945910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587872 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((43 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((11 : Int) : Real) / 4) - ((43 : Real) / 20)) ≤ (((11 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4) := by
          exact sub_le_sub_left hshift (((11 : Int) : Real) / 4)
        have hdiv_bound : (((((11 : Int) : Real) / 4) - ((43 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((11 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex4) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRMinusZeroOffDeclared_idx4
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex4.1 ∉ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (5 : Int)
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx4_of_delta_le_p5 hleft
  by_cases hright : (11 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx4_of_p11_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (6 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (10 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
