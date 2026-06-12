import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
zero-off-declared support facts, index chunk 25: 25..25.
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


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx25_of_delta_le_p14
    {δInt : Int}
    (hδle : δInt ≤ (14 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex25
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((14 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex25) ≤ (((14 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex25) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((14 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex25) / primaryK11Ell) ≤ ((((14 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex25) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((14 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex25) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : ((82 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex25 := by
          change ((82 : Real) / 20) ≤ (((1 : Nat) : Real) * ((4110873864173311248751389103425614746315681743081261062937383646419439806844948731185429206100103 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((14 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex25) ≤ ((((14 : Int) : Real) / 4) - ((82 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((14 : Int) : Real) / 4)
        have hdiv_bound : ((((14 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex25) / ((3 : Real) / 10)) ≤ (((((14 : Int) : Real) / 4) - ((82 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx25_of_p19_le_delta
    {δInt : Int}
    (hδge : (19 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex25
    (by
      have hδreal : ((19 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25) := by
        have hdiv : (((19 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25) / primaryK11Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25 ≤ ((83 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((4110873864173311248751389103425614746315681743081261062937383646419439806844948731185429206100104 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((83 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((19 : Int) : Real) / 4) - ((83 : Real) / 20)) ≤ (((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25) := by
          exact sub_le_sub_left hshift (((19 : Int) : Real) / 4)
        have hdiv_bound : (((((19 : Int) : Real) / 4) - ((83 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex25) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRMinusZeroOffDeclared_idx25
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex25.1 ∉ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (14 : Int)
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx25_of_delta_le_p14 hleft
  by_cases hright : (19 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx25_of_p19_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (15 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (18 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
