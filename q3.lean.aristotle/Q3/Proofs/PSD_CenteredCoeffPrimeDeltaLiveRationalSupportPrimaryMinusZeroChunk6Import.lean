import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
zero-off-declared support facts, index chunk 6: 6..6.
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


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx6_of_delta_le_p6
    {δInt : Int}
    (hδle : δInt ≤ (6 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex6
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((6 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex6) ≤ (((6 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex6) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((6 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex6) / primaryK11Ell) ≤ ((((6 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex6) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((6 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex6) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : ((42 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex6 := by
          change ((42 : Real) / 20) ≤ (((2 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813732 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((6 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex6) ≤ ((((6 : Int) : Real) / 4) - ((42 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((6 : Int) : Real) / 4)
        have hdiv_bound : ((((6 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex6) / ((3 : Real) / 10)) ≤ (((((6 : Int) : Real) / 4) - ((42 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx6_of_p12_le_delta
    {δInt : Int}
    (hδge : (12 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex6
    (by
      have hδreal : ((12 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6) := by
        have hdiv : (((12 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6) / primaryK11Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6 ≤ ((48 : Real) / 20) := by
          change (((2 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((48 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((12 : Int) : Real) / 4) - ((48 : Real) / 20)) ≤ (((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6) := by
          exact sub_le_sub_left hshift (((12 : Int) : Real) / 4)
        have hdiv_bound : (((((12 : Int) : Real) / 4) - ((48 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex6) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRMinusZeroOffDeclared_idx6
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex6.1 ∉ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (6 : Int)
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx6_of_delta_le_p6 hleft
  by_cases hright : (12 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx6_of_p12_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (7 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (11 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
