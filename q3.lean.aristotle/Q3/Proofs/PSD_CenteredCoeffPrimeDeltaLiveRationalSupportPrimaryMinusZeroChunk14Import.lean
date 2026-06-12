import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
zero-off-declared support facts, index chunk 14: 14..14.
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


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx14_of_delta_le_p10
    {δInt : Int}
    (hδle : δInt ≤ (10 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex14
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((10 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) ≤ (((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((10 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / primaryK11Ell) ≤ ((((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : ((62 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex14 := by
          change ((62 : Real) / 20) ≤ (((3 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813732 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) ≤ ((((10 : Int) : Real) / 4) - ((62 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((10 : Int) : Real) / 4)
        have hdiv_bound : ((((10 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / ((3 : Real) / 10)) ≤ (((((10 : Int) : Real) / 4) - ((62 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx14_of_p16_le_delta
    {δInt : Int}
    (hδge : (16 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex14
    (by
      have hδreal : ((16 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) := by
        have hdiv : (((16 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / primaryK11Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14 ≤ ((68 : Real) / 20) := by
          change (((3 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((68 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((16 : Int) : Real) / 4) - ((68 : Real) / 20)) ≤ (((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) := by
          exact sub_le_sub_left hshift (((16 : Int) : Real) / 4)
        have hdiv_bound : (((((16 : Int) : Real) / 4) - ((68 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((16 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRMinusZeroOffDeclared_idx14
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex14.1 ∉ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (10 : Int)
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx14_of_delta_le_p10 hleft
  by_cases hright : (16 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx14_of_p16_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (11 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (15 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
