import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
zero-off-declared support facts, index chunk 43: 43..43.
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


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx43_of_delta_le_p17
    {δInt : Int}
    (hδle : δInt ≤ (17 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex43) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex43
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((17 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex43) ≤ (((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex43) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((17 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex43) / controlK9Ell) ≤ ((((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex43) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex43) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : ((97 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex43 := by
          change ((97 : Real) / 20) ≤ (((7 : Nat) : Real) * ((693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex43) ≤ ((((17 : Int) : Real) / 4) - ((97 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((17 : Int) : Real) / 4)
        have hdiv_bound : ((((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex43) / ((3 : Real) / 10)) ≤ (((((17 : Int) : Real) / 4) - ((97 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx43_of_p22_le_delta
    {δInt : Int}
    (hδge : (22 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex43) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex43
    (by
      have hδreal : ((22 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((22 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43) := by
        have hdiv : (((22 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((22 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((22 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43) / controlK9Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43 ≤ ((98 : Real) / 20) := by
          change (((7 : Nat) : Real) * ((693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((98 : Real) / 20)
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((22 : Int) : Real) / 4) - ((98 : Real) / 20)) ≤ (((22 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43) := by
          exact sub_le_sub_left hshift (((22 : Int) : Real) / 4)
        have hdiv_bound : (((((22 : Int) : Real) / 4) - ((98 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((22 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex43) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRMinusZeroOffDeclared_idx43
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex43.1 ∉ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex43) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (17 : Int)
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx43_of_delta_le_p17 hleft
  by_cases hright : (22 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx43_of_p22_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (18 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (21 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
