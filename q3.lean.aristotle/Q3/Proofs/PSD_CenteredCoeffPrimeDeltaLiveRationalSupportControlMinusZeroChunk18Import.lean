import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
zero-off-declared support facts, index chunk 18: 18..18.
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


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx18_of_delta_le_p12
    {δInt : Int}
    (hδle : δInt ≤ (12 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex18) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex18
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((12 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex18) ≤ (((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex18) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((12 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex18) / controlK9Ell) ≤ ((((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex18) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex18) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : ((72 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex18 := by
          change ((72 : Real) / 20) ≤ (((1 : Nat) : Real) * ((3610917912644224444368095671031447163900077587167636163644912681192989746990361065399021533672168 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex18) ≤ ((((12 : Int) : Real) / 4) - ((72 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((12 : Int) : Real) / 4)
        have hdiv_bound : ((((12 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex18) / ((3 : Real) / 10)) ≤ (((((12 : Int) : Real) / 4) - ((72 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx18_of_p17_le_delta
    {δInt : Int}
    (hδge : (17 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex18) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex18
    (by
      have hδreal : ((17 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18) ≤ (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18) := by
        have hdiv : (((17 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18) / controlK9Ell) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18 ≤ ((73 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((3610917912644224444368095671031447163900077587167636163644912681192989746990361065399021533672169 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((73 : Real) / 20)
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((17 : Int) : Real) / 4) - ((73 : Real) / 20)) ≤ (((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18) := by
          exact sub_le_sub_left hshift (((17 : Int) : Real) / 4)
        have hdiv_bound : (((((17 : Int) : Real) / 4) - ((73 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((17 : Int) : Real) / 4 - activeL3RationalPrimeShiftUpper activeL3RatWeightIndex18) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRMinusZeroOffDeclared_idx18
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex18.1 ∉ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex18) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (12 : Int)
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx18_of_delta_le_p12 hleft
  by_cases hright : (17 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx18_of_p17_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (13 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (16 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
