import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
zero-off-declared support facts, index chunk 77: 77..77.
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


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx77_of_delta_le_p20
    {δInt : Int}
    (hδle : δInt ≤ (20 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex77) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex77
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((20 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex77) ≤ (((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex77) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((20 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex77) / controlK9Ell) ≤ ((((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex77) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex77) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : ((112 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex77 := by
          change ((112 : Real) / 20) ≤ (((2 : Nat) : Real) * ((2833213344056216080249534617873126535588203012585744787297237737882292575800931280912094868037502 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex77) ≤ ((((20 : Int) : Real) / 4) - ((112 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((20 : Int) : Real) / 4)
        have hdiv_bound : ((((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex77) / ((3 : Real) / 10)) ≤ (((((20 : Int) : Real) / 4) - ((112 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)

theorem controlK9RationalDeltaLiveRMinusZeroOffDeclared_idx77
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex77.1 ∉ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex77) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (20 : Int)
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx77_of_delta_le_p20 hleft
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (21 : Int) ≤ δInt := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
