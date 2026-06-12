import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
zero-off-declared support facts, index chunk 72: 72..72.
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


private theorem controlK9RationalDeltaLiveRMinus_eq_zero_idx72_of_delta_le_p19
    {δInt : Int}
    (hδle : δInt ≤ (19 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex72) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex72
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((19 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex72) ≤ (((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex72) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((19 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex72) / controlK9Ell) ≤ ((((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex72) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex72) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : ((107 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex72 := by
          change ((107 : Real) / 20) ≤ (((1 : Nat) : Real) * ((5594711379601839106219953180495237117871048111163037614197601132382099951585438154162025704330860 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex72) ≤ ((((19 : Int) : Real) / 4) - ((107 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((19 : Int) : Real) / 4)
        have hdiv_bound : ((((19 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex72) / ((3 : Real) / 10)) ≤ (((((19 : Int) : Real) / 4) - ((107 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)

theorem controlK9RationalDeltaLiveRMinusZeroOffDeclared_idx72
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex72.1 ∉ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex72) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (19 : Int)
  · exact controlK9RationalDeltaLiveRMinus_eq_zero_idx72_of_delta_le_p19 hleft
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (20 : Int) ≤ δInt := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
