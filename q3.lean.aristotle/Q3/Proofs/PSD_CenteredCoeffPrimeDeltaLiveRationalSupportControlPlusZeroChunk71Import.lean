import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
zero-off-declared support facts, index chunk 71: 71..71.
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


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx71_of_m19_le_delta
    {δInt : Int}
    (hδge : (-19 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex71
    (by
      have hδreal : ((-19 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex71) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex71) := by
        have hdiv : (((-19 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex71)
      have hmono : ((((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex71) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex71) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex71) / controlK9Ell) := by
        have hshift : ((107 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex71 := by
          change ((107 : Real) / 20) ≤ (((1 : Nat) : Real) * ((5572154032177764551085926264205072090385483840064565278827832833141200721758068253120067962186734 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-19 : Int) : Real) / 4) + ((107 : Real) / 20)) ≤ (((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex71) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-19 : Int) : Real) / 4)
        have hdiv_bound : (((((-19 : Int) : Real) / 4) + ((107 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex71) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRPlusZeroOffDeclared_idx71
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex71.1 ∉ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell) = 0 := by
  by_cases hright : (-19 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx71_of_m19_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hrightGap : δInt ≤ (-20 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
