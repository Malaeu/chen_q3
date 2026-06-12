import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
zero-off-declared support facts, index chunk 87: 87..87.
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


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx87_of_m21_le_delta
    {δInt : Int}
    (hδge : (-21 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex87) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex87
    (by
      have hδreal : ((-21 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-21 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex87) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex87) := by
        have hdiv : (((-21 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex87)
      have hmono : ((((-21 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex87) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex87) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((-21 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex87) / controlK9Ell) := by
        have hshift : ((117 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex87 := by
          change ((117 : Real) / 20) ≤ (((1 : Nat) : Real) * ((5855071922202427163199481522498639709148885337460362389226388599216983137544793935201123354203720 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-21 : Int) : Real) / 4) + ((117 : Real) / 20)) ≤ (((-21 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex87) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-21 : Int) : Real) / 4)
        have hdiv_bound : (((((-21 : Int) : Real) / 4) + ((117 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-21 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex87) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRPlusZeroOffDeclared_idx87
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex87.1 ∉ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex87) / controlK9Ell) = 0 := by
  by_cases hright : (-21 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx87_of_m21_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hrightGap : δInt ≤ (-22 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
