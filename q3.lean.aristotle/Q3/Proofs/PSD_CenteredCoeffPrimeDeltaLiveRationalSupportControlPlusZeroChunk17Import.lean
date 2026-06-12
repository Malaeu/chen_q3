import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
zero-off-declared support facts, index chunk 17: 17..17.
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


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx17_of_delta_le_m17
    {δInt : Int}
    (hδle : δInt ≤ (-17 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex17
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-17 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17) ≤ (((-17 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-17 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17) / controlK9Ell) ≤ ((((-17 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((-17 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17 ≤ ((73 : Real) / 20) := by
          change (((5 : Nat) : Real) * ((693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((73 : Real) / 20)
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((-17 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17) ≤ ((((-17 : Int) : Real) / 4) + ((73 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-17 : Int) : Real) / 4)
        have hdiv_bound : ((((-17 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex17) / ((3 : Real) / 10)) ≤ (((((-17 : Int) : Real) / 4) + ((73 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx17_of_m11_le_delta
    {δInt : Int}
    (hδge : (-11 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex17
    (by
      have hδreal : ((-11 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-11 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex17) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex17) := by
        have hdiv : (((-11 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex17)
      have hmono : ((((-11 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex17) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex17) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((-11 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex17) / controlK9Ell) := by
        have hshift : ((67 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex17 := by
          change ((67 : Real) / 20) ≤ (((5 : Nat) : Real) * ((693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-11 : Int) : Real) / 4) + ((67 : Real) / 20)) ≤ (((-11 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex17) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-11 : Int) : Real) / 4)
        have hdiv_bound : (((((-11 : Int) : Real) / 4) + ((67 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-11 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex17) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRPlusZeroOffDeclared_idx17
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex17.1 ∉ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (-17 : Int)
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx17_of_delta_le_m17 hleft
  by_cases hright : (-11 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx17_of_m11_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-16 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-12 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
