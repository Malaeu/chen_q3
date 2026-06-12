import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
zero-off-declared support facts, index chunk 31: 31..31.
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


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx31_of_delta_le_m20
    {δInt : Int}
    (hδle : δInt ≤ (-20 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex31) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex31
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-20 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31) ≤ (((-20 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-20 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31) / controlK9Ell) ≤ ((((-20 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((-20 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31 ≤ ((88 : Real) / 20) := by
          change (((4 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((88 : Real) / 20)
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((-20 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31) ≤ ((((-20 : Int) : Real) / 4) + ((88 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-20 : Int) : Real) / 4)
        have hdiv_bound : ((((-20 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex31) / ((3 : Real) / 10)) ≤ (((((-20 : Int) : Real) / 4) + ((88 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx31_of_m15_le_delta
    {δInt : Int}
    (hδge : (-15 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex31) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex31
    (by
      have hδreal : ((-15 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex31) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex31) := by
        have hdiv : (((-15 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex31)
      have hmono : ((((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex31) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex31) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex31) / controlK9Ell) := by
        have hshift : ((87 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex31 := by
          change ((87 : Real) / 20) ≤ (((4 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813732 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-15 : Int) : Real) / 4) + ((87 : Real) / 20)) ≤ (((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex31) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-15 : Int) : Real) / 4)
        have hdiv_bound : (((((-15 : Int) : Real) / 4) + ((87 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex31) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRPlusZeroOffDeclared_idx31
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex31.1 ∉ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex31) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (-20 : Int)
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx31_of_delta_le_m20 hleft
  by_cases hright : (-15 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx31_of_m15_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-19 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-16 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
