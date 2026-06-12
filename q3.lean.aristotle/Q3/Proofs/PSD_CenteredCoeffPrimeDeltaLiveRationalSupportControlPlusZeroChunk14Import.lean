import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
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


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx14_of_delta_le_m16
    {δInt : Int}
    (hδle : δInt ≤ (-16 : Int)) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex14
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-16 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) ≤ (((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-16 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / controlK9Ell) ≤ ((((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : ((((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / controlK9Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14 ≤ ((68 : Real) / 20) := by
          change (((3 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((68 : Real) / 20)
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : (((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) ≤ ((((-16 : Int) : Real) / 4) + ((68 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-16 : Int) : Real) / 4)
        have hdiv_bound : ((((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex14) / ((3 : Real) / 10)) ≤ (((((-16 : Int) : Real) / 4) + ((68 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem controlK9RationalDeltaLiveRPlus_eq_zero_idx14_of_m10_le_delta
    {δInt : Int}
    (hδge : (-10 : Int) ≤ δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell) = 0 := by
  exact controlK9RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex14
    (by
      have hδreal : ((-10 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) := by
        have hdiv : (((-10 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex14)
      have hmono : ((((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / controlK9Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / controlK9Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt controlK9_hell)
      have hbound : (2 : Real) ≤ ((((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / controlK9Ell) := by
        have hshift : ((62 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex14 := by
          change ((62 : Real) / 20) ≤ (((3 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813732 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : controlK9Ell = (3 : Real) / 10 := by
          norm_num [controlK9Ell, controlK9EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-10 : Int) : Real) / 4) + ((62 : Real) / 20)) ≤ (((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-10 : Int) : Real) / 4)
        have hdiv_bound : (((((-10 : Int) : Real) / 4) + ((62 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex14) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem controlK9RationalDeltaLiveRPlusZeroOffDeclared_idx14
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex14.1 ∉ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell) = 0 := by
  by_cases hleft : δInt ≤ (-16 : Int)
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx14_of_delta_le_m16 hleft
  by_cases hright : (-10 : Int) ≤ δInt
  · exact controlK9RationalDeltaLiveRPlus_eq_zero_idx14_of_m10_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-15 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-11 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
