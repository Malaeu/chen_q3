import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
zero-off-declared support facts, index chunk 37: 37..37.
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


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx37_of_delta_le_m22
    {δInt : Int}
    (hδle : δInt ≤ (-22 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex37) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex37
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-22 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37) ≤ (((-22 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-22 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37) / primaryK11Ell) ≤ ((((-22 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((-22 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37 ≤ ((98 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((4672828834461906173304398817023277001563146276131407553560116719246717369529992656557318703501611 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((98 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((-22 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37) ≤ ((((-22 : Int) : Real) / 4) + ((98 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-22 : Int) : Real) / 4)
        have hdiv_bound : ((((-22 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex37) / ((3 : Real) / 10)) ≤ (((((-22 : Int) : Real) / 4) + ((98 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx37_of_m16_le_delta
    {δInt : Int}
    (hδge : (-16 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex37) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex37
    (by
      have hδreal : ((-16 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex37) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex37) := by
        have hdiv : (((-16 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex37)
      have hmono : ((((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex37) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex37) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex37) / primaryK11Ell) := by
        have hshift : ((92 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex37 := by
          change ((92 : Real) / 20) ≤ (((1 : Nat) : Real) * ((4672828834461906173304398817023277001563146276131407553560116719246717369529992656557318703501610 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-16 : Int) : Real) / 4) + ((92 : Real) / 20)) ≤ (((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex37) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-16 : Int) : Real) / 4)
        have hdiv_bound : (((((-16 : Int) : Real) / 4) + ((92 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-16 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex37) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRPlusZeroOffDeclared_idx37
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex37.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex37) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (-22 : Int)
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx37_of_delta_le_m22 hleft
  by_cases hright : (-16 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx37_of_m16_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-21 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-17 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
