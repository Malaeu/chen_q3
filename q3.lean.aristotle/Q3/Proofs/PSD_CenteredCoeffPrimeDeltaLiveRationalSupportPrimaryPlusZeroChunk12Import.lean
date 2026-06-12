import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
zero-off-declared support facts, index chunk 12: 12..12.
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


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx12_of_delta_le_m15
    {δInt : Int}
    (hδle : δInt ≤ (-15 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex12) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex12
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-15 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12) ≤ (((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-15 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12) / primaryK11Ell) ≤ ((((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12 ≤ ((63 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((3135494215929149690806752831810196118442380314840435741998635377482993245984798298198401092152995 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((63 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12) ≤ ((((-15 : Int) : Real) / 4) + ((63 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-15 : Int) : Real) / 4)
        have hdiv_bound : ((((-15 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex12) / ((3 : Real) / 10)) ≤ (((((-15 : Int) : Real) / 4) + ((63 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx12_of_m10_le_delta
    {δInt : Int}
    (hδge : (-10 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex12) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex12
    (by
      have hδreal : ((-10 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex12) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex12) := by
        have hdiv : (((-10 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex12)
      have hmono : ((((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex12) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex12) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex12) / primaryK11Ell) := by
        have hshift : ((62 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex12 := by
          change ((62 : Real) / 20) ≤ (((1 : Nat) : Real) * ((3135494215929149690806752831810196118442380314840435741998635377482993245984798298198401092152994 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-10 : Int) : Real) / 4) + ((62 : Real) / 20)) ≤ (((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex12) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-10 : Int) : Real) / 4)
        have hdiv_bound : (((((-10 : Int) : Real) / 4) + ((62 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-10 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex12) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRPlusZeroOffDeclared_idx12
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex12.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex12) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (-15 : Int)
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx12_of_delta_le_m15 hleft
  by_cases hright : (-10 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx12_of_m10_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-14 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-11 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
