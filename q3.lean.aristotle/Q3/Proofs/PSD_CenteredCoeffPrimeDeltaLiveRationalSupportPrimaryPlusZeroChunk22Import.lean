import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
zero-off-declared support facts, index chunk 22: 22..22.
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


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx22_of_delta_le_m18
    {δInt : Int}
    (hδle : δInt ≤ (-18 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex22
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-18 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) ≤ (((-18 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-18 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / primaryK11Ell) ≤ ((((-18 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((-18 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22 ≤ ((78 : Real) / 20) := by
          change (((2 : Nat) : Real) * ((1945910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587872 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((78 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((-18 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) ≤ ((((-18 : Int) : Real) / 4) + ((78 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-18 : Int) : Real) / 4)
        have hdiv_bound : ((((-18 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex22) / ((3 : Real) / 10)) ≤ (((((-18 : Int) : Real) / 4) + ((78 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx22_of_m13_le_delta
    {δInt : Int}
    (hδge : (-13 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex22
    (by
      have hδreal : ((-13 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-13 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) := by
        have hdiv : (((-13 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex22)
      have hmono : ((((-13 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((-13 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / primaryK11Ell) := by
        have hshift : ((77 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex22 := by
          change ((77 : Real) / 20) ≤ (((2 : Nat) : Real) * ((1945910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587871 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-13 : Int) : Real) / 4) + ((77 : Real) / 20)) ≤ (((-13 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-13 : Int) : Real) / 4)
        have hdiv_bound : (((((-13 : Int) : Real) / 4) + ((77 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-13 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex22) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRPlusZeroOffDeclared_idx22
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex22.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (-18 : Int)
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx22_of_delta_le_m18 hleft
  by_cases hright : (-13 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx22_of_m13_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-17 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-14 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
