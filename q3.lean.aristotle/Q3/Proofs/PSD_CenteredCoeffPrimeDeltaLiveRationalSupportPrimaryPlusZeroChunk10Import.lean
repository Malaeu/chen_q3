import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
zero-off-declared support facts, index chunk 10: 10..10.
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


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx10_of_delta_le_m14
    {δInt : Int}
    (hδle : δInt ≤ (-14 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex10
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-14 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10) ≤ (((-14 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-14 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10) / primaryK11Ell) ≤ ((((-14 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((-14 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10 ≤ ((58 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((2833213344056216080249534617873126535588203012585744787297237737882292575800931280912094868037503 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((58 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((-14 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10) ≤ ((((-14 : Int) : Real) / 4) + ((58 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-14 : Int) : Real) / 4)
        have hdiv_bound : ((((-14 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex10) / ((3 : Real) / 10)) ≤ (((((-14 : Int) : Real) / 4) + ((58 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx10_of_m8_le_delta
    {δInt : Int}
    (hδge : (-8 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex10
    (by
      have hδreal : ((-8 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-8 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex10) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex10) := by
        have hdiv : (((-8 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex10)
      have hmono : ((((-8 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex10) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex10) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((-8 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex10) / primaryK11Ell) := by
        have hshift : ((52 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex10 := by
          change ((52 : Real) / 20) ≤ (((1 : Nat) : Real) * ((2833213344056216080249534617873126535588203012585744787297237737882292575800931280912094868037502 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-8 : Int) : Real) / 4) + ((52 : Real) / 20)) ≤ (((-8 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex10) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-8 : Int) : Real) / 4)
        have hdiv_bound : (((((-8 : Int) : Real) / 4) + ((52 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-8 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex10) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRPlusZeroOffDeclared_idx10
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex10.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (-14 : Int)
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx10_of_delta_le_m14 hleft
  by_cases hright : (-8 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx10_of_m8_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-13 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-9 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
