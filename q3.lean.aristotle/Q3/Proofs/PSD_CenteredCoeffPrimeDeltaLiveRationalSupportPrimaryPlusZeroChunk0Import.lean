import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
zero-off-declared support facts, index chunk 0: 0..0.
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


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx0_of_delta_le_m6
    {δInt : Int}
    (hδle : δInt ≤ (-6 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex0) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex0
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-6 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0) ≤ (((-6 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-6 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0) / primaryK11Ell) ≤ ((((-6 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((-6 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0 ≤ ((18 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((18 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((-6 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0) ≤ ((((-6 : Int) : Real) / 4) + ((18 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-6 : Int) : Real) / 4)
        have hdiv_bound : ((((-6 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex0) / ((3 : Real) / 10)) ≤ (((((-6 : Int) : Real) / 4) + ((18 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx0_of_z0_le_delta
    {δInt : Int}
    (hδge : (0 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex0) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex0
    (by
      have hδreal : ((0 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((0 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex0) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex0) := by
        have hdiv : (((0 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex0)
      have hmono : ((((0 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex0) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex0) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((0 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex0) / primaryK11Ell) := by
        have hshift : ((12 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex0 := by
          change ((12 : Real) / 20) ≤ (((1 : Nat) : Real) * ((693147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996418 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((0 : Int) : Real) / 4) + ((12 : Real) / 20)) ≤ (((0 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex0) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((0 : Int) : Real) / 4)
        have hdiv_bound : (((((0 : Int) : Real) / 4) + ((12 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((0 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex0) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRPlusZeroOffDeclared_idx0
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex0.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex0) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (-6 : Int)
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx0_of_delta_le_m6 hleft
  by_cases hright : (0 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx0_of_z0_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-5 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-1 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
