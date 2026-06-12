import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
zero-off-declared support facts, index chunk 1: 1..1.
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


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx1_of_delta_le_m7
    {δInt : Int}
    (hδle : δInt ≤ (-7 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex1
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((-7 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1) ≤ (((-7 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((-7 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1)
      have hmono : ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1) / primaryK11Ell) ≤ ((((-7 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((-7 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1 ≤ ((23 : Real) / 20) := by
          change (((1 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))) ≤ ((23 : Real) / 20)
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((-7 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1) ≤ ((((-7 : Int) : Real) / 4) + ((23 : Real) / 20)) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-7 : Int) : Real) / 4)
        have hdiv_bound : ((((-7 : Int) : Real) / 4 + activeL3RationalPrimeShiftUpper activeL3RatWeightIndex1) / ((3 : Real) / 10)) ≤ (((((-7 : Int) : Real) / 4) + ((23 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx1_of_m1_le_delta
    {δInt : Int}
    (hδge : (-1 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex1
    (by
      have hδreal : ((-1 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-1 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex1) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex1) := by
        have hdiv : (((-1 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex1)
      have hmono : ((((-1 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex1) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex1) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((-1 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex1) / primaryK11Ell) := by
        have hshift : ((17 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex1 := by
          change ((17 : Real) / 20) ≤ (((1 : Nat) : Real) * ((1098612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813732 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-1 : Int) : Real) / 4) + ((17 : Real) / 20)) ≤ (((-1 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex1) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-1 : Int) : Real) / 4)
        have hdiv_bound : (((((-1 : Int) : Real) / 4) + ((17 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-1 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex1) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRPlusZeroOffDeclared_idx1
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex1.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (-7 : Int)
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx1_of_delta_le_m7 hleft
  by_cases hright : (-1 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx1_of_m1_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (-6 : Int) ≤ δInt := by omega
  have hrightGap : δInt ≤ (-2 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
