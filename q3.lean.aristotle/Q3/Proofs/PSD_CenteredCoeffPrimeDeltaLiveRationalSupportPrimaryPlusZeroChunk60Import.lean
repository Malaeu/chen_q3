import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
zero-off-declared support facts, index chunk 60: 60..60.
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


private theorem primaryK11RationalDeltaLiveRPlus_eq_zero_idx60_of_m19_le_delta
    {δInt : Int}
    (hδge : (-19 : Int) ≤ δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex60) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRPlus_eq_zero_of_two_le_lower
    δInt activeL3RatWeightIndex60
    (by
      have hδreal : ((-19 : Int) : Real) ≤ ((δInt : Int) : Real) := by exact_mod_cast hδge
      have hnum : (((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex60) ≤ (((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex60) := by
        have hdiv : (((-19 : Int) : Real) / 4) ≤ (((δInt : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdiv (activeL3RationalPrimeShiftLower activeL3RatWeightIndex60)
      have hmono : ((((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex60) / primaryK11Ell) ≤ ((((δInt : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex60) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : (2 : Real) ≤ ((((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex60) / primaryK11Ell) := by
        have hshift : ((107 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex60 := by
          change ((107 : Real) / 20) ≤ (((1 : Nat) : Real) * ((5351858133476066495741956265454280118041158173581668370687778799606135752960928683123887335392390 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : ((((-19 : Int) : Real) / 4) + ((107 : Real) / 20)) ≤ (((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex60) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hshift (((-19 : Int) : Real) / 4)
        have hdiv_bound : (((((-19 : Int) : Real) / 4) + ((107 : Real) / 20)) / ((3 : Real) / 10)) ≤ ((((-19 : Int) : Real) / 4 + activeL3RationalPrimeShiftLower activeL3RatWeightIndex60) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans (by norm_num) hdiv_bound
      exact le_trans hbound hmono)

theorem primaryK11RationalDeltaLiveRPlusZeroOffDeclared_idx60
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex60.1 ∉ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex60) / primaryK11Ell) = 0 := by
  by_cases hright : (-19 : Int) ≤ δInt
  · exact primaryK11RationalDeltaLiveRPlus_eq_zero_idx60_of_m19_le_delta hright
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hrightGap : δInt ≤ (-20 : Int) := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
