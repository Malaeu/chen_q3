import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
zero-off-declared support facts, index chunk 82: 82..82.
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


private theorem primaryK11RationalDeltaLiveRMinus_eq_zero_idx82_of_delta_le_p20
    {δInt : Int}
    (hδle : δInt ≤ (20 : Int)) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex82) / primaryK11Ell) = 0 := by
  exact primaryK11RationalDeltaLiveRMinus_eq_zero_of_upper_le_neg_two
    δInt activeL3RatWeightIndex82
    (by
      have hδreal : ((δInt : Int) : Real) ≤ ((20 : Int) : Real) := by exact_mod_cast hδle
      have hnum : (((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex82) ≤ (((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex82) := by
        have hdiv : (((δInt : Int) : Real) / 4) ≤ (((20 : Int) : Real) / 4) := by
          exact div_le_div_of_nonneg_right hδreal (by norm_num)
        exact sub_le_sub_right hdiv _
      have hmono : ((((δInt : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex82) / primaryK11Ell) ≤ ((((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex82) / primaryK11Ell) := by
        exact div_le_div_of_nonneg_right hnum (le_of_lt primaryK11_hell)
      have hbound : ((((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex82) / primaryK11Ell) ≤ (-2 : Real) := by
        have hshift : ((112 : Real) / 20) ≤ activeL3RationalPrimeShiftLower activeL3RatWeightIndex82 := by
          change ((112 : Real) / 20) ≤ (((1 : Nat) : Real) * ((5758901773877280614199762169298611309377583164687073399737159802452205530409276863243777225266114 : Real) / (1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)))
          norm_num
        have hell_eq : primaryK11Ell = (3 : Real) / 10 := by
          norm_num [primaryK11Ell, primaryK11EllRat]
        rw [hell_eq]
        have hnum_bound : (((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex82) ≤ ((((20 : Int) : Real) / 4) - ((112 : Real) / 20)) := by
          exact sub_le_sub_left hshift (((20 : Int) : Real) / 4)
        have hdiv_bound : ((((20 : Int) : Real) / 4 - activeL3RationalPrimeShiftLower activeL3RatWeightIndex82) / ((3 : Real) / 10)) ≤ (((((20 : Int) : Real) / 4) - ((112 : Real) / 20)) / ((3 : Real) / 10)) := by
          exact div_le_div_of_nonneg_right hnum_bound (by norm_num)
        exact le_trans hdiv_bound (by norm_num)
      exact le_trans hmono hbound)

theorem primaryK11RationalDeltaLiveRMinusZeroOffDeclared_idx82
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hnot : activeL3RatWeightIndex82.1 ∉ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex82) / primaryK11Ell) = 0 := by
  by_cases hleft : δInt ≤ (20 : Int)
  · exact primaryK11RationalDeltaLiveRMinus_eq_zero_idx82_of_delta_le_p20 hleft
  exfalso
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  have hleftGap : (21 : Int) ≤ δInt := by omega
  interval_cases δInt <;> exact hnot (by native_decide)

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
