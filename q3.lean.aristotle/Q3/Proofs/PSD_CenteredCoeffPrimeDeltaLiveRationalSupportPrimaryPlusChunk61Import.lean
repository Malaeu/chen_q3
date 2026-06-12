import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 61: 61..61.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift61 :
    |centeredBSplineR 11
        (((((-22 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex61) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-22 : Int) 61| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-22 : Int) 61 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift61 : Rat := ((-6188548569325416090926319351790664886758115035267545125975175826790914837600871257839606586617 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift61 : Rat := ((-46414114269940620681947395138429986650685862764506588444813818700931861282006534433797049399627 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-22 : Int) activeL3RatWeightIndex61
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift61 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex61) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift61 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p223) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift61, activeL3RatLogLo_p223, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift61 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex61) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift61 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p223) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift61, activeL3RatLogHi_p223, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift61 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift61 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift61 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift61 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 61| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 61 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-22 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex61) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift61)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift61)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 61)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 61)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift61 :
    |centeredBSplineR 11
        (((((-21 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex61) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-21 : Int) 61| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-21 : Int) 61 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift61 : Rat := ((31434354292023751727221041944628005339725654894197364622074472519627255487197386226481180240149 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift61 : Rat := ((78585885730059379318052604861570013349314137235493411555186181299068138717993465566202950600373 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex61
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift61 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex61) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift61 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p223) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift61, activeL3RatLogLo_p223, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift61 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex61) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift61 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p223) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift61, activeL3RatLogHi_p223, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift61 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift61 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift61 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift61 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 61| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 61 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-21 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex61) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift61)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift61)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 61)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 61)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift61 :
    |centeredBSplineR 11
        (((((-20 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex61) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-20 : Int) 61| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-20 : Int) 61 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift61 : Rat := ((81434354292023751727221041944628005339725654894197364622074472519627255487197386226481180240149 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift61 : Rat := ((67861961910019793106017534953856671116438045745164470518395393766356046239331155188734316866791 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex61
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift61 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex61) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift61 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p223) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift61, activeL3RatLogLo_p223, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift61 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex61) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift61 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p223) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift61, activeL3RatLogHi_p223, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift61 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift61 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift61 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift61 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 61| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 61 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-20 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex61) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift61)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift61)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 61)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 61)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx61
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex61) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 61| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 61 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift61
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift61
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift61
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex61.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
