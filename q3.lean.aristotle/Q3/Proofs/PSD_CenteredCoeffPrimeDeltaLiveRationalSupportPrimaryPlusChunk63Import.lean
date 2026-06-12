import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 63: 63..63.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift63 :
    |centeredBSplineR 11
        (((((-22 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex63) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-22 : Int) 63| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-22 : Int) 63 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift63 : Rat := ((-66277996445760351558764396067391682761530057004054152951283918697834524612818584404742129468059 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift63 : Rat := ((-11046332740960058593127399344565280460255009500675692158547319782972420768803097400790354911343 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-22 : Int) activeL3RatWeightIndex63
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift63 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex63) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift63 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p229) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift63, activeL3RatLogLo_p229, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift63 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex63) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift63 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p229) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift63, activeL3RatLogHi_p229, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift63 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift63 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift63 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift63 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 63| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 63 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-22 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex63) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift63)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift63)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 63)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 63)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift63 :
    |centeredBSplineR 11
        (((((-21 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex63) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-21 : Int) 63| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-21 : Int) 63 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift63 : Rat := ((61240667851413216147078534644202772412823314331981949016238693767388491795727138531752623510647 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift63 : Rat := ((91861001777119824220617801966304158619234971497972923524358040651082737693590707797628935265971 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex63
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift63 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex63) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift63 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p229) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift63, activeL3RatLogLo_p229, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift63 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex63) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift63 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p229) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift63, activeL3RatLogHi_p229, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift63 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift63 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift63 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift63 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 63| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 63 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-21 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex63) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift63)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift63)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 63)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 63)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift63 :
    |centeredBSplineR 11
        (((((-20 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex63) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-20 : Int) 63| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-20 : Int) 63 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift63 : Rat := ((433722003554239648441235603932608317238469942995945847048716081302165475387181415595257870531941 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift63 : Rat := ((216861001777119824220617801966304158619234971497972923524358040651082737693590707797628935265971 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex63
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift63 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex63) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift63 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p229) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift63, activeL3RatLogLo_p229, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift63 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex63) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift63 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p229) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift63, activeL3RatLogHi_p229, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift63 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift63 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift63 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift63 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 63| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 63 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-20 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex63) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift63)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift63)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 63)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 63)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx63
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex63) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 63| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 63 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift63
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift63
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift63
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex63.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
