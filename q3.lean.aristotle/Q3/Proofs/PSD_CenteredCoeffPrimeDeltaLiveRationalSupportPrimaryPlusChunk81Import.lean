import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 81: 81..81.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift81 :
    |centeredBSplineR 11
        (((((-22 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex81) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-22 : Int) 81| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-22 : Int) 81 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift81 : Rat := ((49240638108030643335753061851442070714619853667453985629672728992392588210160914072778304380077 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift81 : Rat := ((123101595270076608339382654628605176786549634168634964074181822480981470525402285181945760950193 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-22 : Int) activeL3RatWeightIndex81
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift81 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex81) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift81 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p313) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift81, activeL3RatLogLo_p313, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift81 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex81) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift81 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p313) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift81, activeL3RatLogHi_p313, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift81 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift81 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift81 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift81 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 81| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 81 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-22 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex81) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift81)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift81)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 81)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 81)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift81 :
    |centeredBSplineR 11
        (((((-21 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex81) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-21 : Int) 81| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-21 : Int) 81 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift81 : Rat := ((99240638108030643335753061851442070714619853667453985629672728992392588210160914072778304380077 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift81 : Rat := ((82700531756692202779794218209535058928849878056211654691393940826993823508467428393981920316731 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex81
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift81 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex81) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift81 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p313) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift81, activeL3RatLogLo_p313, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift81 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex81) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift81 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p313) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift81, activeL3RatLogHi_p313, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift81 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift81 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift81 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift81 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 81| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 81 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-21 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex81) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift81)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift81)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 81)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 81)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx81
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex81) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 81| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 81 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift81
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift81
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex81.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
