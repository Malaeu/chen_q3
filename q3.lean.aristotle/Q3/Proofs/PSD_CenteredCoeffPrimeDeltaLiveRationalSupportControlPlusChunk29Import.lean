import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 29: 29..29.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift29 :
    |centeredBSplineR 9
        (((((-19 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-19 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-19 : Int) 29 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m19_shift29 : Rat := ((-76590093141934811817981857093576238182541192521400389234050190473035004013233784453945112860857 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m19_shift29 : Rat := ((-459540558851608870907891142561457429095247155128402335404301142838210024079402706723670677165141 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex29
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift29 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift29 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m19_shift29, activeL3RatLogLo_p73, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift29 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift29 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m19_shift29, activeL3RatLogHi_p73, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift29 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift29 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 29 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-19 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m19_shift29)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m19_shift29)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 29)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 29)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift29 :
    |centeredBSplineR 9
        (((((-18 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-18 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-18 : Int) 29 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m18_shift29 : Rat := ((-104770279425804435453945571280728714547623577564201167702150571419105012039701353361835338582571 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m18_shift29 : Rat := ((-209540558851608870907891142561457429095247155128402335404301142838210024079402706723670677165141 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex29
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift29 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift29 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m18_shift29, activeL3RatLogLo_p73, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift29 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift29 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m18_shift29, activeL3RatLogHi_p73, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift29 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift29 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 29 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-18 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m18_shift29)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m18_shift29)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 29)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 29)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift29 :
    |centeredBSplineR 9
        (((((-17 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-17 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-17 : Int) 29 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m17_shift29 : Rat := ((20229720574195564546054428719271285452376422435798832297849428580894987960298646638164661417429 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m17_shift29 : Rat := ((13486480382797043030702952479514190301584281623865888198566285720596658640199097758776440944953 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex29
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift29 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift29 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m17_shift29, activeL3RatLogLo_p73, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift29 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift29 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m17_shift29, activeL3RatLogHi_p73, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift29 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift29 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 29 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-17 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m17_shift29)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m17_shift29)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 29)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 29)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift29 :
    |centeredBSplineR 9
        (((((-16 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-16 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-16 : Int) 29 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m16_shift29 : Rat := ((48409906858065188182018142906423761817458807478599610765949809526964995986766215546054887139143 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m16_shift29 : Rat := ((290459441148391129092108857438542570904752844871597664595698857161789975920597293276329322834859 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex29
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift29 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift29 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m16_shift29, activeL3RatLogLo_p73, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift29 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift29 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m16_shift29, activeL3RatLogHi_p73, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift29 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift29 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 29 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-16 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m16_shift29)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m16_shift29)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 29)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 29)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift29 :
    |centeredBSplineR 9
        (((((-15 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-15 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-15 : Int) 29 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m15_shift29 : Rat := ((270229720574195564546054428719271285452376422435798832297849428580894987960298646638164661417429 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m15_shift29 : Rat := ((540459441148391129092108857438542570904752844871597664595698857161789975920597293276329322834859 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex29
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift29 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift29 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m15_shift29, activeL3RatLogLo_p73, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift29 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex29) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift29 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p73) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m15_shift29, activeL3RatLogHi_p73, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift29 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift29 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift29 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 29| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 29 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-15 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m15_shift29)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m15_shift29)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 29)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 29)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx29
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex29) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 29| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 29 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift29
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift29
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift29
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift29
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift29
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex29.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
