import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 71: 71..71.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift71 :
    |centeredBSplineR 9
        (((((20 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (20 : Int) 71| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (20 : Int) 71 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p20_shift71 : Rat := ((-114430806435552910217185252841014418077096768012913055765566566628240144351613650624013592437347 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p20_shift71 : Rat := ((-95359005362960758514321044034178681730913973344094213137972138856866786959678042186677993697789 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex71
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift71 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex71) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift71 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p263) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p20_shift71, activeL3RatLogHi_p263, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift71 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex71) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift71 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p263) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p20_shift71, activeL3RatLogLo_p263, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift71 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift71 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift71 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift71 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 71| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 71 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((20 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p20_shift71)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p20_shift71)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 71)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 71)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift71 :
    |centeredBSplineR 9
        (((((21 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (21 : Int) 71| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (21 : Int) 71 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p21_shift71 : Rat := ((-21476935478517636739061750947004806025698922670971018588522188876080048117204550208004530812449 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p21_shift71 : Rat := ((-161077016088882275542963132102536045192741920032282639413916416570600360879034126560033981093367 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex71
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift71 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex71) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift71 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p263) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p21_shift71, activeL3RatLogHi_p263, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift71 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex71) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift71 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p263) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p21_shift71, activeL3RatLogLo_p263, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift71 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift71 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift71 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift71 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 71| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 71 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((21 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p21_shift71)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p21_shift71)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 71)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 71)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift71 :
    |centeredBSplineR 9
        (((((22 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (22 : Int) 71| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (22 : Int) 71 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p22_shift71 : Rat := ((-14430806435552910217185252841014418077096768012913055765566566628240144351613650624013592437347 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p22_shift71 : Rat := ((-36077016088882275542963132102536045192741920032282639413916416570600360879034126560033981093367 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (22 : Int) activeL3RatWeightIndex71
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift71 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex71) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift71 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p263) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p22_shift71, activeL3RatLogHi_p263, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift71 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex71) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift71 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p263) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p22_shift71, activeL3RatLogLo_p263, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift71 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift71 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift71 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift71 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 71| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 71 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((22 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p22_shift71)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p22_shift71)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 71)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 71)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx71
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex71) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 71| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 71 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex71.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift71
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift71
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift71

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
