import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 49: 49..49.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift49 :
    |centeredBSplineR 9
        (((((18 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (18 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (18 : Int) 49 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p18_shift49 : Rat := ((-556245805348308057424445236403475248742243630863650355928185997731725548400121617821509762527229 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p18_shift49 : Rat := ((-139061451337077014356111309100868812185560907715912588982046499432931387100030404455377440631807 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex49
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift49 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift49 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p18_shift49, activeL3RatLogHi_p157, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift49 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift49 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p18_shift49, activeL3RatLogLo_p157, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift49 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift49 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 49 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((18 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p18_shift49)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p18_shift49)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 49)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 49)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift49 :
    |centeredBSplineR 9
        (((((19 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (19 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (19 : Int) 49 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p19_shift49 : Rat := ((-306245805348308057424445236403475248742243630863650355928185997731725548400121617821509762527229 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p19_shift49 : Rat := ((-25520483779025671452037103033622937395186969238637529660682166477643795700010134818459146877269 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex49
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift49 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift49 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p19_shift49, activeL3RatLogHi_p157, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift49 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift49 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p19_shift49, activeL3RatLogLo_p157, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift49 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift49 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 49 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((19 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p19_shift49)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p19_shift49)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 49)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 49)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift49 :
    |centeredBSplineR 9
        (((((20 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (20 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (20 : Int) 49 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p20_shift49 : Rat := ((-18748601782769352474815078801158416247414543621216785309395332577241849466707205940503254175743 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p20_shift49 : Rat := ((-14061451337077014356111309100868812185560907715912588982046499432931387100030404455377440631807 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex49
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift49 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift49 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p20_shift49, activeL3RatLogHi_p157, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift49 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift49 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p20_shift49, activeL3RatLogLo_p157, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift49 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift49 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 49 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((20 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p20_shift49)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p20_shift49)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 49)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 49)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift49 :
    |centeredBSplineR 9
        (((((21 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (21 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (21 : Int) 49 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p21_shift49 : Rat := ((193754194651691942575554763596524751257756369136349644071814002268274451599878382178490237472771 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p21_shift49 : Rat := ((48438548662922985643888690899131187814439092284087411017953500567068612899969595544622559368193 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex49
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift49 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift49 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p21_shift49, activeL3RatLogHi_p157, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift49 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift49 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p21_shift49, activeL3RatLogLo_p157, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift49 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift49 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 49 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((21 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p21_shift49)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p21_shift49)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 49)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 49)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift49 :
    |centeredBSplineR 9
        (((((22 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (22 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (22 : Int) 49 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p22_shift49 : Rat := ((443754194651691942575554763596524751257756369136349644071814002268274451599878382178490237472771 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p22_shift49 : Rat := ((36979516220974328547962896966377062604813030761362470339317833522356204299989865181540853122731 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (22 : Int) activeL3RatWeightIndex49
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift49 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift49 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p22_shift49, activeL3RatLogHi_p157, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift49 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex49) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift49 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p157) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p22_shift49, activeL3RatLogLo_p157, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift49 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift49 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift49 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 49| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 49 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((22 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p22_shift49)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p22_shift49)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 49)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 49)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx49
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex49) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 49| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 49 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex49.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift49
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift49
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift49
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift49
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift49

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
