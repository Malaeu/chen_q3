import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 3: 3..3.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p5_shift3 :
    |centeredBSplineR 9
        (((((5 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (5 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (5 : Int) 3 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p5_shift3 : Rat := ((-17971895621705018730037966661309381976280067713425886095632394573708949385382888231506693904659 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p5_shift3 : Rat := ((-119812637478033458200253111075395879841867118089505907304215963824726329235885921543377959364393 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (5 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p5_shift3 : Rat) : Real) =
            ((((5 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p5_shift3 : Rat) : Real) = (((((5 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p5_shift3, activeL3RatLogHi_p5, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p5_shift3 : Rat) : Real) =
            ((((5 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p5_shift3 : Rat) : Real) = (((((5 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p5_shift3, activeL3RatLogLo_p5, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p5_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p5_shift3 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p5_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p5_shift3 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (5 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (5 : Int) 3 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((5 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p5_shift3)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p5_shift3)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (5 : Int) 3)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (5 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p6_shift3 :
    |centeredBSplineR 9
        (((((6 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (6 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (6 : Int) 3 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p6_shift3 : Rat := ((-1823965207235006243345988887103127325426689237808628698544131524569649795127629410502231301553 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p6_shift3 : Rat := ((-109437912434100374600759333226187639525601354268517721912647891474178987707657764630133878093179 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (6 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p6_shift3 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p6_shift3 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p6_shift3, activeL3RatLogHi_p5, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p6_shift3 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p6_shift3 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p6_shift3, activeL3RatLogLo_p5, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p6_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p6_shift3 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p6_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p6_shift3 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 3 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((6 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p6_shift3)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p6_shift3)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 3)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p7_shift3 :
    |centeredBSplineR 9
        (((((7 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (7 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (7 : Int) 3 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p7_shift3 : Rat := ((7028104378294981269962033338690618023719932286574113904367605426291050614617111768493306095341 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p7_shift3 : Rat := ((140562087565899625399240666773812360474398645731482278087352108525821012292342235369866121906821 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (7 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p7_shift3 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p7_shift3 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p7_shift3, activeL3RatLogHi_p5, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p7_shift3 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p7_shift3 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p7_shift3, activeL3RatLogLo_p5, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p7_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p7_shift3 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p7_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p7_shift3 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 3 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((7 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p7_shift3)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p7_shift3)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 3)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p8_shift3 :
    |centeredBSplineR 9
        (((((8 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (8 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (8 : Int) 3 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p8_shift3 : Rat := ((19528104378294981269962033338690618023719932286574113904367605426291050614617111768493306095341 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p8_shift3 : Rat := ((130187362521966541799746888924604120158132881910494092695784036175273670764114078456622040635607 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (8 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p8_shift3 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p8_shift3 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p8_shift3, activeL3RatLogHi_p5, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p8_shift3 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p8_shift3 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p5) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p8_shift3, activeL3RatLogLo_p5, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p8_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p8_shift3 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p8_shift3 controlK9RationalDeltaLiveRMinusHi_delta_p8_shift3 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 3| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 3 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((8 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p8_shift3)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p8_shift3)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 3)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx3
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex3) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 3| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 3 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p5_shift3
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p6_shift3
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p7_shift3
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p8_shift3
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
