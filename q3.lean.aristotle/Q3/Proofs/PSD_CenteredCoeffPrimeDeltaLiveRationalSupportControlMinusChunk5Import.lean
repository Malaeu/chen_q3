import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 5: 5..5.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p6_shift5 :
    |centeredBSplineR 9
        (((((6 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (6 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (6 : Int) 5 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p6_shift5 : Rat := ((-193147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p6_shift5 : Rat := ((-96573590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (6 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p6_shift5 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p6_shift5 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p6_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p6_shift5 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p6_shift5 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p6_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p6_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p6_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p6_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p6_shift5 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((6 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p6_shift5)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p6_shift5)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 5)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p7_shift5 :
    |centeredBSplineR 9
        (((((7 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (7 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (7 : Int) 5 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p7_shift5 : Rat := ((-329441541679835928251696364374529704226500403080765762362040028480180865909084146817589980989257 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p7_shift5 : Rat := ((-164720770839917964125848182187264852113250201540382881181020014240090432954542073408794990494627 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (7 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p7_shift5 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p7_shift5 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p7_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p7_shift5 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p7_shift5 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p7_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p7_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p7_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p7_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p7_shift5 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((7 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p7_shift5)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p7_shift5)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 5)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p8_shift5 :
    |centeredBSplineR 9
        (((((8 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (8 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (8 : Int) 5 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p8_shift5 : Rat := ((-79441541679835928251696364374529704226500403080765762362040028480180865909084146817589980989257 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p8_shift5 : Rat := ((-39720770839917964125848182187264852113250201540382881181020014240090432954542073408794990494627 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (8 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p8_shift5 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p8_shift5 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p8_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p8_shift5 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p8_shift5 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p8_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p8_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p8_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p8_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p8_shift5 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((8 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p8_shift5)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p8_shift5)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 5)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p9_shift5 :
    |centeredBSplineR 9
        (((((9 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (9 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (9 : Int) 5 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p9_shift5 : Rat := ((56852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p9_shift5 : Rat := ((28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (9 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p9_shift5 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p9_shift5 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p9_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p9_shift5 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p9_shift5 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p9_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p9_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p9_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p9_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p9_shift5 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((9 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p9_shift5)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p9_shift5)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 5)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p10_shift5 :
    |centeredBSplineR 9
        (((((10 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (10 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (10 : Int) 5 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p10_shift5 : Rat := ((420558458320164071748303635625470295773499596919234237637959971519819134090915853182410019010743 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p10_shift5 : Rat := ((210279229160082035874151817812735147886749798459617118818979985759909567045457926591205009505373 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (10 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p10_shift5 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p10_shift5 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p10_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p10_shift5 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p10_shift5 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p10_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p10_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p10_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p10_shift5 controlK9RationalDeltaLiveRMinusHi_delta_p10_shift5 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 5| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((10 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p10_shift5)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p10_shift5)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 5)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx5
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 5| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 5 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p6_shift5
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p7_shift5
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p8_shift5
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p9_shift5
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p10_shift5
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
