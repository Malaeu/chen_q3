import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift5 :
    |centeredBSplineR 9
        (((((-10 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-10 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-10 : Int) 5 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m10_shift5 : Rat := ((-210279229160082035874151817812735147886749798459617118818979985759909567045457926591205009505373 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m10_shift5 : Rat := ((-420558458320164071748303635625470295773499596919234237637959971519819134090915853182410019010743 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-10 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift5 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift5 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m10_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift5 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift5 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m10_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift5 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-10 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m10_shift5)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m10_shift5)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 5)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m9_shift5 :
    |centeredBSplineR 9
        (((((-9 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-9 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-9 : Int) 5 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m9_shift5 : Rat := ((-28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m9_shift5 : Rat := ((-56852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-9 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m9_shift5 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m9_shift5 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m9_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m9_shift5 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m9_shift5 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m9_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m9_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m9_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m9_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m9_shift5 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-9 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m9_shift5)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m9_shift5)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 5)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m8_shift5 :
    |centeredBSplineR 9
        (((((-8 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-8 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-8 : Int) 5 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m8_shift5 : Rat := ((39720770839917964125848182187264852113250201540382881181020014240090432954542073408794990494627 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m8_shift5 : Rat := ((79441541679835928251696364374529704226500403080765762362040028480180865909084146817589980989257 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-8 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m8_shift5 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m8_shift5 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m8_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m8_shift5 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m8_shift5 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m8_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m8_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m8_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m8_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m8_shift5 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-8 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m8_shift5)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m8_shift5)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 5)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m7_shift5 :
    |centeredBSplineR 9
        (((((-7 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-7 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-7 : Int) 5 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m7_shift5 : Rat := ((164720770839917964125848182187264852113250201540382881181020014240090432954542073408794990494627 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m7_shift5 : Rat := ((329441541679835928251696364374529704226500403080765762362040028480180865909084146817589980989257 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-7 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m7_shift5 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m7_shift5 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m7_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m7_shift5 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m7_shift5 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m7_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m7_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m7_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m7_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m7_shift5 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-7 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m7_shift5)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m7_shift5)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 5)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m6_shift5 :
    |centeredBSplineR 9
        (((((-6 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-6 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-6 : Int) 5 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m6_shift5 : Rat := ((96573590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m6_shift5 : Rat := ((193147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-6 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m6_shift5 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m6_shift5 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m6_shift5, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m6_shift5 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m6_shift5 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m6_shift5, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m6_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m6_shift5 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m6_shift5 controlK9RationalDeltaLiveRPlusHi_delta_m6_shift5 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 5| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 5 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-6 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m6_shift5)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m6_shift5)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 5)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx5
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex5) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 5| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 5 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift5
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m9_shift5
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m8_shift5
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m7_shift5
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m6_shift5
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
