import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 14: 14..14.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift14 :
    |centeredBSplineR 9
        (((((-15 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-15 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-15 : Int) 14 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m15_shift14 : Rat := ((-37846927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m15_shift14 : Rat := ((-151387711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift14 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift14 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m15_shift14, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift14 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift14 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m15_shift14, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift14 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift14 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 14 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-15 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m15_shift14)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m15_shift14)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 14)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift14 :
    |centeredBSplineR 9
        (((((-14 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-14 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-14 : Int) 14 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m14_shift14 : Rat := ((-51040783498917731453566072308105721514382081632937911198979249771879280086043274844788183889701 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m14_shift14 : Rat := ((-204163133995670925814264289232422886057528326531751644795916999087517120344173099379152735558801 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift14 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift14 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m14_shift14, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift14 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift14 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m14_shift14, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift14 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift14 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 14 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-14 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m14_shift14)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m14_shift14)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 14)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift14 :
    |centeredBSplineR 9
        (((((-13 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-13 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-13 : Int) 14 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m13_shift14 : Rat := ((11459216501082268546433927691894278485617918367062088801020750228120719913956725155211816110299 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m13_shift14 : Rat := ((45836866004329074185735710767577113942471673468248355204083000912482879655826900620847264441199 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift14 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift14 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m13_shift14, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift14 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift14 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m13_shift14, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift14 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift14 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 14 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-13 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m13_shift14)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m13_shift14)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 14)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift14 :
    |centeredBSplineR 9
        (((((-12 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-12 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-12 : Int) 14 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m12_shift14 : Rat := ((24653072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m12_shift14 : Rat := ((98612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-12 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift14 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift14 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m12_shift14, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift14 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift14 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m12_shift14, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift14 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift14 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 14 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-12 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m12_shift14)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m12_shift14)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 14)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift14 :
    |centeredBSplineR 9
        (((((-11 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-11 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-11 : Int) 14 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m11_shift14 : Rat := ((136459216501082268546433927691894278485617918367062088801020750228120719913956725155211816110299 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m11_shift14 : Rat := ((545836866004329074185735710767577113942471673468248355204083000912482879655826900620847264441199 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-11 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift14 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift14 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m11_shift14, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift14 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift14 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m11_shift14, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift14 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift14 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift14 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 14| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 14 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-11 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m11_shift14)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m11_shift14)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 14)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx14
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex14) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 14| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 14 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift14
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift14
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift14
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift14
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift14
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
