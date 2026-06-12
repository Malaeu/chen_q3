import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 9: 9..9.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift9 :
    |centeredBSplineR 9
        (((((-13 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-13 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-13 : Int) 9 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m13_shift9 : Rat := ((-59676409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m13_shift9 : Rat := ((-119352819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift9 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift9 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m13_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift9 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift9 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m13_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift9 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-13 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m13_shift9)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m13_shift9)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 9)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift9 :
    |centeredBSplineR 9
        (((((-12 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-12 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-12 : Int) 9 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m12_shift9 : Rat := ((-28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m12_shift9 : Rat := ((-18950939813351563527589292847274477308166621879914915293106663502202126010101761464712224334527 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-12 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift9 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift9 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m12_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift9 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift9 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m12_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift9 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-12 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m12_shift9)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m12_shift9)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 9)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift9 :
    |centeredBSplineR 9
        (((((-11 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-11 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-11 : Int) 9 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m11_shift9 : Rat := ((941196759990884902872020243029428012583355726709209020113334915565603661615785934310554499403 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m11_shift9 : Rat := ((5647180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-11 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift9 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift9 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m11_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift9 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift9 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m11_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift9 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-11 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m11_shift9)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m11_shift9)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 9)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift9 :
    |centeredBSplineR 9
        (((((-10 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-10 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-10 : Int) 9 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m10_shift9 : Rat := ((34073590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m10_shift9 : Rat := ((68147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-10 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift9 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift9 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m10_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift9 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift9 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m10_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift9 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-10 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m10_shift9)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m10_shift9)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 9)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m9_shift9 :
    |centeredBSplineR 9
        (((((-9 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-9 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-9 : Int) 9 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m9_shift9 : Rat := ((65323590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m9_shift9 : Rat := ((43549060186648436472410707152725522691833378120085084706893336497797873989898238535287775665473 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-9 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m9_shift9 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m9_shift9 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m9_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m9_shift9 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m9_shift9 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m9_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m9_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m9_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m9_shift9 controlK9RationalDeltaLiveRPlusHi_delta_m9_shift9 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 9| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-9 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m9_shift9)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m9_shift9)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 9)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx9
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 9| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 9 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift9
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift9
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift9
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift9
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m9_shift9
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
