import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p9_shift9 :
    |centeredBSplineR 9
        (((((9 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (9 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (9 : Int) 9 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p9_shift9 : Rat := ((-43549060186648436472410707152725522691833378120085084706893336497797873989898238535287775665473 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p9_shift9 : Rat := ((-65323590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (9 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p9_shift9 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p9_shift9 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p9_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p9_shift9 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p9_shift9 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p9_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p9_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p9_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p9_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p9_shift9 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((9 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p9_shift9)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p9_shift9)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 9)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p10_shift9 :
    |centeredBSplineR 9
        (((((10 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (10 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (10 : Int) 9 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p10_shift9 : Rat := ((-68147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p10_shift9 : Rat := ((-34073590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (10 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p10_shift9 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p10_shift9 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p10_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p10_shift9 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p10_shift9 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p10_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p10_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p10_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p10_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p10_shift9 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((10 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p10_shift9)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p10_shift9)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 9)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p11_shift9 :
    |centeredBSplineR 9
        (((((11 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (11 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (11 : Int) 9 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p11_shift9 : Rat := ((-5647180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p11_shift9 : Rat := ((-941196759990884902872020243029428012583355726709209020113334915565603661615785934310554499403 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (11 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p11_shift9 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p11_shift9 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p11_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p11_shift9 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p11_shift9 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p11_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p11_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p11_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p11_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p11_shift9 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((11 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p11_shift9)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p11_shift9)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 9)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p12_shift9 :
    |centeredBSplineR 9
        (((((12 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (12 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (12 : Int) 9 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p12_shift9 : Rat := ((18950939813351563527589292847274477308166621879914915293106663502202126010101761464712224334527 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p12_shift9 : Rat := ((28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (12 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p12_shift9 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p12_shift9 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p12_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p12_shift9 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p12_shift9 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p12_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p12_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p12_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p12_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p12_shift9 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((12 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p12_shift9)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p12_shift9)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 9)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift9 :
    |centeredBSplineR 9
        (((((13 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (13 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (13 : Int) 9 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p13_shift9 : Rat := ((119352819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p13_shift9 : Rat := ((59676409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (13 : Int) activeL3RatWeightIndex9
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift9 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift9 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p13_shift9, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift9 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex9) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift9 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((4 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p13_shift9, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift9 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift9 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift9 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 9| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 9 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((13 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p13_shift9)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p13_shift9)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 9)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 9)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx9
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex9) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 9| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 9 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p9_shift9
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p10_shift9
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p11_shift9
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p12_shift9
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift9
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex9.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
