import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 17: 17..17.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p12_shift17 :
    |centeredBSplineR 9
        (((((12 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (12 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (12 : Int) 17 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p12_shift17 : Rat := ((-31049060186648436472410707152725522691833378120085084706893336497797873989898238535287775665473 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p12_shift17 : Rat := ((-46573590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (12 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p12_shift17 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p12_shift17 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p12_shift17, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p12_shift17 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p12_shift17 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p12_shift17, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p12_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p12_shift17 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p12_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p12_shift17 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 17 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((12 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p12_shift17)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p12_shift17)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 17)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift17 :
    |centeredBSplineR 9
        (((((13 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (13 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (13 : Int) 17 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p13_shift17 : Rat := ((-43147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p13_shift17 : Rat := ((-7191196759990884902872020243029428012583355726709209020113334915565603661615785934310554499403 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (13 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift17 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift17 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p13_shift17, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift17 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift17 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p13_shift17, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift17 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift17 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 17 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((13 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p13_shift17)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p13_shift17)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 17)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p14_shift17 :
    |centeredBSplineR 9
        (((((14 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (14 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (14 : Int) 17 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p14_shift17 : Rat := ((6852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p14_shift17 : Rat := ((3426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (14 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p14_shift17 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p14_shift17 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p14_shift17, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p14_shift17 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p14_shift17 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p14_shift17, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p14_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p14_shift17 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p14_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p14_shift17 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 17 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((14 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p14_shift17)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p14_shift17)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 17)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p15_shift17 :
    |centeredBSplineR 9
        (((((15 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (15 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (15 : Int) 17 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p15_shift17 : Rat := ((18950939813351563527589292847274477308166621879914915293106663502202126010101761464712224334527 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p15_shift17 : Rat := ((28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (15 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p15_shift17 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p15_shift17 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p15_shift17, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p15_shift17 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p15_shift17 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p15_shift17, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p15_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p15_shift17 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p15_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p15_shift17 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 17 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((15 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p15_shift17)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p15_shift17)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 17)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift17 :
    |centeredBSplineR 9
        (((((16 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (16 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (16 : Int) 17 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p16_shift17 : Rat := ((106852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p16_shift17 : Rat := ((17808803240009115097127979756970571987416644273290790979886665084434396338384214065689445500597 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (16 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift17 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift17 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p16_shift17, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift17 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift17 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((5 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p16_shift17, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift17 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift17 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift17 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 17| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 17 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((16 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p16_shift17)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p16_shift17)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 17)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx17
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex17) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 17| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 17 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p12_shift17
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift17
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p14_shift17
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p15_shift17
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift17
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
