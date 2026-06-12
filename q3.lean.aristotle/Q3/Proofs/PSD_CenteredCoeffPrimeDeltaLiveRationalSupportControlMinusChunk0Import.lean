import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 0: 0..0.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p1_shift0 :
    |centeredBSplineR 9
        (((((1 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (1 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (1 : Int) 0 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p1_shift0 : Rat := ((-443147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p1_shift0 : Rat := ((-221573590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (1 : Int) activeL3RatWeightIndex0
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p1_shift0 : Rat) : Real) =
            ((((1 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p1_shift0 : Rat) : Real) = (((((1 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p1_shift0, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p1_shift0 : Rat) : Real) =
            ((((1 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p1_shift0 : Rat) : Real) = (((((1 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p1_shift0, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p1_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p1_shift0 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p1_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p1_shift0 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (1 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (1 : Int) 0 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((1 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p1_shift0)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p1_shift0)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (1 : Int) 0)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (1 : Int) 0)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p2_shift0 :
    |centeredBSplineR 9
        (((((2 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (2 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (2 : Int) 0 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p2_shift0 : Rat := ((-193147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p2_shift0 : Rat := ((-32191196759990884902872020243029428012583355726709209020113334915565603661615785934310554499403 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (2 : Int) activeL3RatWeightIndex0
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p2_shift0 : Rat) : Real) =
            ((((2 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p2_shift0 : Rat) : Real) = (((((2 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p2_shift0, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p2_shift0 : Rat) : Real) =
            ((((2 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p2_shift0 : Rat) : Real) = (((((2 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p2_shift0, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p2_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p2_shift0 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p2_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p2_shift0 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (2 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (2 : Int) 0 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((2 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p2_shift0)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p2_shift0)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (2 : Int) 0)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (2 : Int) 0)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p3_shift0 :
    |centeredBSplineR 9
        (((((3 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (3 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (3 : Int) 0 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p3_shift0 : Rat := ((18950939813351563527589292847274477308166621879914915293106663502202126010101761464712224334527 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p3_shift0 : Rat := ((28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (3 : Int) activeL3RatWeightIndex0
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p3_shift0 : Rat) : Real) =
            ((((3 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p3_shift0 : Rat) : Real) = (((((3 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p3_shift0, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p3_shift0 : Rat) : Real) =
            ((((3 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p3_shift0 : Rat) : Real) = (((((3 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p3_shift0, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p3_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p3_shift0 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p3_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p3_shift0 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (3 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (3 : Int) 0 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((3 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p3_shift0)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p3_shift0)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (3 : Int) 0)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (3 : Int) 0)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p4_shift0 :
    |centeredBSplineR 9
        (((((4 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (4 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (4 : Int) 0 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p4_shift0 : Rat := ((306852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p4_shift0 : Rat := ((153426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (4 : Int) activeL3RatWeightIndex0
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p4_shift0 : Rat) : Real) =
            ((((4 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p4_shift0 : Rat) : Real) = (((((4 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p4_shift0, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p4_shift0 : Rat) : Real) =
            ((((4 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p4_shift0 : Rat) : Real) = (((((4 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p4_shift0, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p4_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p4_shift0 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p4_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p4_shift0 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (4 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (4 : Int) 0 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((4 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p4_shift0)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p4_shift0)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (4 : Int) 0)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (4 : Int) 0)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p5_shift0 :
    |centeredBSplineR 9
        (((((5 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (5 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (5 : Int) 0 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p5_shift0 : Rat := ((556852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p5_shift0 : Rat := ((92808803240009115097127979756970571987416644273290790979886665084434396338384214065689445500597 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (5 : Int) activeL3RatWeightIndex0
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p5_shift0 : Rat) : Real) =
            ((((5 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p5_shift0 : Rat) : Real) = (((((5 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p5_shift0, activeL3RatLogHi_p2, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p5_shift0 : Rat) : Real) =
            ((((5 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex0) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p5_shift0 : Rat) : Real) = (((((5 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p2) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p5_shift0, activeL3RatLogLo_p2, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p5_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p5_shift0 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p5_shift0 controlK9RationalDeltaLiveRMinusHi_delta_p5_shift0 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (5 : Int) 0| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (5 : Int) 0 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((5 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p5_shift0)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p5_shift0)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (5 : Int) 0)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (5 : Int) 0)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx0
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex0) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 0| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 0 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p1_shift0
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p2_shift0
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p3_shift0
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p4_shift0
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p5_shift0
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex0.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
