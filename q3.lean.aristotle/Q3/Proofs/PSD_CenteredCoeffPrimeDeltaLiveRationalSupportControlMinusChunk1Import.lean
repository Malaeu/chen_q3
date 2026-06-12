import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 1: 1..1.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p2_shift1 :
    |centeredBSplineR 9
        (((((2 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (2 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (2 : Int) 1 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p2_shift1 : Rat := ((-199537429556036563798415078974175234882496852607583150578231444545831431072869655624538584937911 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p2_shift1 : Rat := ((-149653072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (2 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p2_shift1 : Rat) : Real) =
            ((((2 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p2_shift1 : Rat) : Real) = (((((2 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p2_shift1, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p2_shift1 : Rat) : Real) =
            ((((2 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p2_shift1 : Rat) : Real) = (((((2 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p2_shift1, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p2_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p2_shift1 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p2_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p2_shift1 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (2 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (2 : Int) 1 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((2 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p2_shift1)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p2_shift1)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (2 : Int) 1)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (2 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p3_shift1 :
    |centeredBSplineR 9
        (((((3 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (3 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (3 : Int) 1 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p3_shift1 : Rat := ((-348612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p3_shift1 : Rat := ((-87153072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (3 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p3_shift1 : Rat) : Real) =
            ((((3 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p3_shift1 : Rat) : Real) = (((((3 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p3_shift1, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p3_shift1 : Rat) : Real) =
            ((((3 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p3_shift1 : Rat) : Real) = (((((3 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p3_shift1, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p3_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p3_shift1 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p3_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p3_shift1 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (3 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (3 : Int) 1 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((3 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p3_shift1)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p3_shift1)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (3 : Int) 1)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (3 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p4_shift1 :
    |centeredBSplineR 9
        (((((4 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (4 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (4 : Int) 1 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p4_shift1 : Rat := ((-98612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p4_shift1 : Rat := ((-8217690722342474282937103076877142053957546485229120977891194469791191101550747239467979567811 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (4 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p4_shift1 : Rat) : Real) =
            ((((4 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p4_shift1 : Rat) : Real) = (((((4 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p4_shift1, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p4_shift1 : Rat) : Real) =
            ((((4 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p4_shift1 : Rat) : Real) = (((((4 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p4_shift1, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p4_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p4_shift1 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p4_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p4_shift1 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (4 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (4 : Int) 1 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((4 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p4_shift1)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p4_shift1)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (4 : Int) 1)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (4 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p5_shift1 :
    |centeredBSplineR 9
        (((((5 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (5 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (5 : Int) 1 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p5_shift1 : Rat := ((50462570443963436201584921025824765117503147392416849421768555454168568927130344375461415062089 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p5_shift1 : Rat := ((37846927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (5 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p5_shift1 : Rat) : Real) =
            ((((5 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p5_shift1 : Rat) : Real) = (((((5 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p5_shift1, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p5_shift1 : Rat) : Real) =
            ((((5 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p5_shift1 : Rat) : Real) = (((((5 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p5_shift1, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p5_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p5_shift1 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p5_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p5_shift1 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (5 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (5 : Int) 1 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((5 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p5_shift1)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p5_shift1)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (5 : Int) 1)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (5 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p6_shift1 :
    |centeredBSplineR 9
        (((((6 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (6 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (6 : Int) 1 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p6_shift1 : Rat := ((401387711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p6_shift1 : Rat := ((100346927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (6 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p6_shift1 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p6_shift1 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p6_shift1, activeL3RatLogHi_p3, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p6_shift1 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p6_shift1 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p3) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p6_shift1, activeL3RatLogLo_p3, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p6_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p6_shift1 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p6_shift1 controlK9RationalDeltaLiveRMinusHi_delta_p6_shift1 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 1| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 1 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((6 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p6_shift1)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p6_shift1)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 1)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx1
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex1) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 1| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 1 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p2_shift1
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p3_shift1
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p4_shift1
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p5_shift1
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p6_shift1
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
