import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 28: 28..28.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p15_shift28 :
    |centeredBSplineR 9
        (((((15 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (15 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (15 : Int) 28 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p15_shift28 : Rat := ((-128169969260328855332363633128258524189894131677641527030356450506837876706057591491560831068159 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p15_shift28 : Rat := ((-34178658469421028088630302167535606450638435114037740541428386801823433788282024397749554951509 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (15 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p15_shift28 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p15_shift28 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p15_shift28, activeL3RatLogHi_p71, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p15_shift28 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p15_shift28 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p15_shift28, activeL3RatLogLo_p71, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p15_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p15_shift28 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p15_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p15_shift28 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 28 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((15 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p15_shift28)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p15_shift28)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 28)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift28 :
    |centeredBSplineR 9
        (((((16 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (16 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (16 : Int) 28 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p16_shift28 : Rat := ((-21889989753442951777454544376086174729964710559213842343452150168945958902019197163853610356053 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p16_shift28 : Rat := ((-52535975408263084265890906502606819351915305342113221624285160405470301364846073193248664854527 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (16 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift28 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift28 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p16_shift28, activeL3RatLogHi_p71, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift28 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift28 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p16_shift28, activeL3RatLogLo_p71, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift28 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift28 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 28 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((16 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p16_shift28)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p16_shift28)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 28)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p17_shift28 :
    |centeredBSplineR 9
        (((((17 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (17 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (17 : Int) 28 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p17_shift28 : Rat := ((-3169969260328855332363633128258524189894131677641527030356450506837876706057591491560831068159 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p17_shift28 : Rat := ((-2535975408263084265890906502606819351915305342113221624285160405470301364846073193248664854527 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (17 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p17_shift28 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p17_shift28 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p17_shift28, activeL3RatLogHi_p71, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p17_shift28 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p17_shift28 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p17_shift28, activeL3RatLogLo_p71, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p17_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p17_shift28 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p17_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p17_shift28 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 28 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((17 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p17_shift28)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p17_shift28)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 28)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift28 :
    |centeredBSplineR 9
        (((((18 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (18 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (18 : Int) 28 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p18_shift28 : Rat := ((59330030739671144667636366871741475810105868322358472969643549493162123293942408508439168931841 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p18_shift28 : Rat := ((15821341530578971911369697832464393549361564885962259458571613198176566211717975602250445048491 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift28 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift28 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p18_shift28, activeL3RatLogHi_p71, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift28 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift28 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p18_shift28, activeL3RatLogLo_p71, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift28 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift28 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 28 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((18 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p18_shift28)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p18_shift28)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 28)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift28 :
    |centeredBSplineR 9
        (((((19 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (19 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (19 : Int) 28 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p19_shift28 : Rat := ((40610010246557048222545455623913825270035289440786157656547849831054041097980802836146389643947 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p19_shift28 : Rat := ((97464024591736915734109093497393180648084694657886778375714839594529698635153926806751335145473 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift28 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift28 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p19_shift28, activeL3RatLogHi_p71, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift28 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift28 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p71) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p19_shift28, activeL3RatLogLo_p71, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift28 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift28 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift28 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 28| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 28 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((19 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p19_shift28)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p19_shift28)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 28)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx28
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex28) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 28| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 28 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p15_shift28
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift28
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p17_shift28
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift28
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift28
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
