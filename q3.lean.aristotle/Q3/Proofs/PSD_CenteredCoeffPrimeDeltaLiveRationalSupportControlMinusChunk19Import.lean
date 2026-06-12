import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 19: 19..19.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift19 :
    |centeredBSplineR 9
        (((((13 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (13 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (13 : Int) 19 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p13_shift19 : Rat := ((-463572066704307803866763373037407588376410469399301633619262910259978616405657505962317141371987 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p13_shift19 : Rat := ((-231786033352153901933381686518703794188205234699650816809631455129989308202828752981158570685993 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (13 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift19 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift19 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p13_shift19, activeL3RatLogHi_p41, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift19 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift19 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p13_shift19, activeL3RatLogLo_p41, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift19 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift19 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 19 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((13 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p13_shift19)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p13_shift19)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 19)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p14_shift19 :
    |centeredBSplineR 9
        (((((14 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (14 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (14 : Int) 19 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p14_shift19 : Rat := ((-213572066704307803866763373037407588376410469399301633619262910259978616405657505962317141371987 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p14_shift19 : Rat := ((-35595344450717967311127228839567931396068411566550272269877151709996436067609584327052856895331 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (14 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p14_shift19 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p14_shift19 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p14_shift19, activeL3RatLogHi_p41, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p14_shift19 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p14_shift19 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p14_shift19, activeL3RatLogLo_p41, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p14_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p14_shift19 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p14_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p14_shift19 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 19 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((14 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p14_shift19)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p14_shift19)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 19)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p15_shift19 :
    |centeredBSplineR 9
        (((((15 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (15 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (15 : Int) 19 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p15_shift19 : Rat := ((12142644431897398711078875654197470541196510200232788793579029913340461198114164679227619542671 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p15_shift19 : Rat := ((18213966647846098066618313481296205811794765300349183190368544870010691797171247018841429314007 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (15 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p15_shift19 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p15_shift19 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p15_shift19, activeL3RatLogHi_p41, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p15_shift19 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p15_shift19 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p15_shift19, activeL3RatLogLo_p41, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p15_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p15_shift19 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p15_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p15_shift19 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 19 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((15 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p15_shift19)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p15_shift19)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 19)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift19 :
    |centeredBSplineR 9
        (((((16 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (16 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (16 : Int) 19 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p16_shift19 : Rat := ((286427933295692196133236626962592411623589530600698366380737089740021383594342494037682858628013 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p16_shift19 : Rat := ((143213966647846098066618313481296205811794765300349183190368544870010691797171247018841429314007 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (16 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift19 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift19 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p16_shift19, activeL3RatLogHi_p41, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift19 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift19 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p16_shift19, activeL3RatLogLo_p41, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift19 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift19 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 19 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((16 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p16_shift19)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p16_shift19)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 19)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p17_shift19 :
    |centeredBSplineR 9
        (((((17 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (17 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (17 : Int) 19 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p17_shift19 : Rat := ((536427933295692196133236626962592411623589530600698366380737089740021383594342494037682858628013 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p17_shift19 : Rat := ((89404655549282032688872771160432068603931588433449727730122848290003563932390415672947143104669 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (17 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p17_shift19 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p17_shift19 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p17_shift19, activeL3RatLogHi_p41, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p17_shift19 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p17_shift19 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p41) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p17_shift19, activeL3RatLogLo_p41, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p17_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p17_shift19 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p17_shift19 controlK9RationalDeltaLiveRMinusHi_delta_p17_shift19 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 19| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 19 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((17 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p17_shift19)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p17_shift19)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 19)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx19
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex19) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 19| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 19 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift19
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p14_shift19
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p15_shift19
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift19
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p17_shift19
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
