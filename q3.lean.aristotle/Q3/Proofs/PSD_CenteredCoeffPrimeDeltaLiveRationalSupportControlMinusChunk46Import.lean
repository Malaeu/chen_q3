import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 46: 46..46.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift46 :
    |centeredBSplineR 9
        (((((18 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (18 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (18 : Int) 46 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p18_shift46 : Rat := ((-144824644376897252396261639625181260814198886785051305224692834947751621840028373675660687102737 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p18_shift46 : Rat := ((-43447393313069175718878491887554378244259666035515391567407850484325486552008512102698206130821 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift46 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift46 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p18_shift46, activeL3RatLogHi_p139, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift46 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift46 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p18_shift46, activeL3RatLogLo_p139, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift46 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift46 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 46 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((18 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p18_shift46)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p18_shift46)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 46)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift46 :
    |centeredBSplineR 9
        (((((19 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (19 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (19 : Int) 46 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p19_shift46 : Rat := ((-184473933130691757188784918875543782442596660355153915674078504843254865520085121026982061308211 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p19_shift46 : Rat := ((-18447393313069175718878491887554378244259666035515391567407850484325486552008512102698206130821 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift46 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift46 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p19_shift46, activeL3RatLogHi_p139, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift46 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift46 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p19_shift46, activeL3RatLogLo_p139, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift46 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift46 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 46 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((19 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p19_shift46)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p19_shift46)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 46)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift46 :
    |centeredBSplineR 9
        (((((20 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (20 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (20 : Int) 46 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p20_shift46 : Rat := ((65526066869308242811215081124456217557403339644846084325921495156745134479914878973017938691789 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p20_shift46 : Rat := ((2184202228976941427040502704148540585246777988161536144197383171891504482663829299100597956393 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift46 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift46 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p20_shift46, activeL3RatLogHi_p139, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift46 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift46 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p20_shift46, activeL3RatLogLo_p139, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift46 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift46 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 46 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((20 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p20_shift46)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p20_shift46)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 46)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift46 :
    |centeredBSplineR 9
        (((((21 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (21 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (21 : Int) 46 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p21_shift46 : Rat := ((105175355623102747603738360374818739185801113214948694775307165052248378159971626324339312897263 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p21_shift46 : Rat := ((31552606686930824281121508112445621755740333964484608432592149515674513447991487897301793869179 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift46 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift46 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p21_shift46, activeL3RatLogHi_p139, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift46 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift46 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p21_shift46, activeL3RatLogLo_p139, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift46 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift46 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 46 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((21 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p21_shift46)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p21_shift46)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 46)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift46 :
    |centeredBSplineR 9
        (((((22 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (22 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (22 : Int) 46 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p22_shift46 : Rat := ((565526066869308242811215081124456217557403339644846084325921495156745134479914878973017938691789 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p22_shift46 : Rat := ((56552606686930824281121508112445621755740333964484608432592149515674513447991487897301793869179 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (22 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift46 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift46 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p22_shift46, activeL3RatLogHi_p139, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift46 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift46 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p22_shift46, activeL3RatLogLo_p139, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift46 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift46 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift46 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 46| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 46 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((22 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p22_shift46)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p22_shift46)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 46)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx46
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex46) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 46| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 46 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift46
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift46
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift46
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift46
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift46

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
