import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 47: 47..47.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift47 :
    |centeredBSplineR 9
        (((((18 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (18 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (18 : Int) 47 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p18_shift47 : Rat := ((-100789261189091828198485655020824097571216954238593429557908019301394366857559611253173499140243 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p18_shift47 : Rat := ((-83991050990909856832071379184020081309347461865494524631590016084495305714633009377644582616869 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex47
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift47 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift47 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p18_shift47, activeL3RatLogHi_p149, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift47 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift47 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p18_shift47, activeL3RatLogLo_p149, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift47 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift47 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 47 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((18 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p18_shift47)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p18_shift47)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 47)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 47)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift47 :
    |centeredBSplineR 9
        (((((19 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (19 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (19 : Int) 47 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p19_shift47 : Rat := ((-16929753729697276066161885006941365857072318079531143185969339767131455619186537084391166380081 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p19_shift47 : Rat := ((-126973152972729570496214137552060243928042385596483573894770048253485917143899028132933747850607 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex47
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift47 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift47 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p19_shift47, activeL3RatLogHi_p149, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift47 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift47 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p19_shift47, activeL3RatLogLo_p149, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift47 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift47 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 47 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((19 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p19_shift47)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p19_shift47)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 47)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 47)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift47 :
    |centeredBSplineR 9
        (((((20 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (20 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (20 : Int) 47 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p20_shift47 : Rat := ((-789261189091828198485655020824097571216954238593429557908019301394366857559611253173499140243 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p20_shift47 : Rat := ((-1973152972729570496214137552060243928042385596483573894770048253485917143899028132933747850607 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex47
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift47 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift47 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p20_shift47, activeL3RatLogHi_p149, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift47 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift47 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p20_shift47, activeL3RatLogLo_p149, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift47 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift47 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 47 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((20 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p20_shift47)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p20_shift47)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 47)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 47)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift47 :
    |centeredBSplineR 9
        (((((21 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (21 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (21 : Int) 47 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p21_shift47 : Rat := ((49210738810908171801514344979175902428783045761406570442091980698605633142440388746826500859757 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p21_shift47 : Rat := ((41008949009090143167928620815979918690652538134505475368409983915504694285366990622355417383131 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex47
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift47 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p21_shift47 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p21_shift47, activeL3RatLogHi_p149, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift47 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p21_shift47 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p21_shift47, activeL3RatLogLo_p149, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift47 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p21_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p21_shift47 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 47 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((21 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p21_shift47)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p21_shift47)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 47)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 47)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift47 :
    |centeredBSplineR 9
        (((((22 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (22 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (22 : Int) 47 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p22_shift47 : Rat := ((33070246270302723933838114993058634142927681920468856814030660232868544380813462915608833619919 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p22_shift47 : Rat := ((248026847027270429503785862447939756071957614403516426105229951746514082856100971867066252149393 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (22 : Int) activeL3RatWeightIndex47
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift47 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p22_shift47 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p22_shift47, activeL3RatLogHi_p149, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift47 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex47) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p22_shift47 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p149) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p22_shift47, activeL3RatLogLo_p149, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift47 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p22_shift47 controlK9RationalDeltaLiveRMinusHi_delta_p22_shift47 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 47| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 47 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((22 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p22_shift47)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p22_shift47)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 47)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 47)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx47
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex47) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 47| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 47 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex47.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift47
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift47
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift47
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p21_shift47
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p22_shift47

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
