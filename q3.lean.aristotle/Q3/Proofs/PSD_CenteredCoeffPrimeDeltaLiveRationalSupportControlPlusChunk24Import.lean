import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 24: 24..24.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift24 :
    |centeredBSplineR 9
        (((((-18 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-18 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-18 : Int) 24 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m18_shift24 : Rat := ((-140820852031426849794649875426767458645551070223181823495987767646933295244857507546886680065789 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m18_shift24 : Rat := ((-211231278047140274691974813140151187968326605334772735243981651470399942867286261320330020098683 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex24
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift24 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift24 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m18_shift24, activeL3RatLogLo_p59, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift24 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift24 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m18_shift24, activeL3RatLogHi_p59, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift24 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift24 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 24 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-18 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m18_shift24)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m18_shift24)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 24)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 24)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift24 :
    |centeredBSplineR 9
        (((((-17 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-17 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-17 : Int) 24 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m17_shift24 : Rat := ((-172462556094280549383949626280302375936653210669545470487963302940799885734572522640660040197367 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m17_shift24 : Rat := ((-86231278047140274691974813140151187968326605334772735243981651470399942867286261320330020098683 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex24
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift24 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift24 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m17_shift24, activeL3RatLogLo_p59, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift24 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift24 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m17_shift24, activeL3RatLogHi_p59, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift24 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift24 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 24 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-17 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m17_shift24)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m17_shift24)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 24)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 24)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift24 :
    |centeredBSplineR 9
        (((((-16 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-16 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-16 : Int) 24 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m16_shift24 : Rat := ((77537443905719450616050373719697624063346789330454529512036697059200114265427477359339959802633 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m16_shift24 : Rat := ((12922907317619908436008395619949604010557798221742421585339449509866685710904579559889993300439 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex24
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift24 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift24 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m16_shift24, activeL3RatLogLo_p59, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift24 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift24 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m16_shift24, activeL3RatLogHi_p59, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift24 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift24 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 24 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-16 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m16_shift24)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m16_shift24)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 24)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 24)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift24 :
    |centeredBSplineR 9
        (((((-15 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-15 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-15 : Int) 24 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m15_shift24 : Rat := ((109179147968573150205350124573232541354448929776818176504012232353066704755142492453113319934211 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m15_shift24 : Rat := ((163768721952859725308025186859848812031673394665227264756018348529600057132713738679669979901317 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex24
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift24 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift24 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m15_shift24, activeL3RatLogLo_p59, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift24 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift24 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m15_shift24, activeL3RatLogHi_p59, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift24 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift24 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 24 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-15 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m15_shift24)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m15_shift24)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 24)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 24)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift24 :
    |centeredBSplineR 9
        (((((-14 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-14 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-14 : Int) 24 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m14_shift24 : Rat := ((577537443905719450616050373719697624063346789330454529512036697059200114265427477359339959802633 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m14_shift24 : Rat := ((288768721952859725308025186859848812031673394665227264756018348529600057132713738679669979901317 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex24
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift24 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift24 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m14_shift24, activeL3RatLogLo_p59, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift24 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex24) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift24 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p59) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m14_shift24, activeL3RatLogHi_p59, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift24 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift24 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift24 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 24| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 24 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-14 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m14_shift24)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m14_shift24)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 24)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 24)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx24
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex24) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 24| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 24 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift24
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift24
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift24
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift24
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift24
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex24.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
