import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 11: 11..11.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift11 :
    |centeredBSplineR 9
        (((((-14 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-14 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-14 : Int) 11 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m14_shift11 : Rat := ((-185187006944519846663657522704048820920873579566957060487346587863569099311934237095280538728087 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m14_shift11 : Rat := ((-27778051041677976999548628405607323138131036935043559073101988179535364896790135564292080809213 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift11 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift11 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m14_shift11, activeL3RatLogLo_p19, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift11 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift11 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m14_shift11, activeL3RatLogHi_p19, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift11 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift11 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 11 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-14 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m14_shift11)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m14_shift11)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 11)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift11 :
    |centeredBSplineR 9
        (((((-13 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-13 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-13 : Int) 11 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m13_shift11 : Rat := ((-305561020833559539990972568112146462762620738700871181462039763590707297935802711285841616184261 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m13_shift11 : Rat := ((-15278051041677976999548628405607323138131036935043559073101988179535364896790135564292080809213 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift11 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift11 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m13_shift11, activeL3RatLogLo_p19, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift11 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift11 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m13_shift11, activeL3RatLogHi_p19, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift11 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift11 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 11 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-13 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m13_shift11)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m13_shift11)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 11)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift11 :
    |centeredBSplineR 9
        (((((-12 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-12 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-12 : Int) 11 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m12_shift11 : Rat := ((-55561020833559539990972568112146462762620738700871181462039763590707297935802711285841616184261 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m12_shift11 : Rat := ((-926017013892658999849542801869107712710345645014519691033996059845121632263378521430693603071 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-12 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift11 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift11 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m12_shift11, activeL3RatLogLo_p19, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift11 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift11 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m12_shift11, activeL3RatLogHi_p19, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift11 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift11 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 11 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-12 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m12_shift11)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m12_shift11)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 11)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift11 :
    |centeredBSplineR 9
        (((((-11 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-11 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-11 : Int) 11 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m11_shift11 : Rat := ((64812993055480153336342477295951179079126420433042939512653412136430900688065762904719461271913 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m11_shift11 : Rat := ((9721948958322023000451371594392676861868963064956440926898011820464635103209864435707919190787 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-11 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift11 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift11 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m11_shift11, activeL3RatLogLo_p19, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift11 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift11 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m11_shift11, activeL3RatLogHi_p19, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift11 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift11 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 11 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-11 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m11_shift11)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m11_shift11)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 11)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift11 :
    |centeredBSplineR 9
        (((((-10 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-10 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-10 : Int) 11 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m10_shift11 : Rat := ((444438979166440460009027431887853537237379261299128818537960236409292702064197288714158383815739 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m10_shift11 : Rat := ((22221948958322023000451371594392676861868963064956440926898011820464635103209864435707919190787 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-10 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift11 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift11 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m10_shift11, activeL3RatLogLo_p19, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift11 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift11 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m10_shift11, activeL3RatLogHi_p19, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift11 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift11 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift11 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 11| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 11 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-10 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m10_shift11)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m10_shift11)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 11)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx11
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex11) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 11| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 11 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift11
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift11
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift11
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift11
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift11
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
