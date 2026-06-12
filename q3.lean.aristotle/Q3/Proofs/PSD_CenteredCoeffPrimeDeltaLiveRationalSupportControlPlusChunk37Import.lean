import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 37: 37..37.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift37 :
    |centeredBSplineR 9
        (((((-21 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-21 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-21 : Int) 37 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m21_shift37 : Rat := ((-57717116553809382669560118297672299843685372386859244643988328075328263047000734344268129649839 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m21_shift37 : Rat := ((-577171165538093826695601182976722998436853723868592446439883280753282630470007343442681296498389 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex37
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift37 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift37 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m21_shift37, activeL3RatLogLo_p107, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift37 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift37 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m21_shift37, activeL3RatLogHi_p107, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift37 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift37 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 37 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-21 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m21_shift37)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m21_shift37)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 37)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 37)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift37 :
    |centeredBSplineR 9
        (((((-20 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-20 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-20 : Int) 37 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m20_shift37 : Rat := ((-32717116553809382669560118297672299843685372386859244643988328075328263047000734344268129649839 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m20_shift37 : Rat := ((-109057055179364608898533727658907666145617907956197482146627760251094210156669114480893765499463 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex37
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift37 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift37 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m20_shift37, activeL3RatLogLo_p107, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift37 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift37 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m20_shift37, activeL3RatLogHi_p107, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift37 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift37 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 37 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-20 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m20_shift37)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m20_shift37)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 37)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 37)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift37 :
    |centeredBSplineR 9
        (((((-19 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-19 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-19 : Int) 37 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m19_shift37 : Rat := ((-2572372184603127556520039432557433281228457462286414881329442691776087682333578114756043216613 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m19_shift37 : Rat := ((-77171165538093826695601182976722998436853723868592446439883280753282630470007343442681296498389 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex37
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift37 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift37 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m19_shift37, activeL3RatLogLo_p107, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift37 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift37 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m19_shift37, activeL3RatLogHi_p107, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift37 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift37 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 37 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-19 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m19_shift37)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m19_shift37)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 37)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 37)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift37 :
    |centeredBSplineR 9
        (((((-18 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-18 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-18 : Int) 37 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m18_shift37 : Rat := ((17282883446190617330439881702327700156314627613140755356011671924671736952999265655731870350161 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m18_shift37 : Rat := ((172828834461906173304398817023277001563146276131407553560116719246717369529992656557318703501611 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex37
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift37 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift37 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m18_shift37, activeL3RatLogLo_p107, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift37 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift37 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m18_shift37, activeL3RatLogHi_p107, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift37 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift37 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 37 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-18 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m18_shift37)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m18_shift37)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 37)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 37)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift37 :
    |centeredBSplineR 9
        (((((-17 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-17 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-17 : Int) 37 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m17_shift37 : Rat := ((42282883446190617330439881702327700156314627613140755356011671924671736952999265655731870350161 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m17_shift37 : Rat := ((140942944820635391101466272341092333854382092043802517853372239748905789843330885519106234500537 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex37
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift37 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift37 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m17_shift37, activeL3RatLogLo_p107, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift37 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex37) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift37 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p107) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m17_shift37, activeL3RatLogHi_p107, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift37 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift37 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift37 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 37| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 37 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-17 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m17_shift37)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m17_shift37)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 37)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 37)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx37
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex37) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 37| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 37 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift37
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift37
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift37
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift37
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift37
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex37.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
