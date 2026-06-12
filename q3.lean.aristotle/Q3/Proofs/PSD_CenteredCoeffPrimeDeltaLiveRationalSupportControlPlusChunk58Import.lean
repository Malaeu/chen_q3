import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 58: 58..58.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m22_shift58 :
    |centeredBSplineR 9
        (((((-22 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-22 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-22 : Int) 58 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m22_shift58 : Rat := ((-216796271262011493220202670837169024991355937641960294201395628084498623951151043264242645344389 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m22_shift58 : Rat := ((-18066355938500957768350222569764085415946328136830024516782969007041551995929253605353553778699 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-22 : Int) activeL3RatWeightIndex58
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m22_shift58 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m22_shift58 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m22_shift58, activeL3RatLogLo_p197, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m22_shift58 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m22_shift58 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m22_shift58, activeL3RatLogHi_p197, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m22_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m22_shift58 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m22_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m22_shift58 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 58 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-22 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m22_shift58)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m22_shift58)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 58)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 58)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift58 :
    |centeredBSplineR 9
        (((((-21 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-21 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-21 : Int) 58 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m21_shift58 : Rat := ((11067909579329502259932443054276991669548020786013235266201457305167125349616318911919118218537 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m21_shift58 : Rat := ((8300932184497126694949332290707743752161015589509926449651092978875344012212239183939338663903 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex58
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift58 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift58 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m21_shift58, activeL3RatLogLo_p197, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift58 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift58 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m21_shift58, activeL3RatLogHi_p197, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift58 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift58 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 58 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-21 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m21_shift58)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m21_shift58)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 58)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 58)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift58 :
    |centeredBSplineR 9
        (((((-20 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-20 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-20 : Int) 58 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m20_shift58 : Rat := ((283203728737988506779797329162830975008644062358039705798604371915501376048848956735757354655611 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m20_shift58 : Rat := ((70800932184497126694949332290707743752161015589509926449651092978875344012212239183939338663903 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex58
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift58 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift58 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m20_shift58, activeL3RatLogLo_p197, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift58 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift58 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m20_shift58, activeL3RatLogHi_p197, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift58 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift58 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 58 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-20 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m20_shift58)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m20_shift58)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 58)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 58)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift58 :
    |centeredBSplineR 9
        (((((-19 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-19 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-19 : Int) 58 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m19_shift58 : Rat := ((533203728737988506779797329162830975008644062358039705798604371915501376048848956735757354655611 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m19_shift58 : Rat := ((44433644061499042231649777430235914584053671863169975483217030992958448004070746394646446221301 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex58
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift58 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift58 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m19_shift58, activeL3RatLogLo_p197, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift58 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex58) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift58 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p197) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m19_shift58, activeL3RatLogHi_p197, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift58 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift58 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift58 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 58| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 58 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-19 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m19_shift58)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m19_shift58)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 58)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 58)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx58
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex58) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 58| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 58 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m22_shift58
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift58
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift58
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift58
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex58.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
