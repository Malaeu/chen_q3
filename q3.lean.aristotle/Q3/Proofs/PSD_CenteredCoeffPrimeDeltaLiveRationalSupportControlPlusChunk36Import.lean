import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 36: 36..36.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift36 :
    |centeredBSplineR 9
        (((((-20 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-20 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-20 : Int) 36 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m20_shift36 : Rat := ((-91317752942591057307849421236639794842934722907299209347192260242367198888051432602063506236973 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m20_shift36 : Rat := ((-365271011770364229231397684946559179371738891629196837388769040969468795552205730408254024947891 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex36
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift36 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift36 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m20_shift36, activeL3RatLogLo_p103, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift36 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift36 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m20_shift36, activeL3RatLogHi_p103, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift36 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift36 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 36 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-20 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m20_shift36)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m20_shift36)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 36)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 36)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift36 :
    |centeredBSplineR 9
        (((((-19 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-19 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-19 : Int) 36 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m19_shift36 : Rat := ((-28817752942591057307849421236639794842934722907299209347192260242367198888051432602063506236973 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m19_shift36 : Rat := ((-38423670590121409743799228315519726457246297209732279129589680323156265184068576802751341649297 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex36
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift36 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift36 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m19_shift36, activeL3RatLogLo_p103, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift36 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift36 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m19_shift36, activeL3RatLogHi_p103, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift36 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift36 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 36 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-19 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m19_shift36)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m19_shift36)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 36)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 36)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift36 :
    |centeredBSplineR 9
        (((((-18 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-18 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-18 : Int) 36 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m18_shift36 : Rat := ((11227415685802980897383526254453401719021759030900263550935913252544267037316189132645497921009 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m18_shift36 : Rat := ((134728988229635770768602315053440820628261108370803162611230959030531204447794269591745975052109 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex36
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift36 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift36 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m18_shift36, activeL3RatLogLo_p103, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift36 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift36 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m18_shift36, activeL3RatLogHi_p103, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift36 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift36 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 36 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-18 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m18_shift36)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m18_shift36)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 36)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 36)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift36 :
    |centeredBSplineR 9
        (((((-17 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-17 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-17 : Int) 36 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m17_shift36 : Rat := ((96182247057408942692150578763360205157065277092700790652807739757632801111948567397936493763027 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m17_shift36 : Rat := ((384728988229635770768602315053440820628261108370803162611230959030531204447794269591745975052109 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex36
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift36 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift36 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m17_shift36, activeL3RatLogLo_p103, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift36 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex36) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift36 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p103) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m17_shift36, activeL3RatLogHi_p103, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift36 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift36 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift36 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 36| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 36 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-17 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m17_shift36)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m17_shift36)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 36)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 36)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx36
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex36) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 36| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 36 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift36
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift36
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift36
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift36
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex36.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
