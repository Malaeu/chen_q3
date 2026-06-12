import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 8: 8..8.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift8 :
    |centeredBSplineR 9
        (((((-12 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-12 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-12 : Int) 8 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m12_shift8 : Rat := ((-435050642538463263946512558434681395194732055239792883580954489336535332675589820600425336559511 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m12_shift8 : Rat := ((-43505064253846326394651255843468139519473205523979288358095448933653533267558982060042533655951 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-12 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift8 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m12_shift8 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m12_shift8, activeL3RatLogLo_p13, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift8 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m12_shift8 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m12_shift8, activeL3RatLogHi_p13, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift8 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m12_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m12_shift8 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 8 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-12 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m12_shift8)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m12_shift8)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 8)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift8 :
    |centeredBSplineR 9
        (((((-11 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-11 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-11 : Int) 8 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m11_shift8 : Rat := ((-185050642538463263946512558434681395194732055239792883580954489336535332675589820600425336559511 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m11_shift8 : Rat := ((-6168354751282108798217085281156046506491068507993096119365149644551177755852994020014177885317 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-11 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift8 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m11_shift8 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m11_shift8, activeL3RatLogLo_p13, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift8 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m11_shift8 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m11_shift8, activeL3RatLogHi_p13, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift8 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m11_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m11_shift8 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 8 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-11 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m11_shift8)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m11_shift8)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 8)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift8 :
    |centeredBSplineR 9
        (((((-10 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-10 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-10 : Int) 8 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m10_shift8 : Rat := ((21649785820512245351162480521772868268422648253402372139681836887821555774803393133191554480163 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m10_shift8 : Rat := ((6494935746153673605348744156531860480526794476020711641904551066346466732441017939957466344049 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-10 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift8 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m10_shift8 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m10_shift8, activeL3RatLogLo_p13, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift8 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m10_shift8 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m10_shift8, activeL3RatLogHi_p13, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift8 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m10_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m10_shift8 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 8 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-10 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m10_shift8)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m10_shift8)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 8)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m9_shift8 :
    |centeredBSplineR 9
        (((((-9 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-9 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-9 : Int) 8 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m9_shift8 : Rat := ((314949357461536736053487441565318604805267944760207116419045510663464667324410179399574663440489 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m9_shift8 : Rat := ((31494935746153673605348744156531860480526794476020711641904551066346466732441017939957466344049 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-9 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m9_shift8 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m9_shift8 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m9_shift8, activeL3RatLogLo_p13, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m9_shift8 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m9_shift8 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m9_shift8, activeL3RatLogHi_p13, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m9_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m9_shift8 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m9_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m9_shift8 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 8 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-9 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m9_shift8)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m9_shift8)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 8)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m8_shift8 :
    |centeredBSplineR 9
        (((((-8 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-8 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-8 : Int) 8 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m8_shift8 : Rat := ((564949357461536736053487441565318604805267944760207116419045510663464667324410179399574663440489 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m8_shift8 : Rat := ((18831645248717891201782914718843953493508931492006903880634850355448822244147005979985822114683 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-8 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m8_shift8 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m8_shift8 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m8_shift8, activeL3RatLogLo_p13, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m8_shift8 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m8_shift8 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p13) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m8_shift8, activeL3RatLogHi_p13, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m8_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m8_shift8 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m8_shift8 controlK9RationalDeltaLiveRPlusHi_delta_m8_shift8 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 8| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 8 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-8 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m8_shift8)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m8_shift8)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 8)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx8
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex8) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 8| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 8 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m12_shift8
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m11_shift8
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m10_shift8
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m9_shift8
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m8_shift8
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
