import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 7: 7..7.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p8_shift7 :
    |centeredBSplineR 9
        (((((8 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (8 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (8 : Int) 7 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p8_shift7 : Rat := ((-79579054559674108812388715593025859964341370787483435043713541826114724782647342615010941600527 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p8_shift7 : Rat := ((-66315878799728424010323929660854883303617808989569529203094618188428937318872785512509118000439 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (8 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p8_shift7 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p8_shift7 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p8_shift7, activeL3RatLogHi_p11, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p8_shift7 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p8_shift7 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p8_shift7, activeL3RatLogLo_p11, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p8_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p8_shift7 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p8_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p8_shift7 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 7 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((8 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p8_shift7)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p8_shift7)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 7)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p9_shift7 :
    |centeredBSplineR 9
        (((((9 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (9 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (9 : Int) 7 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p9_shift7 : Rat := ((-9859684853224702937462905197675286654780456929161145014571180608704908260882447538336980533509 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p9_shift7 : Rat := ((-73947636399185272030971788982564649910853426968708587609283854565286811956618356537527354001317 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (9 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p9_shift7 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p9_shift7 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p9_shift7, activeL3RatLogHi_p11, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p9_shift7 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p9_shift7 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p9_shift7, activeL3RatLogLo_p11, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p9_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p9_shift7 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p9_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p9_shift7 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 7 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((9 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p9_shift7)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p9_shift7)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 7)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p10_shift7 :
    |centeredBSplineR 9
        (((((10 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (10 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (10 : Int) 7 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p10_shift7 : Rat := ((20420945440325891187611284406974140035658629212516564956286458173885275217352657384989058399473 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p10_shift7 : Rat := ((51052363600814727969028211017435350089146573031291412390716145434713188043381643462472645998683 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (10 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p10_shift7 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p10_shift7 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p10_shift7, activeL3RatLogHi_p11, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p10_shift7 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p10_shift7 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p10_shift7, activeL3RatLogLo_p11, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p10_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p10_shift7 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p10_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p10_shift7 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 7 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((10 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p10_shift7)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p10_shift7)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 7)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p11_shift7 :
    |centeredBSplineR 9
        (((((11 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (11 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (11 : Int) 7 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p11_shift7 : Rat := ((70420945440325891187611284406974140035658629212516564956286458173885275217352657384989058399473 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p11_shift7 : Rat := ((58684121200271575989676070339145116696382191010430470796905381811571062681127214487490881999561 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (11 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p11_shift7 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p11_shift7 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p11_shift7, activeL3RatLogHi_p11, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p11_shift7 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p11_shift7 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p11) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p11_shift7, activeL3RatLogLo_p11, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p11_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p11_shift7 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p11_shift7 controlK9RationalDeltaLiveRMinusHi_delta_p11_shift7 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 7| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 7 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((11 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p11_shift7)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p11_shift7)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 7)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx7
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex7) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 7| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 7 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p8_shift7
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p9_shift7
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p10_shift7
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p11_shift7
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
