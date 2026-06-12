import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 22: 22..22.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift22 :
    |centeredBSplineR 9
        (((((-17 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-17 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-17 : Int) 22 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m17_shift22 : Rat := ((-59696616981562231631549085518940090120971756806046270513536616687473379082643577404113833804043 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m17_shift22 : Rat := ((-5596557842021459215457726767400633448841102200566837860644057814450629288997835381635671919129 : Rat) / 4687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift22 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift22 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m17_shift22, activeL3RatLogLo_p7, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift22 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift22 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m17_shift22, activeL3RatLogHi_p7, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift22 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift22 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 22 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-17 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m17_shift22)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m17_shift22)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 22)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift22 :
    |centeredBSplineR 9
        (((((-16 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-16 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-16 : Int) 22 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m16_shift22 : Rat := ((-54089850944686694894647256556820270362915270418138811540609850062420137247930732212341501412129 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m16_shift22 : Rat := ((-563435947340486405152575589133544482947034066855612620214685938150209762999278460545223973043 : Rat) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift22 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift22 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m16_shift22, activeL3RatLogLo_p7, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift22 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift22 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m16_shift22, activeL3RatLogHi_p7, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift22 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift22 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 22 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-16 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m16_shift22)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m16_shift22)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 22)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift22 :
    |centeredBSplineR 9
        (((((-15 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-15 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-15 : Int) 22 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m15_shift22 : Rat := ((70910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587871 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m15_shift22 : Rat := ((2215942157978540784542273232599366551158897799433162139355942185549370711002164618364328080871 : Rat) / 4687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift22 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift22 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m15_shift22, activeL3RatLogLo_p7, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift22 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift22 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m15_shift22, activeL3RatLogHi_p7, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift22 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift22 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 22 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-15 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m15_shift22)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m15_shift22)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 22)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift22 :
    |centeredBSplineR 9
        (((((-14 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-14 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-14 : Int) 22 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m14_shift22 : Rat := ((65303383018437768368450914481059909879028243193953729486463383312526620917356422595886166195957 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m14_shift22 : Rat := ((6122192157978540784542273232599366551158897799433162139355942185549370711002164618364328080871 : Rat) / 4687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift22 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift22 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m14_shift22, activeL3RatLogLo_p7, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift22 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift22 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m14_shift22, activeL3RatLogHi_p7, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift22 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift22 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift22 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 22| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 22 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-14 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m14_shift22)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m14_shift22)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 22)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx22
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex22) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 22| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 22 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift22
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift22
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift22
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift22
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
