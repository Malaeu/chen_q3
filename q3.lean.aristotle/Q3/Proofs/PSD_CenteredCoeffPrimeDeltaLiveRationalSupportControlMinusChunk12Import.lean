import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 12: 12..12.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p11_shift12 :
    |centeredBSplineR 9
        (((((11 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (11 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (11 : Int) 12 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p11_shift12 : Rat := ((-25699614395276646053783522120679741229492020989362382799909025165532883065653219879893406143533 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p11_shift12 : Rat := ((-192747107964574845403376415905098059221190157420217870999317688741496622992399149099200546076497 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (11 : Int) activeL3RatWeightIndex12
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p11_shift12 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p11_shift12 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p11_shift12, activeL3RatLogHi_p23, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p11_shift12 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p11_shift12 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p11_shift12, activeL3RatLogLo_p23, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p11_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p11_shift12 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p11_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p11_shift12 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 12 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((11 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p11_shift12)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p11_shift12)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 12)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 12)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p12_shift12 :
    |centeredBSplineR 9
        (((((12 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (12 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (12 : Int) 12 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p12_shift12 : Rat := ((-27098843185829938161350566362039223688476062968087148399727075496598649196959659639680218430599 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p12_shift12 : Rat := ((-67747107964574845403376415905098059221190157420217870999317688741496622992399149099200546076497 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (12 : Int) activeL3RatWeightIndex12
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p12_shift12 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p12_shift12 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p12_shift12, activeL3RatLogHi_p23, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p12_shift12 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p12_shift12 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p12_shift12, activeL3RatLogLo_p23, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p12_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p12_shift12 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p12_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p12_shift12 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 12 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((12 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p12_shift12)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p12_shift12)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 12)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 12)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift12 :
    |centeredBSplineR 9
        (((((13 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (13 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (13 : Int) 12 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p13_shift12 : Rat := ((22901156814170061838649433637960776311523937031912851600272924503401350803040340360319781569401 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p13_shift12 : Rat := ((19084297345141718198874528031633980259603280859927376333560770419501125669200283633599817974501 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (13 : Int) activeL3RatWeightIndex12
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift12 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p13_shift12 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p13_shift12, activeL3RatLogHi_p23, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift12 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p13_shift12 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p13_shift12, activeL3RatLogLo_p23, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift12 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p13_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p13_shift12 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 12 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((13 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p13_shift12)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p13_shift12)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 12)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 12)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p14_shift12 :
    |centeredBSplineR 9
        (((((14 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (14 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (14 : Int) 12 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p14_shift12 : Rat := ((24300385604723353946216477879320258770507979010637617200090974834467116934346780120106593856467 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p14_shift12 : Rat := ((182252892035425154596623584094901940778809842579782129000682311258503377007600850900799453923503 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (14 : Int) activeL3RatWeightIndex12
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p14_shift12 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p14_shift12 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p14_shift12, activeL3RatLogHi_p23, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p14_shift12 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex12) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p14_shift12 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p23) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p14_shift12, activeL3RatLogLo_p23, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p14_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p14_shift12 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p14_shift12 controlK9RationalDeltaLiveRMinusHi_delta_p14_shift12 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 12| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 12 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((14 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p14_shift12)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p14_shift12)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 12)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 12)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx12
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex12) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 12| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 12 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p11_shift12
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p12_shift12
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p13_shift12
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p14_shift12
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex12.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
