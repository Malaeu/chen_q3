import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 57: 57..57.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m22_shift57 :
    |centeredBSplineR 9
        (((((-22 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-22 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-22 : Int) 57 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m22_shift57 : Rat := ((-118654905547557224072534473308470617904966253710507212915289730341661295240903995897106218395863 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m22_shift57 : Rat := ((-9492392443804577925802757864677649432397300296840577033223178427332903619272319671768497471669 : Rat) / 12000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-22 : Int) activeL3RatWeightIndex57
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m22_shift57 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m22_shift57 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m22_shift57, activeL3RatLogLo_p193, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m22_shift57 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m22_shift57 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m22_shift57, activeL3RatLogHi_p193, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m22_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m22_shift57 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m22_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m22_shift57 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 57 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-22 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m22_shift57)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m22_shift57)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 57)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 57)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift57 :
    |centeredBSplineR 9
        (((((-21 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-21 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-21 : Int) 57 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m21_shift57 : Rat := ((6345094452442775927465526691529382095033746289492787084710269658338704759096004102893781604137 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m21_shift57 : Rat := ((169202518731807358065747378440783522534233234386474322258940524222365460242560109410500842777 : Rat) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex57
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift57 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift57 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m21_shift57, activeL3RatLogLo_p193, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift57 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift57 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m21_shift57, activeL3RatLogHi_p193, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift57 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift57 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 57 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-21 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m21_shift57)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m21_shift57)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 57)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 57)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift57 :
    |centeredBSplineR 9
        (((((-20 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-20 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-20 : Int) 57 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m20_shift57 : Rat := ((43781698150814258642488508897176460698344582096497595694903423219446234919698668034297927201379 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m20_shift57 : Rat := ((10507607556195422074197242135322350567602699703159422966776821572667096380727680328231502528331 : Rat) / 12000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex57
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift57 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift57 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m20_shift57, activeL3RatLogLo_p193, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift57 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift57 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m20_shift57, activeL3RatLogHi_p193, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift57 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift57 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 57 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-20 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m20_shift57)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m20_shift57)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 57)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 57)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift57 :
    |centeredBSplineR 9
        (((((-19 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-19 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-19 : Int) 57 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m19_shift57 : Rat := ((256345094452442775927465526691529382095033746289492787084710269658338704759096004102893781604137 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m19_shift57 : Rat := ((20507607556195422074197242135322350567602699703159422966776821572667096380727680328231502528331 : Rat) / 12000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex57
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift57 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift57 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m19_shift57, activeL3RatLogLo_p193, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift57 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex57) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift57 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p193) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m19_shift57, activeL3RatLogHi_p193, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift57 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift57 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift57 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 57| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 57 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-19 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m19_shift57)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m19_shift57)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 57)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 57)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx57
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex57) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 57| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 57 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m22_shift57
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift57
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift57
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift57
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex57.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
