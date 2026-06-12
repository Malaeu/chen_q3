import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 5: 5..5.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m10_shift5 :
    |centeredBSplineR 11
        (((((-10 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-10 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-10 : Int) 5 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift5 : Rat := ((-210279229160082035874151817812735147886749798459617118818979985759909567045457926591205009505373 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift5 : Rat := ((-420558458320164071748303635625470295773499596919234237637959971519819134090915853182410019010743 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-10 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift5 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift5 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift5, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift5 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift5 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift5, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift5 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift5 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 5 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-10 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift5)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift5)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 5)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m9_shift5 :
    |centeredBSplineR 11
        (((((-9 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-9 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-9 : Int) 5 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift5 : Rat := ((-28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift5 : Rat := ((-56852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-9 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift5 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift5 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift5, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift5 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift5 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift5, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift5 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift5 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 5 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-9 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift5)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift5)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 5)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m8_shift5 :
    |centeredBSplineR 11
        (((((-8 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-8 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-8 : Int) 5 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift5 : Rat := ((39720770839917964125848182187264852113250201540382881181020014240090432954542073408794990494627 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift5 : Rat := ((79441541679835928251696364374529704226500403080765762362040028480180865909084146817589980989257 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-8 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift5 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift5 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift5, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift5 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift5 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift5, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift5 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift5 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 5 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-8 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift5)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift5)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 5)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m7_shift5 :
    |centeredBSplineR 11
        (((((-7 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-7 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-7 : Int) 5 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift5 : Rat := ((164720770839917964125848182187264852113250201540382881181020014240090432954542073408794990494627 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift5 : Rat := ((329441541679835928251696364374529704226500403080765762362040028480180865909084146817589980989257 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-7 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift5 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift5 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift5, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift5 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift5 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift5, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift5 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift5 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 5 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-7 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift5)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift5)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 5)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift5 :
    |centeredBSplineR 11
        (((((-6 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-6 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-6 : Int) 5 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift5 : Rat := ((96573590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift5 : Rat := ((193147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-6 : Int) activeL3RatWeightIndex5
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift5 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift5 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift5, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift5 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex5) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift5 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift5, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift5 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift5 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift5 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 5 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-6 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift5)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift5)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 5)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 5)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx5
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex5) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 5| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 5 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m10_shift5
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m9_shift5
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m8_shift5
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m7_shift5
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift5
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex5.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
