import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 17: 17..17.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift17 :
    |centeredBSplineR 11
        (((((-16 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-16 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-16 : Int) 17 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift17 : Rat := ((-17808803240009115097127979756970571987416644273290790979886665084434396338384214065689445500597 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift17 : Rat := ((-106852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift17 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift17 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift17, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift17 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift17 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift17, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift17 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift17 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 17 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-16 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift17)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift17)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 17)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift17 :
    |centeredBSplineR 11
        (((((-15 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-15 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-15 : Int) 17 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift17 : Rat := ((-28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift17 : Rat := ((-18950939813351563527589292847274477308166621879914915293106663502202126010101761464712224334527 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift17 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift17 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift17, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift17 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift17 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift17, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift17 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift17 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 17 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-15 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift17)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift17)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 17)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift17 :
    |centeredBSplineR 11
        (((((-14 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-14 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-14 : Int) 17 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift17 : Rat := ((-3426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift17 : Rat := ((-6852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift17 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift17 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift17, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift17 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift17 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift17, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift17 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift17 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 17 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-14 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift17)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift17)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 17)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift17 :
    |centeredBSplineR 11
        (((((-13 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-13 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-13 : Int) 17 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift17 : Rat := ((7191196759990884902872020243029428012583355726709209020113334915565603661615785934310554499403 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift17 : Rat := ((43147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift17 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift17 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift17, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift17 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift17 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift17, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift17 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift17 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 17 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-13 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift17)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift17)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 17)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m12_shift17 :
    |centeredBSplineR 11
        (((((-12 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-12 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-12 : Int) 17 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift17 : Rat := ((46573590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift17 : Rat := ((31049060186648436472410707152725522691833378120085084706893336497797873989898238535287775665473 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-12 : Int) activeL3RatWeightIndex17
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift17 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift17 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift17, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift17 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex17) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift17 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((5 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift17, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift17 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift17 primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift17 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 17 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-12 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift17)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift17)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 17)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 17)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx17
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex17) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 17| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 17 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift17
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift17
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift17
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift17
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m12_shift17
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex17.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
