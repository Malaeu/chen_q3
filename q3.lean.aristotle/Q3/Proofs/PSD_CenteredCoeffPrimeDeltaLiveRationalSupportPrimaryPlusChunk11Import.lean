import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 11: 11..11.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift11 :
    |centeredBSplineR 11
        (((((-14 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-14 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-14 : Int) 11 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift11 : Rat := ((-185187006944519846663657522704048820920873579566957060487346587863569099311934237095280538728087 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift11 : Rat := ((-27778051041677976999548628405607323138131036935043559073101988179535364896790135564292080809213 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift11 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift11 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift11, activeL3RatLogLo_p19, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift11 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift11 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift11, activeL3RatLogHi_p19, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift11 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift11 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 11 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-14 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift11)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift11)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 11)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift11 :
    |centeredBSplineR 11
        (((((-13 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-13 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-13 : Int) 11 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift11 : Rat := ((-305561020833559539990972568112146462762620738700871181462039763590707297935802711285841616184261 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift11 : Rat := ((-15278051041677976999548628405607323138131036935043559073101988179535364896790135564292080809213 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift11 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift11 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift11, activeL3RatLogLo_p19, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift11 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift11 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift11, activeL3RatLogHi_p19, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift11 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift11 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 11 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-13 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift11)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift11)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 11)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m12_shift11 :
    |centeredBSplineR 11
        (((((-12 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-12 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-12 : Int) 11 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift11 : Rat := ((-55561020833559539990972568112146462762620738700871181462039763590707297935802711285841616184261 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift11 : Rat := ((-926017013892658999849542801869107712710345645014519691033996059845121632263378521430693603071 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-12 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift11 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift11 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift11, activeL3RatLogLo_p19, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift11 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift11 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift11, activeL3RatLogHi_p19, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift11 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift11 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 11 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-12 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift11)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift11)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 11)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m11_shift11 :
    |centeredBSplineR 11
        (((((-11 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-11 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-11 : Int) 11 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift11 : Rat := ((64812993055480153336342477295951179079126420433042939512653412136430900688065762904719461271913 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift11 : Rat := ((9721948958322023000451371594392676861868963064956440926898011820464635103209864435707919190787 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-11 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift11 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift11 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift11, activeL3RatLogLo_p19, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift11 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift11 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift11, activeL3RatLogHi_p19, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift11 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift11 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 11 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-11 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift11)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift11)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 11)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m10_shift11 :
    |centeredBSplineR 11
        (((((-10 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-10 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-10 : Int) 11 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift11 : Rat := ((444438979166440460009027431887853537237379261299128818537960236409292702064197288714158383815739 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift11 : Rat := ((22221948958322023000451371594392676861868963064956440926898011820464635103209864435707919190787 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-10 : Int) activeL3RatWeightIndex11
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift11 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift11 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift11, activeL3RatLogLo_p19, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift11 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex11) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift11 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p19) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift11, activeL3RatLogHi_p19, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift11 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift11 primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift11 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 11 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-10 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift11)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift11)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 11)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 11)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx11
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex11) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 11| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 11 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift11
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift11
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m12_shift11
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m11_shift11
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m10_shift11
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex11.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
