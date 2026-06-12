import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 25: 25..25.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p15_shift25 :
    |centeredBSplineR 11
        (((((15 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (15 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (15 : Int) 25 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift25 : Rat := ((-15036411007221302031307879309400614429820072628385877622390985267476658618539530466059550254171 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift25 : Rat := ((-360873864173311248751389103425614746315681743081261062937383646419439806844948731185429206100103 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (15 : Int) activeL3RatWeightIndex25
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift25 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift25 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift25, activeL3RatLogHi_p61, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift25 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift25 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift25, activeL3RatLogLo_p61, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift25 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift25 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 25 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((15 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift25)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift25)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 25)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 25)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p16_shift25 :
    |centeredBSplineR 11
        (((((16 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (16 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (16 : Int) 25 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift25 : Rat := ((-13859233021663906093923637928201843289460217885157632867172955802429975855618591398178650762513 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift25 : Rat := ((-110873864173311248751389103425614746315681743081261062937383646419439806844948731185429206100103 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (16 : Int) activeL3RatWeightIndex25
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift25 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift25 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift25, activeL3RatLogHi_p61, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift25 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift25 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift25, activeL3RatLogLo_p61, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift25 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift25 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 25 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((16 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift25)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift25)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 25)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 25)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p17_shift25 :
    |centeredBSplineR 11
        (((((17 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (17 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (17 : Int) 25 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift25 : Rat := ((17390766978336093906076362071798156710539782114842367132827044197570024144381408601821349237487 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift25 : Rat := ((46375378608896250416203632191461751228106085639579645687538784526853397718350422938190264633299 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (17 : Int) activeL3RatWeightIndex25
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift25 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift25 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift25, activeL3RatLogHi_p61, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift25 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift25 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift25, activeL3RatLogLo_p61, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift25 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift25 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 25 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((17 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift25)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift25)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 25)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 25)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p18_shift25 :
    |centeredBSplineR 11
        (((((18 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (18 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (18 : Int) 25 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift25 : Rat := ((16213588992778697968692120690599385570179927371614122377609014732523341381460469533940449745829 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift25 : Rat := ((389126135826688751248610896574385253684318256918738937062616353580560193155051268814570793899897 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex25
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift25 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift25 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift25, activeL3RatLogHi_p61, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift25 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex25) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift25 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p61) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift25, activeL3RatLogLo_p61, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift25 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift25 primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift25 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 25 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((18 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift25)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift25)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 25)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 25)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx25
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex25) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 25| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 25 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p15_shift25
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p16_shift25
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p17_shift25
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p18_shift25
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex25.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
