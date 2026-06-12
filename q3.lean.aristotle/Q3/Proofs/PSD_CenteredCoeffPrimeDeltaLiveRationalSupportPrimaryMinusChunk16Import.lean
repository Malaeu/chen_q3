import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 16: 16..16.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p12_shift16 :
    |centeredBSplineR 11
        (((((12 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (12 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (12 : Int) 16 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift16 : Rat := ((-433987204485146245929164324542357210449938930480591971756718072474981416597551232213864831336087 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift16 : Rat := ((-72331200747524374321527387423726201741656488413431995292786345412496902766258538702310805222681 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (12 : Int) activeL3RatWeightIndex16
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift16 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift16 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift16, activeL3RatLogHi_p31, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift16 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift16 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift16, activeL3RatLogLo_p31, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift16 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift16 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 16 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((12 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift16)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift16)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 16)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 16)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p13_shift16 :
    |centeredBSplineR 11
        (((((13 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (13 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (13 : Int) 16 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift16 : Rat := ((-61329068161715415309721441514119070149979643493530657252239357491660472199183744071288277112029 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift16 : Rat := ((-91993602242573122964582162271178605224969465240295985878359036237490708298775616106932415668043 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (13 : Int) activeL3RatWeightIndex16
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift16 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift16 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift16, activeL3RatLogHi_p31, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift16 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift16 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift16, activeL3RatLogLo_p31, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift16 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift16 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 16 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((13 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift16)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift16)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 16)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 16)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p14_shift16 :
    |centeredBSplineR 11
        (((((14 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (14 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (14 : Int) 16 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift16 : Rat := ((66012795514853754070835675457642789550061069519408028243281927525018583402448767786135168663913 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift16 : Rat := ((33006397757426877035417837728821394775030534759704014121640963762509291701224383893067584331957 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (14 : Int) activeL3RatWeightIndex16
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift16 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift16 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift16, activeL3RatLogHi_p31, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift16 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift16 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift16, activeL3RatLogLo_p31, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift16 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift16 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 16 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((14 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift16)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift16)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 16)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 16)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p15_shift16 :
    |centeredBSplineR 11
        (((((15 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (15 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (15 : Int) 16 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift16 : Rat := ((316012795514853754070835675457642789550061069519408028243281927525018583402448767786135168663913 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift16 : Rat := ((52668799252475625678472612576273798258343511586568004707213654587503097233741461297689194777319 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (15 : Int) activeL3RatWeightIndex16
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift16 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift16 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift16, activeL3RatLogHi_p31, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift16 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift16 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift16, activeL3RatLogLo_p31, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift16 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift16 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 16 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((15 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift16)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift16)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 16)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 16)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p16_shift16 :
    |centeredBSplineR 11
        (((((16 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (16 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (16 : Int) 16 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift16 : Rat := ((188670931838284584690278558485880929850020356506469342747760642508339527800816255928711722887971 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift16 : Rat := ((283006397757426877035417837728821394775030534759704014121640963762509291701224383893067584331957 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (16 : Int) activeL3RatWeightIndex16
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift16 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift16 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift16, activeL3RatLogHi_p31, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift16 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex16) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift16 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p31) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift16, activeL3RatLogLo_p31, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift16 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift16 primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift16 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 16 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((16 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift16)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift16)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 16)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 16)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx16
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex16) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 16| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 16 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p12_shift16
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p13_shift16
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p14_shift16
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p15_shift16
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p16_shift16
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex16.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
