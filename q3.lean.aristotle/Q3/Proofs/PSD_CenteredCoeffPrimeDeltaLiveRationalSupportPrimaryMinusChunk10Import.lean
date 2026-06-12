import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 10: 10..10.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift10 :
    |centeredBSplineR 11
        (((((9 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (9 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (9 : Int) 10 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift10 : Rat := ((-194404448018738693416511539291042178529401004195248262432412579294097525266977093637364956012501 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift10 : Rat := ((-291606672028108040124767308936563267794101506292872393648618868941146287900465640456047434018751 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (9 : Int) activeL3RatWeightIndex10
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift10 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift10 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift10, activeL3RatLogHi_p17, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift10 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift10 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift10, activeL3RatLogLo_p17, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift10 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift10 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 10 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((9 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift10)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift10)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 10)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 10)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift10 :
    |centeredBSplineR 11
        (((((10 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (10 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (10 : Int) 10 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift10 : Rat := ((-333213344056216080249534617873126535588203012585744787297237737882292575800931280912094868037503 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift10 : Rat := ((-166606672028108040124767308936563267794101506292872393648618868941146287900465640456047434018751 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (10 : Int) activeL3RatWeightIndex10
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift10 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift10 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift10, activeL3RatLogHi_p17, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift10 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift10 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift10, activeL3RatLogLo_p17, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift10 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift10 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 10 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((10 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift10)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift10)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 10)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 10)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p11_shift10 :
    |centeredBSplineR 11
        (((((11 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (11 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (11 : Int) 10 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift10 : Rat := ((-83213344056216080249534617873126535588203012585744787297237737882292575800931280912094868037503 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift10 : Rat := ((-13868890676036013374922436312187755931367168764290797882872956313715429300155213485349144672917 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (11 : Int) activeL3RatWeightIndex10
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift10 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift10 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift10, activeL3RatLogHi_p17, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift10 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift10 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift10, activeL3RatLogLo_p17, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift10 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift10 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 10 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((11 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift10)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift10)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 10)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 10)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p12_shift10 :
    |centeredBSplineR 11
        (((((12 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (12 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (12 : Int) 10 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift10 : Rat := ((55595551981261306583488460708957821470598995804751737567587420705902474733022906362635043987499 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift10 : Rat := ((83393327971891959875232691063436732205898493707127606351381131058853712099534359543952565981249 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (12 : Int) activeL3RatWeightIndex10
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift10 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift10 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift10, activeL3RatLogHi_p17, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift10 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift10 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift10, activeL3RatLogLo_p17, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift10 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift10 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 10 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((12 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift10)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift10)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 10)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 10)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p13_shift10 :
    |centeredBSplineR 11
        (((((13 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (13 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (13 : Int) 10 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift10 : Rat := ((416786655943783919750465382126873464411796987414255212702762262117707424199068719087905131962497 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift10 : Rat := ((208393327971891959875232691063436732205898493707127606351381131058853712099534359543952565981249 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (13 : Int) activeL3RatWeightIndex10
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift10 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift10 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift10, activeL3RatLogHi_p17, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift10 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex10) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift10 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p17) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift10, activeL3RatLogLo_p17, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift10 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift10 primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift10 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 10 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((13 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift10)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift10)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 10)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 10)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx10
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex10) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 10| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 10 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift10
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift10
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p11_shift10
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p12_shift10
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p13_shift10
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex10.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
