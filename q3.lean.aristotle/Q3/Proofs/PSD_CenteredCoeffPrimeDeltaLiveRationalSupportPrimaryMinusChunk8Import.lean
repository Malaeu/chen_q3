import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 8: 8..8.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p8_shift8 :
    |centeredBSplineR 11
        (((((8 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (8 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (8 : Int) 8 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift8 : Rat := ((-18831645248717891201782914718843953493508931492006903880634850355448822244147005979985822114683 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift8 : Rat := ((-564949357461536736053487441565318604805267944760207116419045510663464667324410179399574663440489 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (8 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift8 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift8 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift8, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift8 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift8 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift8, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift8 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift8 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 8 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((8 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift8)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift8)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 8)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift8 :
    |centeredBSplineR 11
        (((((9 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (9 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (9 : Int) 8 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift8 : Rat := ((-31494935746153673605348744156531860480526794476020711641904551066346466732441017939957466344049 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift8 : Rat := ((-314949357461536736053487441565318604805267944760207116419045510663464667324410179399574663440489 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (9 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift8 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift8 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift8, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift8 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift8 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift8, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift8 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift8 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 8 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((9 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift8)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift8)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 8)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift8 :
    |centeredBSplineR 11
        (((((10 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (10 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (10 : Int) 8 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift8 : Rat := ((-6494935746153673605348744156531860480526794476020711641904551066346466732441017939957466344049 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift8 : Rat := ((-21649785820512245351162480521772868268422648253402372139681836887821555774803393133191554480163 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (10 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift8 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift8 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift8, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift8 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift8 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift8, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift8 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift8 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 8 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((10 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift8)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift8)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 8)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p11_shift8 :
    |centeredBSplineR 11
        (((((11 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (11 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (11 : Int) 8 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift8 : Rat := ((6168354751282108798217085281156046506491068507993096119365149644551177755852994020014177885317 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift8 : Rat := ((185050642538463263946512558434681395194732055239792883580954489336535332675589820600425336559511 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (11 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift8 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift8 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift8, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift8 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift8 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift8, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift8 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift8 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 8 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((11 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift8)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift8)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 8)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p12_shift8 :
    |centeredBSplineR 11
        (((((12 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (12 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (12 : Int) 8 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift8 : Rat := ((43505064253846326394651255843468139519473205523979288358095448933653533267558982060042533655951 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift8 : Rat := ((435050642538463263946512558434681395194732055239792883580954489336535332675589820600425336559511 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (12 : Int) activeL3RatWeightIndex8
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift8 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift8 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift8, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift8 : Rat) : Real) =
            ((((12 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex8) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift8 : Rat) : Real) = (((((12 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift8, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift8 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift8 primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift8 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 8 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((12 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p12_shift8)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p12_shift8)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (12 : Int) 8)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (12 : Int) 8)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx8
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex8) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 8| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 8 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p8_shift8
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift8
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift8
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p11_shift8
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p12_shift8
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex8.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
