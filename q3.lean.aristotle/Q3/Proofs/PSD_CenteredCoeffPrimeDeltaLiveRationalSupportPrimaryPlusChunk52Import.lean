import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 52: 52..52.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift52 :
    |centeredBSplineR 11
        (((((-22 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-22 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-22 : Int) 52 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift52 : Rat := ((-185050642538463263946512558434681395194732055239792883580954489336535332675589820600425336559511 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift52 : Rat := ((-6168354751282108798217085281156046506491068507993096119365149644551177755852994020014177885317 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-22 : Int) activeL3RatWeightIndex52
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift52 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift52 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift52, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift52 : Rat) : Real) =
            ((((-22 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift52 : Rat) : Real) = (((((-22 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift52, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift52 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift52 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 52 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-22 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m22_shift52)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m22_shift52)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-22 : Int) 52)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-22 : Int) 52)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift52 :
    |centeredBSplineR 11
        (((((-21 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-21 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-21 : Int) 52 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift52 : Rat := ((-60050642538463263946512558434681395194732055239792883580954489336535332675589820600425336559511 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift52 : Rat := ((-6005064253846326394651255843468139519473205523979288358095448933653533267558982060042533655951 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex52
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift52 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift52 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift52, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift52 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift52 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift52, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift52 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift52 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 52 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-21 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift52)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift52)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 52)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 52)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift52 :
    |centeredBSplineR 11
        (((((-20 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-20 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-20 : Int) 52 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift52 : Rat := ((21649785820512245351162480521772868268422648253402372139681836887821555774803393133191554480163 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift52 : Rat := ((6494935746153673605348744156531860480526794476020711641904551066346466732441017939957466344049 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex52
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift52 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift52 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift52, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift52 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift52 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift52, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift52 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift52 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 52 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-20 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift52)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift52)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 52)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 52)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift52 :
    |centeredBSplineR 11
        (((((-19 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-19 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-19 : Int) 52 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift52 : Rat := ((189949357461536736053487441565318604805267944760207116419045510663464667324410179399574663440489 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift52 : Rat := ((6331645248717891201782914718843953493508931492006903880634850355448822244147005979985822114683 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex52
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift52 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift52 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift52, activeL3RatLogLo_p13, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift52 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex52) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift52 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p13) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift52, activeL3RatLogHi_p13, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift52 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift52 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift52 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 52 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-19 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift52)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift52)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 52)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 52)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx52
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex52) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 52| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 52 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m22_shift52
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift52
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift52
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift52
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex52.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
