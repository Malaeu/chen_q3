import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 41: 41..41.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p17_shift41 :
    |centeredBSplineR 11
        (((((17 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (17 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (17 : Int) 41 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift41 : Rat := ((-28915686865115056190113899983928145928840203140277658286897183721126848156148664694520081713977 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift41 : Rat := ((-578313737302301123802277999678562918576804062805553165737943674422536963122973293890401634279537 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (17 : Int) activeL3RatWeightIndex41
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift41 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift41 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift41, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift41 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift41 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift41, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift41 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift41 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 41 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((17 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p17_shift41)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p17_shift41)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 41)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 41)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p18_shift41 :
    |centeredBSplineR 11
        (((((18 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (18 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (18 : Int) 41 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift41 : Rat := ((-5471895621705018730037966661309381976280067713425886095632394573708949385382888231506693904659 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift41 : Rat := ((-109437912434100374600759333226187639525601354268517721912647891474178987707657764630133878093179 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex41
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift41 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift41 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift41, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift41 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift41 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift41, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift41 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift41 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 41 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((18 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift41)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift41)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 41)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 41)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift41 :
    |centeredBSplineR 11
        (((((19 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (19 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (19 : Int) 41 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift41 : Rat := ((-3915686865115056190113899983928145928840203140277658286897183721126848156148664694520081713977 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift41 : Rat := ((-78313737302301123802277999678562918576804062805553165737943674422536963122973293890401634279537 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex41
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift41 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift41 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift41, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift41 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift41 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift41, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift41 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift41 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 41 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((19 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift41)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift41)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 41)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 41)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift41 :
    |centeredBSplineR 11
        (((((20 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (20 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (20 : Int) 41 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift41 : Rat := ((8584313134884943809886100016071854071159796859722341713102816278873151843851335305479918286023 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift41 : Rat := ((171686262697698876197722000321437081423195937194446834262056325577463036877026706109598365720463 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex41
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift41 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift41 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift41, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift41 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift41 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift41, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift41 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift41 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 41 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((20 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift41)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift41)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 41)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 41)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift41 :
    |centeredBSplineR 11
        (((((21 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (21 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (21 : Int) 41 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift41 : Rat := ((7028104378294981269962033338690618023719932286574113904367605426291050614617111768493306095341 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift41 : Rat := ((140562087565899625399240666773812360474398645731482278087352108525821012292342235369866121906821 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex41
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift41 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift41 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift41, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift41 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex41) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift41 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((3 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift41, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift41 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift41 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift41 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 41 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((21 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift41)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift41)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 41)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 41)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx41
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex41) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 41| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 41 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p17_shift41
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p18_shift41
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift41
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift41
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift41
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex41.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
