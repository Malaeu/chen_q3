import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 3: 3..3.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m8_shift3 :
    |centeredBSplineR 11
        (((((-8 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-8 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-8 : Int) 3 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift3 : Rat := ((-130187362521966541799746888924604120158132881910494092695784036175273670764114078456622040635607 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift3 : Rat := ((-19528104378294981269962033338690618023719932286574113904367605426291050614617111768493306095341 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-8 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift3 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift3 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift3, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift3 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift3 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift3, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift3 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift3 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 3 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-8 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift3)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift3)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 3)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m7_shift3 :
    |centeredBSplineR 11
        (((((-7 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-7 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-7 : Int) 3 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift3 : Rat := ((-140562087565899625399240666773812360474398645731482278087352108525821012292342235369866121906821 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift3 : Rat := ((-7028104378294981269962033338690618023719932286574113904367605426291050614617111768493306095341 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-7 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift3 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift3 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift3, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift3 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift3 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift3, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift3 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift3 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 3 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-7 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift3)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift3)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 3)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift3 :
    |centeredBSplineR 11
        (((((-6 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-6 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-6 : Int) 3 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift3 : Rat := ((109437912434100374600759333226187639525601354268517721912647891474178987707657764630133878093179 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift3 : Rat := ((1823965207235006243345988887103127325426689237808628698544131524569649795127629410502231301553 : Rat) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-6 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift3 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift3 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift3, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift3 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift3 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift3, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift3 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift3 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 3 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-6 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift3)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift3)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 3)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m5_shift3 :
    |centeredBSplineR 11
        (((((-5 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-5 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-5 : Int) 3 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift3 : Rat := ((119812637478033458200253111075395879841867118089505907304215963824726329235885921543377959364393 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift3 : Rat := ((17971895621705018730037966661309381976280067713425886095632394573708949385382888231506693904659 : Rat) / 15000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-5 : Int) activeL3RatWeightIndex3
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift3 : Rat) : Real) =
            ((((-5 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift3 : Rat) : Real) = (((((-5 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift3, activeL3RatLogLo_p5, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift3 : Rat) : Real) =
            ((((-5 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex3) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift3 : Rat) : Real) = (((((-5 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p5) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift3, activeL3RatLogHi_p5, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift3 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift3 primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift3 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-5 : Int) 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-5 : Int) 3 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-5 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift3)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift3)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-5 : Int) 3)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-5 : Int) 3)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx3
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex3) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 3| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 3 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m8_shift3
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m7_shift3
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift3
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m5_shift3
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex3.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
