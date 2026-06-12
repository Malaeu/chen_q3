import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 2: 2..2.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m7_shift2 :
    |centeredBSplineR 11
        (((((-7 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-7 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-7 : Int) 2 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift2 : Rat := ((-30308803240009115097127979756970571987416644273290790979886665084434396338384214065689445500597 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift2 : Rat := ((-181852819440054690582767878541823431924499865639744745879319990506606378030305284394136673003581 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-7 : Int) activeL3RatWeightIndex2
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift2 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift2 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift2, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift2 : Rat) : Real) =
            ((((-7 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift2 : Rat) : Real) = (((((-7 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift2, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift2 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift2 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 2 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-7 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m7_shift2)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m7_shift2)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-7 : Int) 2)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-7 : Int) 2)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift2 :
    |centeredBSplineR 11
        (((((-6 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-6 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-6 : Int) 2 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift2 : Rat := ((-28426409720027345291383939270911715962249932819872372939659995253303189015152642197068336501791 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift2 : Rat := ((-18950939813351563527589292847274477308166621879914915293106663502202126010101761464712224334527 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-6 : Int) activeL3RatWeightIndex2
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift2 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift2 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift2, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift2 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift2 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift2, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift2 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift2 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 2 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-6 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift2)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift2)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 2)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 2)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m5_shift2 :
    |centeredBSplineR 11
        (((((-5 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-5 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-5 : Int) 2 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift2 : Rat := ((34073590279972654708616060729088284037750067180127627060340004746696810984847357802931663498209 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift2 : Rat := ((68147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-5 : Int) activeL3RatWeightIndex2
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift2 : Rat) : Real) =
            ((((-5 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift2 : Rat) : Real) = (((((-5 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift2, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift2 : Rat) : Real) =
            ((((-5 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift2 : Rat) : Real) = (((((-5 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift2, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift2 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift2 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-5 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-5 : Int) 2 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-5 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift2)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift2)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-5 : Int) 2)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-5 : Int) 2)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m4_shift2 :
    |centeredBSplineR 11
        (((((-4 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-4 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-4 : Int) 2 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift2 : Rat := ((32191196759990884902872020243029428012583355726709209020113334915565603661615785934310554499403 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift2 : Rat := ((193147180559945309417232121458176568075500134360255254120680009493393621969694715605863326996419 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-4 : Int) activeL3RatWeightIndex2
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift2 : Rat) : Real) =
            ((((-4 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift2 : Rat) : Real) = (((((-4 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift2, activeL3RatLogLo_p2, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift2 : Rat) : Real) =
            ((((-4 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex2) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift2 : Rat) : Real) = (((((-4 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p2) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift2, activeL3RatLogHi_p2, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift2 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift2 primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift2 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-4 : Int) 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-4 : Int) 2 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-4 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift2)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift2)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-4 : Int) 2)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-4 : Int) 2)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx2
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex2) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 2| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 2 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m7_shift2
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift2
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m5_shift2
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m4_shift2
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex2.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
