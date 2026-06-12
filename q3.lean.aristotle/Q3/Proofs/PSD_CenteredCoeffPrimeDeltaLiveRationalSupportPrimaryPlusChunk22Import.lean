import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 22: 22..22.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift22 :
    |centeredBSplineR 11
        (((((-17 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-17 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-17 : Int) 22 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift22 : Rat := ((-59696616981562231631549085518940090120971756806046270513536616687473379082643577404113833804043 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift22 : Rat := ((-5596557842021459215457726767400633448841102200566837860644057814450629288997835381635671919129 : Rat) / 4687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift22 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift22 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift22, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift22 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift22 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift22, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift22 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift22 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 22 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-17 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift22)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift22)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 22)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift22 :
    |centeredBSplineR 11
        (((((-16 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-16 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-16 : Int) 22 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift22 : Rat := ((-54089850944686694894647256556820270362915270418138811540609850062420137247930732212341501412129 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift22 : Rat := ((-563435947340486405152575589133544482947034066855612620214685938150209762999278460545223973043 : Rat) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift22 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift22 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift22, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift22 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift22 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift22, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift22 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift22 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 22 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-16 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift22)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift22)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 22)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift22 :
    |centeredBSplineR 11
        (((((-15 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-15 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-15 : Int) 22 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift22 : Rat := ((70910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587871 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift22 : Rat := ((2215942157978540784542273232599366551158897799433162139355942185549370711002164618364328080871 : Rat) / 4687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift22 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift22 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift22, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift22 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift22 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift22, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift22 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift22 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 22 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-15 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift22)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift22)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 22)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift22 :
    |centeredBSplineR 11
        (((((-14 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-14 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-14 : Int) 22 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift22 : Rat := ((65303383018437768368450914481059909879028243193953729486463383312526620917356422595886166195957 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift22 : Rat := ((6122192157978540784542273232599366551158897799433162139355942185549370711002164618364328080871 : Rat) / 4687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex22
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift22 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift22 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift22, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift22 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex22) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift22 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((2 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift22, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift22 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift22 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift22 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 22 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-14 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift22)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift22)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 22)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 22)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx22
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex22) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 22| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 22 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift22
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift22
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift22
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift22
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex22.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
