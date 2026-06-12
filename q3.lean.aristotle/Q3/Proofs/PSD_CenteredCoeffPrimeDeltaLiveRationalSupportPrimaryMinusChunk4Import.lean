import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 4: 4..4.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p6_shift4 :
    |centeredBSplineR 11
        (((((6 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (6 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (6 : Int) 4 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p6_shift4 : Rat := ((-13934692157978540784542273232599366551158897799433162139355942185549370711002164618364328080871 : Rat) / 9375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p6_shift4 : Rat := ((-445910149055313305105352743443179729637084729581861188459390149937579862752069267787658498587871 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (6 : Int) activeL3RatWeightIndex4
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p6_shift4 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p6_shift4 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p6_shift4, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p6_shift4 : Rat) : Real) =
            ((((6 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p6_shift4 : Rat) : Real) = (((((6 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p6_shift4, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p6_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p6_shift4 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p6_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p6_shift4 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 4 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((6 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p6_shift4)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p6_shift4)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (6 : Int) 4)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (6 : Int) 4)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p7_shift4 :
    |centeredBSplineR 11
        (((((7 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (7 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (7 : Int) 4 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift4 : Rat := ((-6122192157978540784542273232599366551158897799433162139355942185549370711002164618364328080871 : Rat) / 9375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift4 : Rat := ((-65303383018437768368450914481059909879028243193953729486463383312526620917356422595886166195957 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (7 : Int) activeL3RatWeightIndex4
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift4 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift4 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift4, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift4 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift4 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift4, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift4 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift4 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 4 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((7 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift4)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift4)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 4)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 4)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p8_shift4 :
    |centeredBSplineR 11
        (((((8 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (8 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (8 : Int) 4 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift4 : Rat := ((563435947340486405152575589133544482947034066855612620214685938150209762999278460545223973043 : Rat) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift4 : Rat := ((54089850944686694894647256556820270362915270418138811540609850062420137247930732212341501412129 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (8 : Int) activeL3RatWeightIndex4
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift4 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift4 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift4, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift4 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift4 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift4, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift4 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift4 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 4 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((8 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift4)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift4)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 4)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 4)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift4 :
    |centeredBSplineR 11
        (((((9 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (9 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (9 : Int) 4 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift4 : Rat := ((9502807842021459215457726767400633448841102200566837860644057814450629288997835381635671919129 : Rat) / 9375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift4 : Rat := ((304089850944686694894647256556820270362915270418138811540609850062420137247930732212341501412129 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (9 : Int) activeL3RatWeightIndex4
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift4 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift4 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift4, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift4 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift4 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift4, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift4 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift4 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 4 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((9 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift4)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift4)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 4)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 4)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift4 :
    |centeredBSplineR 11
        (((((10 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (10 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (10 : Int) 4 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift4 : Rat := ((17315307842021459215457726767400633448841102200566837860644057814450629288997835381635671919129 : Rat) / 9375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift4 : Rat := ((184696616981562231631549085518940090120971756806046270513536616687473379082643577404113833804043 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (10 : Int) activeL3RatWeightIndex4
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift4 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift4 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift4, activeL3RatLogHi_p7, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift4 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex4) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift4 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p7) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift4, activeL3RatLogLo_p7, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift4 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift4 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift4 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 4 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((10 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift4)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift4)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 4)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 4)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx4
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex4) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 4| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 4 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p6_shift4
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p7_shift4
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p8_shift4
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift4
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift4
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex4.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
