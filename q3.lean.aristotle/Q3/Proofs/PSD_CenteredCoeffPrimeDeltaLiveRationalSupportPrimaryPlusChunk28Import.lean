import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 28: 28..28.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift28 :
    |centeredBSplineR 11
        (((((-19 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-19 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-19 : Int) 28 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift28 : Rat := ((-97464024591736915734109093497393180648084694657886778375714839594529698635153926806751335145473 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift28 : Rat := ((-40610010246557048222545455623913825270035289440786157656547849831054041097980802836146389643947 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift28 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift28 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift28, activeL3RatLogLo_p71, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift28 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift28 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift28, activeL3RatLogHi_p71, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift28 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift28 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 28 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-19 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift28)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift28)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 28)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m18_shift28 :
    |centeredBSplineR 11
        (((((-18 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-18 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-18 : Int) 28 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift28 : Rat := ((-15821341530578971911369697832464393549361564885962259458571613198176566211717975602250445048491 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift28 : Rat := ((-59330030739671144667636366871741475810105868322358472969643549493162123293942408508439168931841 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift28 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift28 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift28, activeL3RatLogLo_p71, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift28 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift28 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift28, activeL3RatLogHi_p71, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift28 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift28 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 28 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-18 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift28)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift28)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 28)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift28 :
    |centeredBSplineR 11
        (((((-17 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-17 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-17 : Int) 28 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift28 : Rat := ((2535975408263084265890906502606819351915305342113221624285160405470301364846073193248664854527 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift28 : Rat := ((3169969260328855332363633128258524189894131677641527030356450506837876706057591491560831068159 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift28 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift28 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift28, activeL3RatLogLo_p71, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift28 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift28 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift28, activeL3RatLogHi_p71, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift28 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift28 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 28 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-17 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift28)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift28)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 28)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift28 :
    |centeredBSplineR 11
        (((((-16 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-16 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-16 : Int) 28 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift28 : Rat := ((52535975408263084265890906502606819351915305342113221624285160405470301364846073193248664854527 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift28 : Rat := ((21889989753442951777454544376086174729964710559213842343452150168945958902019197163853610356053 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift28 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift28 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift28, activeL3RatLogLo_p71, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift28 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift28 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift28, activeL3RatLogHi_p71, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift28 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift28 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 28 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-16 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift28)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift28)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 28)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift28 :
    |centeredBSplineR 11
        (((((-15 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-15 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-15 : Int) 28 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift28 : Rat := ((34178658469421028088630302167535606450638435114037740541428386801823433788282024397749554951509 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift28 : Rat := ((128169969260328855332363633128258524189894131677641527030356450506837876706057591491560831068159 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex28
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift28 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift28 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift28, activeL3RatLogLo_p71, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift28 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex28) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift28 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p71) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift28, activeL3RatLogHi_p71, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift28 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift28 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift28 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 28 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-15 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift28)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift28)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 28)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 28)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx28
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex28) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 28| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 28 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift28
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m18_shift28
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift28
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift28
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift28
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex28.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
