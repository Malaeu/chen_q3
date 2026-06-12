import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 31: 31..31.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift31 :
    |centeredBSplineR 11
        (((((-19 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-19 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-19 : Int) 31 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift31 : Rat := ((-7407309277657525717062896923122857946042453514770879022108805530208808898449252760532020432189 : Rat) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift31 : Rat := ((-88887711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex31
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift31 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift31 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift31, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift31 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift31 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift31, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift31 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift31 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 31 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-19 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift31)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift31)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 31)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 31)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m18_shift31 :
    |centeredBSplineR 11
        (((((-18 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-18 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-18 : Int) 31 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift31 : Rat := ((-6596927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 18750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift31 : Rat := ((-26387711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex31
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift31 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift31 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift31, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift31 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift31 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift31, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift31 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift31 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 31 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-18 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift31)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift31)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 31)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 31)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift31 :
    |centeredBSplineR 11
        (((((-17 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-17 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-17 : Int) 31 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift31 : Rat := ((9028072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 18750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift31 : Rat := ((12037429556036563798415078974175234882496852607583150578231444545831431072869655624538584937911 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex31
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift31 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift31 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift31, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift31 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift31 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift31, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift31 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift31 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 31 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-17 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift31)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift31)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 31)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 31)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift31 :
    |centeredBSplineR 11
        (((((-16 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-16 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-16 : Int) 31 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift31 : Rat := ((8217690722342474282937103076877142053957546485229120977891194469791191101550747239467979567811 : Rat) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift31 : Rat := ((98612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex31
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift31 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift31 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift31, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift31 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex31) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift31 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((4 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift31, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift31 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift31 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift31 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 31 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-16 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift31)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift31)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 31)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 31)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx31
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex31) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 31| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 31 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift31
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m18_shift31
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift31
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift31
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex31.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
