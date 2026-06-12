import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 1: 1..1.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift1 :
    |centeredBSplineR 11
        (((((-6 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-6 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-6 : Int) 1 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift1 : Rat := ((-100346927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift1 : Rat := ((-401387711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-6 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift1 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift1 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift1, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift1 : Rat) : Real) =
            ((((-6 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift1 : Rat) : Real) = (((((-6 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift1, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift1 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift1 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 1 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-6 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m6_shift1)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m6_shift1)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-6 : Int) 1)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-6 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m5_shift1 :
    |centeredBSplineR 11
        (((((-5 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-5 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-5 : Int) 1 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift1 : Rat := ((-37846927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift1 : Rat := ((-50462570443963436201584921025824765117503147392416849421768555454168568927130344375461415062089 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-5 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift1 : Rat) : Real) =
            ((((-5 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift1 : Rat) : Real) = (((((-5 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift1, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift1 : Rat) : Real) =
            ((((-5 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift1 : Rat) : Real) = (((((-5 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift1, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift1 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift1 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-5 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-5 : Int) 1 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-5 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m5_shift1)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m5_shift1)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-5 : Int) 1)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-5 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m4_shift1 :
    |centeredBSplineR 11
        (((((-4 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-4 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-4 : Int) 1 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift1 : Rat := ((8217690722342474282937103076877142053957546485229120977891194469791191101550747239467979567811 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift1 : Rat := ((98612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-4 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift1 : Rat) : Real) =
            ((((-4 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift1 : Rat) : Real) = (((((-4 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift1, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift1 : Rat) : Real) =
            ((((-4 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift1 : Rat) : Real) = (((((-4 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift1, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift1 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift1 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-4 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-4 : Int) 1 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-4 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m4_shift1)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m4_shift1)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-4 : Int) 1)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-4 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m3_shift1 :
    |centeredBSplineR 11
        (((((-3 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-3 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-3 : Int) 1 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m3_shift1 : Rat := ((87153072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m3_shift1 : Rat := ((348612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-3 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m3_shift1 : Rat) : Real) =
            ((((-3 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m3_shift1 : Rat) : Real) = (((((-3 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m3_shift1, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m3_shift1 : Rat) : Real) =
            ((((-3 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m3_shift1 : Rat) : Real) = (((((-3 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m3_shift1, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m3_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m3_shift1 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m3_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m3_shift1 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-3 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-3 : Int) 1 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-3 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m3_shift1)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m3_shift1)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-3 : Int) 1)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-3 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m2_shift1 :
    |centeredBSplineR 11
        (((((-2 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-2 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-2 : Int) 1 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m2_shift1 : Rat := ((149653072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m2_shift1 : Rat := ((199537429556036563798415078974175234882496852607583150578231444545831431072869655624538584937911 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-2 : Int) activeL3RatWeightIndex1
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m2_shift1 : Rat) : Real) =
            ((((-2 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m2_shift1 : Rat) : Real) = (((((-2 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m2_shift1, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m2_shift1 : Rat) : Real) =
            ((((-2 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex1) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m2_shift1 : Rat) : Real) = (((((-2 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m2_shift1, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m2_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m2_shift1 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m2_shift1 primaryK11RationalDeltaLiveRPlusHi_delta_m2_shift1 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-2 : Int) 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-2 : Int) 1 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-2 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m2_shift1)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m2_shift1)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-2 : Int) 1)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-2 : Int) 1)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx1
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex1) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 1| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 1 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m6_shift1
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m5_shift1
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m4_shift1
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m3_shift1
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m2_shift1
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex1.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
