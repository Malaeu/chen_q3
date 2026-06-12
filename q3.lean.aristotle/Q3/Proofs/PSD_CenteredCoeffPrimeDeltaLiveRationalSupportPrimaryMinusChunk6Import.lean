import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 6: 6..6.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p7_shift6 :
    |centeredBSplineR 11
        (((((7 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (7 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (7 : Int) 6 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift6 : Rat := ((-74537429556036563798415078974175234882496852607583150578231444545831431072869655624538584937911 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift6 : Rat := ((-55903072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (7 : Int) activeL3RatWeightIndex6
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift6 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift6 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift6, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift6 : Rat) : Real) =
            ((((7 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift6 : Rat) : Real) = (((((7 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift6, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift6 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift6 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 6 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((7 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p7_shift6)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p7_shift6)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (7 : Int) 6)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (7 : Int) 6)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p8_shift6 :
    |centeredBSplineR 11
        (((((8 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (8 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (8 : Int) 6 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift6 : Rat := ((-98612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift6 : Rat := ((-8217690722342474282937103076877142053957546485229120977891194469791191101550747239467979567811 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (8 : Int) activeL3RatWeightIndex6
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift6 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift6 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift6, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift6 : Rat) : Real) =
            ((((8 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift6 : Rat) : Real) = (((((8 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift6, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift6 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift6 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 6 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((8 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p8_shift6)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p8_shift6)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (8 : Int) 6)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (8 : Int) 6)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift6 :
    |centeredBSplineR 11
        (((((9 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (9 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (9 : Int) 6 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift6 : Rat := ((26387711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift6 : Rat := ((6596927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (9 : Int) activeL3RatWeightIndex6
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift6 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift6 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift6, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift6 : Rat) : Real) =
            ((((9 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift6 : Rat) : Real) = (((((9 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift6, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift6 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift6 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 6 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((9 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p9_shift6)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p9_shift6)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (9 : Int) 6)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (9 : Int) 6)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift6 :
    |centeredBSplineR 11
        (((((10 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (10 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (10 : Int) 6 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift6 : Rat := ((50462570443963436201584921025824765117503147392416849421768555454168568927130344375461415062089 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift6 : Rat := ((37846927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (10 : Int) activeL3RatWeightIndex6
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift6 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift6 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift6, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift6 : Rat) : Real) =
            ((((10 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift6 : Rat) : Real) = (((((10 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift6, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift6 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift6 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 6 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((10 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p10_shift6)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p10_shift6)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (10 : Int) 6)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (10 : Int) 6)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p11_shift6 :
    |centeredBSplineR 11
        (((((11 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (11 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (11 : Int) 6 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift6 : Rat := ((276387711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift6 : Rat := ((23032309277657525717062896923122857946042453514770879022108805530208808898449252760532020432189 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (11 : Int) activeL3RatWeightIndex6
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift6 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift6 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift6, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift6 : Rat) : Real) =
            ((((11 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex6) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift6 : Rat) : Real) = (((((11 : Int) : Real) / 4 - ((2 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift6, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift6 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift6 primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift6 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 6 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((11 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p11_shift6)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p11_shift6)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (11 : Int) 6)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (11 : Int) 6)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx6
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex6) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 6| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 6 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p7_shift6
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p8_shift6
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p9_shift6
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p10_shift6
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p11_shift6
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex6.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
