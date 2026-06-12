import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 42: 42..42.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift42 :
    |centeredBSplineR 11
        (((((-21 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-21 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-21 : Int) 42 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift42 : Rat := ((-405812913541408726952559192283707605126090876073914237092734792142814738263424622254104880397497 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift42 : Rat := ((-50726614192676090869069899035463450640761359509239279636591849017851842282928077781763110049687 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex42
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift42 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift42 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift42, activeL3RatLogLo_p127, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift42 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift42 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift42, activeL3RatLogHi_p127, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift42 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift42 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 42 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-21 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m21_shift42)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m21_shift42)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 42)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 42)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift42 :
    |centeredBSplineR 11
        (((((-20 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-20 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-20 : Int) 42 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift42 : Rat := ((-155812913541408726952559192283707605126090876073914237092734792142814738263424622254104880397497 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift42 : Rat := ((-6492204730892030289689966345154483546920453169746426545530616339283947427642692593921036683229 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex42
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift42 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift42 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift42, activeL3RatLogLo_p127, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift42 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift42 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift42, activeL3RatLogHi_p127, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift42 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift42 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 42 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-20 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m20_shift42)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m20_shift42)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 42)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 42)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift42 :
    |centeredBSplineR 11
        (((((-19 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-19 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-19 : Int) 42 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift42 : Rat := ((31395695486197091015813602572097464957969707975361920969088402619061753912191792581965039867501 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift42 : Rat := ((11773385807323909130930100964536549359238640490760720363408150982148157717071922218236889950313 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex42
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift42 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift42 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift42, activeL3RatLogLo_p127, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift42 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift42 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift42, activeL3RatLogHi_p127, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift42 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift42 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 42 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-19 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m19_shift42)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m19_shift42)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 42)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 42)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m18_shift42 :
    |centeredBSplineR 11
        (((((-18 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-18 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-18 : Int) 42 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift42 : Rat := ((344187086458591273047440807716292394873909123926085762907265207857185261736575377745895119602503 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift42 : Rat := ((43023385807323909130930100964536549359238640490760720363408150982148157717071922218236889950313 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex42
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift42 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift42 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift42, activeL3RatLogLo_p127, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift42 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift42 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift42, activeL3RatLogHi_p127, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift42 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift42 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 42 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-18 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m18_shift42)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m18_shift42)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 42)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 42)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift42 :
    |centeredBSplineR 11
        (((((-17 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-17 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-17 : Int) 42 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift42 : Rat := ((594187086458591273047440807716292394873909123926085762907265207857185261736575377745895119602503 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift42 : Rat := ((24757795269107969710310033654845516453079546830253573454469383660716052572357307406078963316771 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex42
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift42 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift42 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift42, activeL3RatLogLo_p127, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift42 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex42) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift42 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p127) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift42, activeL3RatLogHi_p127, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift42 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift42 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift42 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 42 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-17 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift42)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift42)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 42)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 42)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx42
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex42) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 42| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 42 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m21_shift42
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m20_shift42
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m19_shift42
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m18_shift42
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift42
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex42.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
