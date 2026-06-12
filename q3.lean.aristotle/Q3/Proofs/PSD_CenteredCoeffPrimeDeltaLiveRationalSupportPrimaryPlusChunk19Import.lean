import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 19: 19..19.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift19 :
    |centeredBSplineR 11
        (((((-17 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-17 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-17 : Int) 19 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift19 : Rat := ((-89404655549282032688872771160432068603931588433449727730122848290003563932390415672947143104669 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift19 : Rat := ((-536427933295692196133236626962592411623589530600698366380737089740021383594342494037682858628013 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift19 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift19 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift19, activeL3RatLogLo_p41, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift19 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift19 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift19, activeL3RatLogHi_p41, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift19 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift19 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 19 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-17 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m17_shift19)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m17_shift19)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 19)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift19 :
    |centeredBSplineR 11
        (((((-16 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-16 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-16 : Int) 19 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift19 : Rat := ((-143213966647846098066618313481296205811794765300349183190368544870010691797171247018841429314007 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift19 : Rat := ((-286427933295692196133236626962592411623589530600698366380737089740021383594342494037682858628013 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift19 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift19 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift19, activeL3RatLogLo_p41, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift19 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift19 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift19, activeL3RatLogHi_p41, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift19 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift19 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 19 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-16 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m16_shift19)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m16_shift19)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 19)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift19 :
    |centeredBSplineR 11
        (((((-15 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-15 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-15 : Int) 19 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift19 : Rat := ((-18213966647846098066618313481296205811794765300349183190368544870010691797171247018841429314007 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift19 : Rat := ((-12142644431897398711078875654197470541196510200232788793579029913340461198114164679227619542671 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift19 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift19 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift19, activeL3RatLogLo_p41, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift19 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift19 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift19, activeL3RatLogHi_p41, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift19 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift19 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 19 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-15 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift19)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift19)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 19)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift19 :
    |centeredBSplineR 11
        (((((-14 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-14 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-14 : Int) 19 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift19 : Rat := ((35595344450717967311127228839567931396068411566550272269877151709996436067609584327052856895331 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift19 : Rat := ((213572066704307803866763373037407588376410469399301633619262910259978616405657505962317141371987 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift19 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift19 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift19, activeL3RatLogLo_p41, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift19 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift19 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift19, activeL3RatLogHi_p41, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift19 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift19 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 19 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-14 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift19)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift19)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 19)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift19 :
    |centeredBSplineR 11
        (((((-13 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-13 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-13 : Int) 19 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift19 : Rat := ((231786033352153901933381686518703794188205234699650816809631455129989308202828752981158570685993 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift19 : Rat := ((463572066704307803866763373037407588376410469399301633619262910259978616405657505962317141371987 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex19
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift19 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift19 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift19, activeL3RatLogLo_p41, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift19 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex19) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift19 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p41) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift19, activeL3RatLogHi_p41, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift19 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift19 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift19 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 19 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-13 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift19)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift19)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 19)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 19)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx19
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex19) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 19| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 19 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m17_shift19
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m16_shift19
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift19
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift19
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift19
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex19.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
