import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 14: 14..14.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift14 :
    |centeredBSplineR 11
        (((((-15 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-15 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-15 : Int) 14 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift14 : Rat := ((-37846927832972577151188690769368573838127360544312637066326416590626426695347758281596061296567 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift14 : Rat := ((-151387711331890308604754763077474295352509442177250548265305666362505706781391033126384245186267 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift14 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift14 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift14, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift14 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift14 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift14, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift14 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift14 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 14 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-15 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m15_shift14)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m15_shift14)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 14)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift14 :
    |centeredBSplineR 11
        (((((-14 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-14 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-14 : Int) 14 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift14 : Rat := ((-51040783498917731453566072308105721514382081632937911198979249771879280086043274844788183889701 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift14 : Rat := ((-204163133995670925814264289232422886057528326531751644795916999087517120344173099379152735558801 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift14 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift14 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift14, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift14 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift14 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift14, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift14 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift14 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 14 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-14 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m14_shift14)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m14_shift14)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 14)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift14 :
    |centeredBSplineR 11
        (((((-13 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-13 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-13 : Int) 14 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift14 : Rat := ((11459216501082268546433927691894278485617918367062088801020750228120719913956725155211816110299 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift14 : Rat := ((45836866004329074185735710767577113942471673468248355204083000912482879655826900620847264441199 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift14 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift14 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift14, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift14 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift14 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift14, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift14 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift14 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 14 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-13 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m13_shift14)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m13_shift14)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 14)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m12_shift14 :
    |centeredBSplineR 11
        (((((-12 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-12 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-12 : Int) 14 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift14 : Rat := ((24653072167027422848811309230631426161872639455687362933673583409373573304652241718403938703433 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift14 : Rat := ((98612288668109691395245236922525704647490557822749451734694333637494293218608966873615754813733 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-12 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift14 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift14 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift14, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift14 : Rat) : Real) =
            ((((-12 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift14 : Rat) : Real) = (((((-12 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift14, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift14 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift14 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 14 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-12 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m12_shift14)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m12_shift14)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-12 : Int) 14)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-12 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m11_shift14 :
    |centeredBSplineR 11
        (((((-11 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-11 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-11 : Int) 14 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift14 : Rat := ((136459216501082268546433927691894278485617918367062088801020750228120719913956725155211816110299 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift14 : Rat := ((545836866004329074185735710767577113942471673468248355204083000912482879655826900620847264441199 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-11 : Int) activeL3RatWeightIndex14
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift14 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift14 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogLo_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift14, activeL3RatLogLo_p3, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift14 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex14) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift14 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((3 : Nat) : Real) * activeL3RatLogHi_p3) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift14, activeL3RatLogHi_p3, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift14 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift14 primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift14 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 14 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-11 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift14)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift14)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 14)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 14)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx14
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex14) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 14| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 14 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m15_shift14
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m14_shift14
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m13_shift14
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m12_shift14
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m11_shift14
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex14.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
