import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` plus-side
declared-support hbox facts, index chunk 7: 7..7.
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


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m11_shift7 :
    |centeredBSplineR 11
        (((((-11 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-11 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-11 : Int) 7 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift7 : Rat := ((-58684121200271575989676070339145116696382191010430470796905381811571062681127214487490881999561 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift7 : Rat := ((-70420945440325891187611284406974140035658629212516564956286458173885275217352657384989058399473 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-11 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift7 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift7 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift7, activeL3RatLogLo_p11, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift7 : Rat) : Real) =
            ((((-11 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift7 : Rat) : Real) = (((((-11 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift7, activeL3RatLogHi_p11, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift7 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift7 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 7 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-11 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m11_shift7)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m11_shift7)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-11 : Int) 7)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-11 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m10_shift7 :
    |centeredBSplineR 11
        (((((-10 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-10 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-10 : Int) 7 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift7 : Rat := ((-51052363600814727969028211017435350089146573031291412390716145434713188043381643462472645998683 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift7 : Rat := ((-20420945440325891187611284406974140035658629212516564956286458173885275217352657384989058399473 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-10 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift7 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift7 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift7, activeL3RatLogLo_p11, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift7 : Rat) : Real) =
            ((((-10 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift7 : Rat) : Real) = (((((-10 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift7, activeL3RatLogHi_p11, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift7 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift7 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 7 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-10 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m10_shift7)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m10_shift7)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-10 : Int) 7)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-10 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m9_shift7 :
    |centeredBSplineR 11
        (((((-9 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-9 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-9 : Int) 7 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift7 : Rat := ((73947636399185272030971788982564649910853426968708587609283854565286811956618356537527354001317 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift7 : Rat := ((9859684853224702937462905197675286654780456929161145014571180608704908260882447538336980533509 : Rat) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-9 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift7 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift7 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift7, activeL3RatLogLo_p11, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift7 : Rat) : Real) =
            ((((-9 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift7 : Rat) : Real) = (((((-9 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift7, activeL3RatLogHi_p11, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift7 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift7 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 7 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-9 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m9_shift7)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m9_shift7)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-9 : Int) 7)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-9 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRPlusHbox_delta_m8_shift7 :
    |centeredBSplineR 11
        (((((-8 : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRPlusMidByDelta (-8 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta (-8 : Int) 7 := by
  let primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift7 : Rat := ((66315878799728424010323929660854883303617808989569529203094618188428937318872785512509118000439 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift7 : Rat := ((79579054559674108812388715593025859964341370787483435043713541826114724782647342615010941600527 : Rat) / 60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRPlus_arg_bounds
      (-8 : Int) activeL3RatWeightIndex7
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift7 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift7 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift7, activeL3RatLogLo_p11, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift7 : Rat) : Real) =
            ((((-8 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex7) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift7 : Rat) : Real) = (((((-8 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p11) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift7, activeL3RatLogHi_p11, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift7 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift7 primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift7 -
            primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 7 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRPlusMidByDelta,
    primaryK11RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((-8 : Int) : Real) / 4 +
        primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRPlusLo_delta_m8_shift7)
      (hi := primaryK11RationalDeltaLiveRPlusHi_delta_m8_shift7)
      (mid := primaryK11RationalDeltaLiveRPlusMidByDeltaRat (-8 : Int) 7)
      (rad := primaryK11RationalDeltaLiveRPlusRadByDeltaRat (-8 : Int) 7)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRPlusHboxDeclared_idx7
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 +
          primaryK11PrimeShift activeL3RatWeightIndex7) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRPlusMidByDelta δInt 7| <=
        primaryK11RationalDeltaLiveRPlusRadByDelta δInt 7 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m11_shift7
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m10_shift7
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m9_shift7
  · exact primaryK11RationalDeltaLiveRPlusHbox_delta_m8_shift7
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex7.1 ∈ primaryK11RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
