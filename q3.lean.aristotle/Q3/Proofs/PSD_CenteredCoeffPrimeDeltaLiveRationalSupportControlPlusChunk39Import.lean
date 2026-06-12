import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 39: 39..39.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift39 :
    |centeredBSplineR 9
        (((((-21 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-21 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-21 : Int) 39 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m21_shift39 : Rat := ((-5443876888413119077269463608166440916361141784343814638121374631837771817093228428789686432293 : Rat) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m21_shift39 : Rat := ((-522612181287659431417868506383978327970669611297006205259651964656426094440949929163809897500127 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex39
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift39 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift39 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m21_shift39, activeL3RatLogLo_p113, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift39 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift39 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m21_shift39, activeL3RatLogHi_p113, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift39 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift39 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 39 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-21 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m21_shift39)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m21_shift39)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 39)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 39)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift39 :
    |centeredBSplineR 9
        (((((-20 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-20 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-20 : Int) 39 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m20_shift39 : Rat := ((-8519130665239357231808390824499322749083425353031443914364123895513315451279685286369059296879 : Rat) / 9375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m20_shift39 : Rat := ((-272612181287659431417868506383978327970669611297006205259651964656426094440949929163809897500127 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex39
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift39 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift39 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m20_shift39, activeL3RatLogLo_p113, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift39 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift39 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m20_shift39, activeL3RatLogHi_p113, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift39 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift39 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 39 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-20 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m20_shift39)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m20_shift39)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 39)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 39)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift39 :
    |centeredBSplineR 9
        (((((-19 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-19 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-19 : Int) 39 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m19_shift39 : Rat := ((-706630665239357231808390824499322749083425353031443914364123895513315451279685286369059296879 : Rat) / 9375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m19_shift39 : Rat := ((-7537393762553143805956168794659442656889870432335401753217321552142031480316643054603299166709 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex39
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift39 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift39 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m19_shift39, activeL3RatLogLo_p113, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift39 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift39 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m19_shift39, activeL3RatLogHi_p113, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift39 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift39 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 39 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-19 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m19_shift39)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m19_shift39)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 39)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 39)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift39 :
    |centeredBSplineR 9
        (((((-18 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-18 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-18 : Int) 39 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m18_shift39 : Rat := ((2368623111586880922730536391833559083638858215656185361878625368162228182906771571210313567707 : Rat) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m18_shift39 : Rat := ((227387818712340568582131493616021672029330388702993794740348035343573905559050070836190102499873 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex39
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift39 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift39 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m18_shift39, activeL3RatLogLo_p113, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift39 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift39 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m18_shift39, activeL3RatLogHi_p113, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift39 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift39 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 39 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-18 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m18_shift39)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m18_shift39)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 39)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 39)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift39 :
    |centeredBSplineR 9
        (((((-17 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-17 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-17 : Int) 39 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m17_shift39 : Rat := ((14918369334760642768191609175500677250916574646968556085635876104486684548720314713630940703121 : Rat) / 9375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m17_shift39 : Rat := ((477387818712340568582131493616021672029330388702993794740348035343573905559050070836190102499873 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex39
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift39 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift39 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m17_shift39, activeL3RatLogLo_p113, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift39 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex39) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift39 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p113) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m17_shift39, activeL3RatLogHi_p113, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift39 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift39 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift39 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 39| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 39 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-17 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m17_shift39)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m17_shift39)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 39)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 39)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx39
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex39) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 39| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 39 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift39
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift39
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift39
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift39
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift39
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex39.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
