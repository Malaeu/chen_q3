import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 56: 56..56.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift56 :
    |centeredBSplineR 11
        (((((19 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (19 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (19 : Int) 56 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift56 : Rat := ((-41856119003885822737495829350197262217370123038962252623392657294057786600508863979647342074877 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift56 : Rat := ((-502273428046629872849949952202367146608441476467547031480711887528693439206106367755768104898523 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex56
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift56 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift56 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift56, activeL3RatLogHi_p191, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift56 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift56 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift56, activeL3RatLogLo_p191, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift56 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift56 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 56 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((19 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift56)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift56)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 56)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 56)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift56 :
    |centeredBSplineR 11
        (((((20 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (20 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (20 : Int) 56 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift56 : Rat := ((-63068357011657468212487488050591786652110369116886757870177971882173359801526591938942026224631 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift56 : Rat := ((-252273428046629872849949952202367146608441476467547031480711887528693439206106367755768104898523 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex56
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift56 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift56 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift56, activeL3RatLogHi_p191, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift56 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift56 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift56, activeL3RatLogLo_p191, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift56 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift56 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 56 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((20 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift56)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift56)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 56)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 56)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift56 :
    |centeredBSplineR 11
        (((((21 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (21 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (21 : Int) 56 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift56 : Rat := ((-568357011657468212487488050591786652110369116886757870177971882173359801526591938942026224631 : Rat) / 75000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift56 : Rat := ((-757809348876624283316650734122382202813825489182343826903962509564479735368789251922701632841 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex56
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift56 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift56 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift56, activeL3RatLogHi_p191, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift56 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift56 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift56, activeL3RatLogLo_p191, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift56 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift56 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 56 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((21 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift56)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift56)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 56)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 56)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p22_shift56 :
    |centeredBSplineR 11
        (((((22 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (22 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (22 : Int) 56 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift56 : Rat := ((20643880996114177262504170649802737782629876961037747376607342705942213399491136020352657925123 : Rat) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift56 : Rat := ((247726571953370127150050047797632853391558523532452968519288112471306560793893632244231895101477 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (22 : Int) activeL3RatWeightIndex56
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift56 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift56 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift56, activeL3RatLogHi_p191, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift56 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex56) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift56 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p191) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift56, activeL3RatLogLo_p191, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift56 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift56 primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift56 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 56 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((22 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift56)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift56)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 56)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 56)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx56
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex56) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 56| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 56 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex56.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift56
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift56
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift56
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p22_shift56

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
