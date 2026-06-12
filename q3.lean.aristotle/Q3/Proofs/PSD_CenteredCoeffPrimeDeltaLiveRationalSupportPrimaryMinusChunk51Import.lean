import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 51: 51..51.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift51 :
    |centeredBSplineR 11
        (((((19 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (19 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (19 : Int) 51 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift51 : Rat := ((-367993812416755107259750776744779365797322602610991599859684746794357594479530948207854162805823 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift51 : Rat := ((-183996906208377553629875388372389682898661301305495799929842373397178797239765474103927081402911 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex51
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift51 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift51 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift51, activeL3RatLogHi_p167, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift51 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift51 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift51, activeL3RatLogLo_p167, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift51 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift51 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 51 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((19 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift51)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift51)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 51)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 51)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift51 :
    |centeredBSplineR 11
        (((((20 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (20 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (20 : Int) 51 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift51 : Rat := ((-117993812416755107259750776744779365797322602610991599859684746794357594479530948207854162805823 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift51 : Rat := ((-19665635402792517876625129457463227632887100435165266643280791132392932413255158034642360467637 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex51
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift51 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift51 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift51, activeL3RatLogHi_p167, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift51 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift51 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift51, activeL3RatLogLo_p167, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift51 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift51 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 51 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((20 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift51)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift51)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 51)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 51)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift51 :
    |centeredBSplineR 11
        (((((21 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (21 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (21 : Int) 51 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift51 : Rat := ((44002062527748297580083074418406878067559132463002800046771751068547468506823017264048612398059 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift51 : Rat := ((66003093791622446370124611627610317101338698694504200070157626602821202760234525896072918597089 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex51
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift51 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift51 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift51, activeL3RatLogHi_p167, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift51 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift51 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift51, activeL3RatLogLo_p167, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift51 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift51 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 51 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((21 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift51)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift51)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 51)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 51)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p22_shift51 :
    |centeredBSplineR 11
        (((((22 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (22 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (22 : Int) 51 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift51 : Rat := ((382006187583244892740249223255220634202677397389008400140315253205642405520469051792145837194177 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift51 : Rat := ((191003093791622446370124611627610317101338698694504200070157626602821202760234525896072918597089 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (22 : Int) activeL3RatWeightIndex51
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift51 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift51 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift51, activeL3RatLogHi_p167, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift51 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex51) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift51 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p167) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift51, activeL3RatLogLo_p167, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift51 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift51 primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift51 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 51 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((22 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift51)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift51)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 51)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 51)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx51
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex51) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 51| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 51 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex51.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift51
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift51
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift51
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p22_shift51

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
