import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 18: 18..18.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p13_shift18 :
    |centeredBSplineR 11
        (((((13 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (13 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (13 : Int) 18 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift18 : Rat := ((-120305970881408148122698557010482387966692529055878721214970893730996582330120355133007177890723 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift18 : Rat := ((-45114739080528055546011958878930895487509698395954520455614085149123718373795133174877691709021 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (13 : Int) activeL3RatWeightIndex18
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift18 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift18 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift18, activeL3RatLogHi_p37, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift18 : Rat) : Real) =
            ((((13 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift18 : Rat) : Real) = (((((13 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift18, activeL3RatLogLo_p37, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift18 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift18 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 18 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((13 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p13_shift18)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p13_shift18)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (13 : Int) 18)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (13 : Int) 18)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p14_shift18 :
    |centeredBSplineR 11
        (((((14 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (14 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (14 : Int) 18 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift18 : Rat := ((-110917912644224444368095671031447163900077587167636163644912681192989746990361065399021533672169 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift18 : Rat := ((-13864739080528055546011958878930895487509698395954520455614085149123718373795133174877691709021 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (14 : Int) activeL3RatWeightIndex18
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift18 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift18 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift18, activeL3RatLogHi_p37, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift18 : Rat) : Real) =
            ((((14 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift18 : Rat) : Real) = (((((14 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift18, activeL3RatLogLo_p37, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift18 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift18 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 18 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((14 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p14_shift18)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p14_shift18)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (14 : Int) 18)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (14 : Int) 18)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p15_shift18 :
    |centeredBSplineR 11
        (((((15 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (15 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (15 : Int) 18 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift18 : Rat := ((139082087355775555631904328968552836099922412832363836355087318807010253009638934600978466327831 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift18 : Rat := ((5795086973157314817996013707023034837496767201348493181461971616958760542068288941707436096993 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (15 : Int) activeL3RatWeightIndex18
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift18 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift18 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift18, activeL3RatLogHi_p37, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift18 : Rat) : Real) =
            ((((15 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift18 : Rat) : Real) = (((((15 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift18, activeL3RatLogLo_p37, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift18 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift18 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 18 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((15 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p15_shift18)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p15_shift18)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (15 : Int) 18)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (15 : Int) 18)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p16_shift18 :
    |centeredBSplineR 11
        (((((16 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (16 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (16 : Int) 18 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift18 : Rat := ((129694029118591851877301442989517612033307470944121278785029106269003417669879644866992822109277 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift18 : Rat := ((48635260919471944453988041121069104512490301604045479544385914850876281626204866825122308290979 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (16 : Int) activeL3RatWeightIndex18
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift18 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift18 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift18, activeL3RatLogHi_p37, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift18 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex18) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift18 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p37) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift18, activeL3RatLogLo_p37, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift18 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift18 primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift18 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 18 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((16 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p16_shift18)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p16_shift18)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 18)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 18)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx18
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex18) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 18| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 18 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p13_shift18
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p14_shift18
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p15_shift18
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p16_shift18
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex18.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
