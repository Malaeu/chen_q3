import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B primaryK11 split-`R` minus-side
declared-support hbox facts, index chunk 46: 46..46.
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


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p18_shift46 :
    |centeredBSplineR 11
        (((((18 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (18 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (18 : Int) 46 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift46 : Rat := ((-144824644376897252396261639625181260814198886785051305224692834947751621840028373675660687102737 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift46 : Rat := ((-43447393313069175718878491887554378244259666035515391567407850484325486552008512102698206130821 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift46 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift46 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift46, activeL3RatLogHi_p139, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift46 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift46 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift46, activeL3RatLogLo_p139, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift46 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift46 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 46 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((18 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p18_shift46)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p18_shift46)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 46)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift46 :
    |centeredBSplineR 11
        (((((19 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (19 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (19 : Int) 46 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift46 : Rat := ((-184473933130691757188784918875543782442596660355153915674078504843254865520085121026982061308211 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift46 : Rat := ((-18447393313069175718878491887554378244259666035515391567407850484325486552008512102698206130821 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift46 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift46 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift46, activeL3RatLogHi_p139, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift46 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift46 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift46, activeL3RatLogLo_p139, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift46 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift46 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 46 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((19 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p19_shift46)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p19_shift46)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 46)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift46 :
    |centeredBSplineR 11
        (((((20 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (20 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (20 : Int) 46 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift46 : Rat := ((65526066869308242811215081124456217557403339644846084325921495156745134479914878973017938691789 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift46 : Rat := ((2184202228976941427040502704148540585246777988161536144197383171891504482663829299100597956393 : Rat) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift46 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift46 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift46, activeL3RatLogHi_p139, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift46 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift46 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift46, activeL3RatLogLo_p139, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift46 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift46 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 46 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((20 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p20_shift46)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p20_shift46)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 46)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift46 :
    |centeredBSplineR 11
        (((((21 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (21 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (21 : Int) 46 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift46 : Rat := ((105175355623102747603738360374818739185801113214948694775307165052248378159971626324339312897263 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift46 : Rat := ((31552606686930824281121508112445621755740333964484608432592149515674513447991487897301793869179 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (21 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift46 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift46 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift46, activeL3RatLogHi_p139, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift46 : Rat) : Real) =
            ((((21 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift46 : Rat) : Real) = (((((21 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift46, activeL3RatLogLo_p139, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift46 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift46 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 46 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((21 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p21_shift46)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p21_shift46)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (21 : Int) 46)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (21 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem primaryK11RationalDeltaLiveRMinusHbox_delta_p22_shift46 :
    |centeredBSplineR 11
        (((((22 : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell)) -
      primaryK11RationalDeltaLiveRMinusMidByDelta (22 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta (22 : Int) 46 := by
  let primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift46 : Rat := ((565526066869308242811215081124456217557403339644846084325921495156745134479914878973017938691789 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift46 : Rat := ((56552606686930824281121508112445621755740333964484608432592149515674513447991487897301793869179 : Rat) / 30000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    primaryK11RationalDeltaLiveRMinus_arg_bounds
      (22 : Int) activeL3RatWeightIndex46
  have hlo_eq :
          ((primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift46 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift46 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift46, activeL3RatLogHi_p139, primaryK11Ell, primaryK11EllRat]
  have hhi_eq :
          ((primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift46 : Rat) : Real) =
            ((((22 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex46) / primaryK11Ell) := by
    change ((primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift46 : Rat) : Real) = (((((22 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p139) / primaryK11Ell))
    norm_num [primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift46, activeL3RatLogLo_p139, primaryK11Ell, primaryK11EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 11 primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift46 +
          |rationalDeltaLiveRatRMid 11 primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift46 primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift46 -
            primaryK11RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 46 := by
    native_decide
  simpa [primaryK11RationalDeltaLiveRMinusMidByDelta,
    primaryK11RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 11)
      (x := ((((22 : Int) : Real) / 4 -
        primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell))
      (lo := primaryK11RationalDeltaLiveRMinusLo_delta_p22_shift46)
      (hi := primaryK11RationalDeltaLiveRMinusHi_delta_p22_shift46)
      (mid := primaryK11RationalDeltaLiveRMinusMidByDeltaRat (22 : Int) 46)
      (rad := primaryK11RationalDeltaLiveRMinusRadByDeltaRat (22 : Int) 46)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem primaryK11RationalDeltaLiveRMinusHboxDeclared_idx46
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 11
      ((((δInt : Int) : Real) / 4 -
          primaryK11PrimeShift activeL3RatWeightIndex46) / primaryK11Ell) -
      primaryK11RationalDeltaLiveRMinusMidByDelta δInt 46| <=
        primaryK11RationalDeltaLiveRMinusRadByDelta δInt 46 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex46.1 ∈ primaryK11RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p18_shift46
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p19_shift46
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p20_shift46
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p21_shift46
  · exact primaryK11RationalDeltaLiveRMinusHbox_delta_p22_shift46

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
