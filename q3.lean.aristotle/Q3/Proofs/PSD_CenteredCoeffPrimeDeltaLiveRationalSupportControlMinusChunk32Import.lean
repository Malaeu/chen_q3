import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` minus-side
declared-support hbox facts, index chunk 32: 32..32.
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


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift32 :
    |centeredBSplineR 9
        (((((16 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (16 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (16 : Int) 32 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p16_shift32 : Rat := ((-69806767966099653912578703881895075504885509443872728364657243823096498314831767639737882828429 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p16_shift32 : Rat := ((-418840607796597923475472223291370453029313056663236370187943462938578989888990605838427296970573 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (16 : Int) activeL3RatWeightIndex32
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift32 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p16_shift32 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p16_shift32, activeL3RatLogHi_p83, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift32 : Rat) : Real) =
            ((((16 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p16_shift32 : Rat) : Real) = (((((16 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p16_shift32, activeL3RatLogLo_p83, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift32 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p16_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p16_shift32 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 32 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((16 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p16_shift32)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p16_shift32)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (16 : Int) 32)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (16 : Int) 32)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p17_shift32 :
    |centeredBSplineR 9
        (((((17 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (17 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (17 : Int) 32 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p17_shift32 : Rat := ((-84420303898298961737736111645685226514656528331618185093971731469289494944495302919213648485287 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p17_shift32 : Rat := ((-168840607796597923475472223291370453029313056663236370187943462938578989888990605838427296970573 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (17 : Int) activeL3RatWeightIndex32
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p17_shift32 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p17_shift32 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p17_shift32, activeL3RatLogHi_p83, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p17_shift32 : Rat) : Real) =
            ((((17 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p17_shift32 : Rat) : Real) = (((((17 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p17_shift32, activeL3RatLogLo_p83, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p17_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p17_shift32 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p17_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p17_shift32 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 32 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((17 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p17_shift32)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p17_shift32)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (17 : Int) 32)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (17 : Int) 32)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift32 :
    |centeredBSplineR 9
        (((((18 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (18 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (18 : Int) 32 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p18_shift32 : Rat := ((40579696101701038262263888354314773485343471668381814906028268530710505055504697080786351514713 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p18_shift32 : Rat := ((27053130734467358841509258902876515656895647778921209937352179020473670037003131387190901009809 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (18 : Int) activeL3RatWeightIndex32
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift32 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p18_shift32 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p18_shift32, activeL3RatLogHi_p83, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift32 : Rat) : Real) =
            ((((18 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p18_shift32 : Rat) : Real) = (((((18 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p18_shift32, activeL3RatLogLo_p83, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift32 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p18_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p18_shift32 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 32 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((18 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p18_shift32)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p18_shift32)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (18 : Int) 32)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (18 : Int) 32)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift32 :
    |centeredBSplineR 9
        (((((19 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (19 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (19 : Int) 32 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p19_shift32 : Rat := ((55193232033900346087421296118104924495114490556127271635342756176903501685168232360262117171571 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p19_shift32 : Rat := ((331159392203402076524527776708629546970686943336763629812056537061421010111009394161572703029427 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (19 : Int) activeL3RatWeightIndex32
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift32 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p19_shift32 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p19_shift32, activeL3RatLogHi_p83, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift32 : Rat) : Real) =
            ((((19 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p19_shift32 : Rat) : Real) = (((((19 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p19_shift32, activeL3RatLogLo_p83, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift32 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p19_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p19_shift32 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 32 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((19 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p19_shift32)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p19_shift32)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (19 : Int) 32)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (19 : Int) 32)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift32 :
    |centeredBSplineR 9
        (((((20 : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell)) -
      controlK9RationalDeltaLiveRMinusMidByDelta (20 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDelta (20 : Int) 32 := by
  let controlK9RationalDeltaLiveRMinusLo_delta_p20_shift32 : Rat := ((290579696101701038262263888354314773485343471668381814906028268530710505055504697080786351514713 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRMinusHi_delta_p20_shift32 : Rat := ((581159392203402076524527776708629546970686943336763629812056537061421010111009394161572703029427 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRMinus_arg_bounds
      (20 : Int) activeL3RatWeightIndex32
  have hlo_eq :
          ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift32 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusLo_delta_p20_shift32 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogHi_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusLo_delta_p20_shift32, activeL3RatLogHi_p83, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift32 : Rat) : Real) =
            ((((20 : Int) : Real) / 4 -
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex32) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRMinusHi_delta_p20_shift32 : Rat) : Real) = (((((20 : Int) : Real) / 4 - ((1 : Nat) : Real) * activeL3RatLogLo_p83) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRMinusHi_delta_p20_shift32, activeL3RatLogLo_p83, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift32 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRMinusLo_delta_p20_shift32 controlK9RationalDeltaLiveRMinusHi_delta_p20_shift32 -
            controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 32| <=
        controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 32 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRMinusMidByDelta,
    controlK9RationalDeltaLiveRMinusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((20 : Int) : Real) / 4 -
        controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRMinusLo_delta_p20_shift32)
      (hi := controlK9RationalDeltaLiveRMinusHi_delta_p20_shift32)
      (mid := controlK9RationalDeltaLiveRMinusMidByDeltaRat (20 : Int) 32)
      (rad := controlK9RationalDeltaLiveRMinusRadByDeltaRat (20 : Int) 32)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRMinusHboxDeclared_idx32
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 -
          controlK9PrimeShift activeL3RatWeightIndex32) / controlK9Ell) -
      controlK9RationalDeltaLiveRMinusMidByDelta δInt 32| <=
        controlK9RationalDeltaLiveRMinusRadByDelta δInt 32 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p16_shift32
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p17_shift32
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p18_shift32
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p19_shift32
  · exact controlK9RationalDeltaLiveRMinusHbox_delta_p20_shift32
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex32.1 ∈ controlK9RationalDeltaLiveRMinusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
