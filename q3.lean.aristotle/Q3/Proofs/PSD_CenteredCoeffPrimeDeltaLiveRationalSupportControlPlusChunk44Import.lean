import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 44: 44..44.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift44 :
    |centeredBSplineR 9
        (((((-21 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-21 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-21 : Int) 44 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m21_shift44 : Rat := ((-4997369023984646078007679851072988091894533271458920373906727265232848798178540747369156523147 : Rat) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m21_shift44 : Rat := ((-46850334599856056981321998603809263361511249419927378505375568111557957482923819506585842404503 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-21 : Int) activeL3RatWeightIndex44
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift44 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m21_shift44 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m21_shift44, activeL3RatLogLo_p131, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift44 : Rat) : Real) =
            ((((-21 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m21_shift44 : Rat) : Real) = (((((-21 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m21_shift44, activeL3RatLogHi_p131, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift44 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m21_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m21_shift44 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 44 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-21 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m21_shift44)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m21_shift44)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-21 : Int) 44)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-21 : Int) 44)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift44 :
    |centeredBSplineR 9
        (((((-20 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-20 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-20 : Int) 44 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m20_shift44 : Rat := ((-4992107071953938234023039553218964275683599814376761121720181795698546394535622242107469569441 : Rat) / 12000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m20_shift44 : Rat := ((-15600334599856056981321998603809263361511249419927378505375568111557957482923819506585842404503 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-20 : Int) activeL3RatWeightIndex44
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift44 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m20_shift44 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m20_shift44, activeL3RatLogLo_p131, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift44 : Rat) : Real) =
            ((((-20 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m20_shift44 : Rat) : Real) = (((((-20 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m20_shift44, activeL3RatLogHi_p131, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift44 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m20_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m20_shift44 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 44 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-20 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m20_shift44)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m20_shift44)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-20 : Int) 44)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-20 : Int) 44)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift44 :
    |centeredBSplineR 9
        (((((-19 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-19 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-19 : Int) 44 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m19_shift44 : Rat := ((5007892928046061765976960446781035724316400185623238878279818204301453605464377757892530430559 : Rat) / 12000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m19_shift44 : Rat := ((5216555133381314339559333798730245546162916860024207164874810629480680839025393497804719198499 : Rat) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-19 : Int) activeL3RatWeightIndex44
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift44 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m19_shift44 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m19_shift44, activeL3RatLogLo_p131, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift44 : Rat) : Real) =
            ((((-19 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m19_shift44 : Rat) : Real) = (((((-19 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m19_shift44, activeL3RatLogHi_p131, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift44 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m19_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m19_shift44 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 44 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-19 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m19_shift44)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m19_shift44)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-19 : Int) 44)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-19 : Int) 44)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift44 :
    |centeredBSplineR 9
        (((((-18 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-18 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-18 : Int) 44 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m18_shift44 : Rat := ((5002630976015353921992320148927011908105466728541079626093272734767151201821459252630843476853 : Rat) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m18_shift44 : Rat := ((46899665400143943018678001396190736638488750580072621494624431888442042517076180493414157595497 : Rat) / 37500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-18 : Int) activeL3RatWeightIndex44
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift44 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m18_shift44 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m18_shift44, activeL3RatLogLo_p131, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift44 : Rat) : Real) =
            ((((-18 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex44) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m18_shift44 : Rat) : Real) = (((((-18 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p131) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m18_shift44, activeL3RatLogHi_p131, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift44 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m18_shift44 controlK9RationalDeltaLiveRPlusHi_delta_m18_shift44 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 44| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 44 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-18 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m18_shift44)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m18_shift44)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-18 : Int) 44)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-18 : Int) 44)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx44
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex44) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 44| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 44 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m21_shift44
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m20_shift44
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m19_shift44
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m18_shift44
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex44.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
