import Q3.Proofs.PSD_CenteredCoeffPrimeDeltaLiveRationalPayloadImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

/-!
Generated Step33A.1 option-B controlK9 split-`R` plus-side
declared-support hbox facts, index chunk 20: 20..20.
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


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift20 :
    |centeredBSplineR 9
        (((((-17 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-17 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-17 : Int) 20 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m17_shift20 : Rat := ((-488799884306437576527157486654152964440863815118444584808314735077140826127013561462408001916003 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m17_shift20 : Rat := ((-81466647384406262754526247775692160740143969186407430801385789179523471021168926910401333652667 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-17 : Int) activeL3RatWeightIndex20
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift20 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m17_shift20 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m17_shift20, activeL3RatLogLo_p43, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift20 : Rat) : Real) =
            ((((-17 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m17_shift20 : Rat) : Real) = (((((-17 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m17_shift20, activeL3RatLogHi_p43, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift20 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m17_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m17_shift20 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 20 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-17 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m17_shift20)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m17_shift20)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-17 : Int) 20)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-17 : Int) 20)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift20 :
    |centeredBSplineR 9
        (((((-16 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-16 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-16 : Int) 20 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m16_shift20 : Rat := ((-79599961435479192175719162218050988146954605039481528269438245025713608709004520487469333972001 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m16_shift20 : Rat := ((-119399942153218788263578743327076482220431907559222292404157367538570413063506780731204000958001 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-16 : Int) activeL3RatWeightIndex20
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift20 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m16_shift20 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m16_shift20, activeL3RatLogLo_p43, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift20 : Rat) : Real) =
            ((((-16 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m16_shift20 : Rat) : Real) = (((((-16 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m16_shift20, activeL3RatLogHi_p43, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift20 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m16_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m16_shift20 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 20 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-16 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m16_shift20)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m16_shift20)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-16 : Int) 20)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-16 : Int) 20)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift20 :
    |centeredBSplineR 9
        (((((-15 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-15 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-15 : Int) 20 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m15_shift20 : Rat := ((11200115693562423472842513345847035559136184881555415191685264922859173872986438537591998083997 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m15_shift20 : Rat := ((5600057846781211736421256672923517779568092440777707595842632461429586936493219268795999041999 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-15 : Int) activeL3RatWeightIndex20
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift20 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m15_shift20 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m15_shift20, activeL3RatLogLo_p43, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift20 : Rat) : Real) =
            ((((-15 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m15_shift20 : Rat) : Real) = (((((-15 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m15_shift20, activeL3RatLogHi_p43, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift20 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m15_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m15_shift20 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 20 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-15 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m15_shift20)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m15_shift20)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-15 : Int) 20)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-15 : Int) 20)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift20 :
    |centeredBSplineR 9
        (((((-14 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-14 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-14 : Int) 20 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m14_shift20 : Rat := ((261200115693562423472842513345847035559136184881555415191685264922859173872986438537591998083997 : Rat) / 300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m14_shift20 : Rat := ((43533352615593737245473752224307839259856030813592569198614210820476528978831073089598666347333 : Rat) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-14 : Int) activeL3RatWeightIndex20
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift20 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m14_shift20 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m14_shift20, activeL3RatLogLo_p43, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift20 : Rat) : Real) =
            ((((-14 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m14_shift20 : Rat) : Real) = (((((-14 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m14_shift20, activeL3RatLogHi_p43, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift20 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m14_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m14_shift20 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 20 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-14 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m14_shift20)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m14_shift20)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-14 : Int) 20)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-14 : Int) 20)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom


private theorem controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift20 :
    |centeredBSplineR 9
        (((((-13 : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell)) -
      controlK9RationalDeltaLiveRPlusMidByDelta (-13 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDelta (-13 : Int) 20 := by
  let controlK9RationalDeltaLiveRPlusLo_delta_m13_shift20 : Rat := ((170400038564520807824280837781949011853045394960518471730561754974286391290995479512530666027999 : Rat) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  let controlK9RationalDeltaLiveRPlusHi_delta_m13_shift20 : Rat := ((255600057846781211736421256672923517779568092440777707595842632461429586936493219268795999041999 : Rat) / 150000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
  have hb :=
    controlK9RationalDeltaLiveRPlus_arg_bounds
      (-13 : Int) activeL3RatWeightIndex20
  have hlo_eq :
          ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift20 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftLower
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusLo_delta_m13_shift20 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogLo_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusLo_delta_m13_shift20, activeL3RatLogLo_p43, controlK9Ell, controlK9EllRat]
  have hhi_eq :
          ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift20 : Rat) : Real) =
            ((((-13 : Int) : Real) / 4 +
              activeL3RationalPrimeShiftUpper
                activeL3RatWeightIndex20) / controlK9Ell) := by
    change ((controlK9RationalDeltaLiveRPlusHi_delta_m13_shift20 : Rat) : Real) = (((((-13 : Int) : Real) / 4 + ((1 : Nat) : Real) * activeL3RatLogHi_p43) / controlK9Ell))
    norm_num [controlK9RationalDeltaLiveRPlusHi_delta_m13_shift20, activeL3RatLogHi_p43, controlK9Ell, controlK9EllRat]
  have hdom :
      rationalDeltaLiveRatRRad 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift20 +
          |rationalDeltaLiveRatRMid 9 controlK9RationalDeltaLiveRPlusLo_delta_m13_shift20 controlK9RationalDeltaLiveRPlusHi_delta_m13_shift20 -
            controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 20| <=
        controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 20 := by
    native_decide
  simpa [controlK9RationalDeltaLiveRPlusMidByDelta,
    controlK9RationalDeltaLiveRPlusRadByDelta] using
    rationalDeltaLive_centeredBSplineR_hbox_of_rat_arg_bounds
      (k := 9)
      (x := ((((-13 : Int) : Real) / 4 +
        controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell))
      (lo := controlK9RationalDeltaLiveRPlusLo_delta_m13_shift20)
      (hi := controlK9RationalDeltaLiveRPlusHi_delta_m13_shift20)
      (mid := controlK9RationalDeltaLiveRPlusMidByDeltaRat (-13 : Int) 20)
      (rad := controlK9RationalDeltaLiveRPlusRadByDeltaRat (-13 : Int) 20)
      (by simpa [hlo_eq] using hb.1)
      (by simpa [hhi_eq] using hb.2)
      hdom

theorem controlK9RationalDeltaLiveRPlusHboxDeclared_idx20
    (δInt : Int)
    (hδ : (-22 : Int) ≤ δInt ∧ δInt ≤ (22 : Int))
    (hmem : activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta δInt) :
    |centeredBSplineR 9
      ((((δInt : Int) : Real) / 4 +
          controlK9PrimeShift activeL3RatWeightIndex20) / controlK9Ell) -
      controlK9RationalDeltaLiveRPlusMidByDelta δInt 20| <=
        controlK9RationalDeltaLiveRPlusRadByDelta δInt 20 := by
  have hlow : (-22 : Int) ≤ δInt := hδ.1
  have hhigh : δInt ≤ (22 : Int) := hδ.2
  interval_cases δInt
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-22 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-18 : Int)) (by simpa using hmem))
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m17_shift20
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m16_shift20
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m15_shift20
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m14_shift20
  · exact controlK9RationalDeltaLiveRPlusHbox_delta_m13_shift20
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (-1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (0 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (1 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (2 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (3 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (4 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (5 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (6 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (7 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (8 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (9 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (10 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (11 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (12 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (13 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (14 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (15 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (16 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (17 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (18 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (19 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (20 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (21 : Int)) (by simpa using hmem))
  · exact False.elim ((by native_decide :
        ¬ activeL3RatWeightIndex20.1 ∈ controlK9RationalDeltaLiveRPlusDeclaredNonzeroShiftSetByDelta
          (22 : Int)) (by simpa using hmem))

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
