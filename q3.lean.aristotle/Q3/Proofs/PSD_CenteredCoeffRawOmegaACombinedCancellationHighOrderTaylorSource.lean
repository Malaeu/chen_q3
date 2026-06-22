import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
High-order Taylor source bridge for the Step33A.1-A sub0 combined-cancellation
cell.

This file intentionally does not provide generated center-jet rows, order-16
rows, Horner range rows, or a final interval payload.  It specializes the
existing order-16 center-Taylor receiver to the whole combined expression on
`[0, 1/10]`, with center `1/20` and radius `1/20`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
Whole-expression degree-15 Taylor remainder receiver for the active
combined-cancellation cell.

A future generator must supply rational coefficient enclosures for the center
jets `0..15` and a proof-grade uniform bound on the 16th iterated derivative.
Lean then proves the full-cell remainder bound in the exact
`rawOmegaATaylorPolynomial` normalization.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_bound_of_centerJet15_order16
    (coeff coeffErrorAbs : Fin 16 -> Rat)
    (order16Abs remainderAbs : Rat)
    (hSmooth :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr)
    (hCoeffErrorNonneg :
      ∀ j : Fin 16, 0 <= (coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            ((1 / 20 : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (coeff j : Real)‖ <=
          (coeffErrorAbs j : Real))
    (hOrder16 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta‖ <=
          (order16Abs : Real))
    (hBudget :
      (∑ j : Fin 16,
          (coeffErrorAbs j : Real) * ((1 : Real) / 20) ^ j.1) +
          (order16Abs : Real) * ((1 : Real) / 20) ^ 16 /
            (Nat.factorial 16 : Real) <=
        (remainderAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta -
          rawOmegaATaylorPolynomial 15 (1 / 20 : Rat) coeff eta‖ <=
        (remainderAbs : Real) := by
  refine
    centerJetTaylor_error_bound_of_order16
      (f := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr)
      (a := (0 : Real)) (b := ((1 : Real) / 10))
      (radius := ((1 : Real) / 20)) (order16Abs := (order16Abs : Real))
      (remainderAbs := (remainderAbs : Real)) (center := (1 / 20 : Rat))
      coeff coeffErrorAbs ?_ hSmooth hCoeffErrorNonneg hCenterJet hOrder16 ?_
      hBudget
  · norm_num
  · intro eta hEta
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [hEta.1]
    · linarith [hEta.2]

/--
Alias with the "centerTaylor15" wording used in the active route notes.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerTaylor15_remainder_of_order16
    (coeff coeffErrorAbs : Fin 16 -> Rat)
    (order16Abs remainderAbs : Rat)
    (hSmooth :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr)
    (hCoeffErrorNonneg :
      ∀ j : Fin 16, 0 <= (coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            ((1 / 20 : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (coeff j : Real)‖ <=
          (coeffErrorAbs j : Real))
    (hOrder16 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta‖ <=
          (order16Abs : Real))
    (hBudget :
      (∑ j : Fin 16,
          (coeffErrorAbs j : Real) * ((1 : Real) / 20) ^ j.1) +
          (order16Abs : Real) * ((1 : Real) / 20) ^ 16 /
            (Nat.factorial 16 : Real) <=
        (remainderAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta -
          rawOmegaATaylorPolynomial 15 (1 / 20 : Rat) coeff eta‖ <=
        (remainderAbs : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_bound_of_centerJet15_order16
    coeff coeffErrorAbs order16Abs remainderAbs hSmooth hCoeffErrorNonneg
    hCenterJet hOrder16 hBudget

/--
Proof-bearing certificate shape for the active whole-expression degree-15
combined-cancellation Taylor source.

The fields are only rational data.  `Valid` below is the proof object:
generators may emit these values only together with center-jet, order-16, and
budget proofs in the exact normalization consumed by
`primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_bound_of_centerJet15_order16`.
-/
structure Step33Sub0CombinedCancellationHighOrderTaylorCert where
  coeff : Fin 16 -> Rat
  coeffErrorAbs : Fin 16 -> Rat
  order16Abs : Rat
  remainderAbs : Rat

namespace Step33Sub0CombinedCancellationHighOrderTaylorCert

def poly (data : Step33Sub0CombinedCancellationHighOrderTaylorCert)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 15 (1 / 20 : Rat) data.coeff eta

def toIntervalData
    (data : Step33Sub0CombinedCancellationHighOrderTaylorCert)
    (polyLower polyUpper : Rat) :
    Step33Sub0CombinedCancellationIntervalCert where
  cellL := 0
  cellU := (1 : Rat) / 10
  center := (1 : Rat) / 20
  degree := 15
  coeff := data.coeff
  remainderAbs := data.remainderAbs
  polyLower := polyLower
  polyUpper := polyUpper

structure Valid (data : Step33Sub0CombinedCancellationHighOrderTaylorCert) :
    Prop where
  smooth :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
  coeffErrorNonneg :
    ∀ j : Fin 16, 0 <= (data.coeffErrorAbs j : Real)
  remainderNonneg :
    0 <= (data.remainderAbs : Real)
  centerJet :
    ∀ j : Fin 16,
      ‖iteratedDeriv j.1
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
          ((1 / 20 : Rat) : Real) /
          (Nat.factorial j.1 : Real) -
        (data.coeff j : Real)‖ <=
        (data.coeffErrorAbs j : Real)
  order16 :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
          eta‖ <=
        (data.order16Abs : Real)
  remainderBudget :
    (∑ j : Fin 16,
        (data.coeffErrorAbs j : Real) * ((1 : Real) / 20) ^ j.1) +
        (data.order16Abs : Real) * ((1 : Real) / 20) ^ 16 /
          (Nat.factorial 16 : Real) <=
      (data.remainderAbs : Real)

namespace Valid

theorem remainder_bound
    {data : Step33Sub0CombinedCancellationHighOrderTaylorCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta -
          data.poly eta‖ <=
        (data.remainderAbs : Real) := by
  simpa [Step33Sub0CombinedCancellationHighOrderTaylorCert.poly] using
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_bound_of_centerJet15_order16
      data.coeff data.coeffErrorAbs data.order16Abs data.remainderAbs
      h.smooth h.coeffErrorNonneg h.centerJet h.order16 h.remainderBudget

theorem to_interval_valid
    {data : Step33Sub0CombinedCancellationHighOrderTaylorCert}
    (h : data.Valid)
    {polyLower polyUpper : Rat}
    {range :
      Step33Sub0CombinedCancellationHornerRangeCert
        (data.toIntervalData polyLower polyUpper)}
    (hRange : range.Valid)
    (hBudgetLower :
      (step33Sub0CombinedCancellationTargetLower : Real) <=
        (polyLower : Real) - (data.remainderAbs : Real))
    (hBudgetUpper :
      (polyUpper : Real) + (data.remainderAbs : Real) <=
        (step33Sub0CombinedCancellationTargetUpper : Real)) :
    (data.toIntervalData polyLower polyUpper).Valid := by
  refine
    Step33Sub0CombinedCancellationIntervalCert.Valid.of_horner_range
      (data := data.toIntervalData polyLower polyUpper)
      (range := range)
      ?_ ?_ ?_ ?_ hRange ?_ ?_
  · rfl
  · rfl
  · simpa [Step33Sub0CombinedCancellationHighOrderTaylorCert.toIntervalData] using
      h.remainderNonneg
  · intro eta hEta
    simpa [Step33Sub0CombinedCancellationHighOrderTaylorCert.toIntervalData,
      Step33Sub0CombinedCancellationIntervalCert.poly,
      Step33Sub0CombinedCancellationHighOrderTaylorCert.poly] using
      h.remainder_bound eta hEta
  · simpa [Step33Sub0CombinedCancellationHighOrderTaylorCert.toIntervalData] using
      hBudgetLower
  · simpa [Step33Sub0CombinedCancellationHighOrderTaylorCert.toIntervalData] using
      hBudgetUpper

theorem to_hCombined
    {data : Step33Sub0CombinedCancellationHighOrderTaylorCert}
    (h : data.Valid)
    {polyLower polyUpper : Rat}
    {range :
      Step33Sub0CombinedCancellationHornerRangeCert
        (data.toIntervalData polyLower polyUpper)}
    (hRange : range.Valid)
    (hBudgetLower :
      (step33Sub0CombinedCancellationTargetLower : Real) <=
        (polyLower : Real) - (data.remainderAbs : Real))
    (hBudgetUpper :
      (polyUpper : Real) + (data.remainderAbs : Real) <=
        (step33Sub0CombinedCancellationTargetUpper : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (h.to_interval_valid hRange hBudgetLower hBudgetUpper).to_hCombined

theorem to_fullTaylor_residual_deriv_interval
    {data : Step33Sub0CombinedCancellationHighOrderTaylorCert}
    (h : data.Valid)
    {polyLower polyUpper : Rat}
    {range :
      Step33Sub0CombinedCancellationHornerRangeCert
        (data.toIntervalData polyLower polyUpper)}
    (hRange : range.Valid)
    (hBudgetLower :
      (step33Sub0CombinedCancellationTargetLower : Real) <=
        (polyLower : Real) - (data.remainderAbs : Real))
    (hBudgetUpper :
      (polyUpper : Real) + (data.remainderAbs : Real) <=
        (step33Sub0CombinedCancellationTargetUpper : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (h.to_interval_valid hRange hBudgetLower hBudgetUpper).to_fullTaylor_residual_deriv_interval

end Valid
end Step33Sub0CombinedCancellationHighOrderTaylorCert

end Step33
end PSDpd
end Q3
