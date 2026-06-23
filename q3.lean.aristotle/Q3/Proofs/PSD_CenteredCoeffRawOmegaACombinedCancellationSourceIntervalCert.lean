import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-bearing source-interval certificate target for the Step33A.1-A sub0
combined-cancellation high-order payload.

This file intentionally does not emit generated rows.  It packages the exact
component-source lower/upper row obligations that a future generator must prove,
then routes a valid source-interval certificate through the already checked
`Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid` constructor and final
combined interval receivers.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
Generator-facing source-interval certificate data for the active
combined-cancellation high-order Taylor bridge.

The fields are rational data only.  `Valid` below is the proof object: it must
justify lower/upper rows for the checked component-source center jets and the
checked component-source order-16 expression.
-/
structure Step33Sub0CombinedCancellationSourceIntervalCert where
  highOrderData : Step33Sub0CombinedCancellationHighOrderTaylorCert
  coeffLower : Fin 16 -> Rat
  coeffUpper : Fin 16 -> Rat
  order16Lower : Rat
  order16Upper : Rat

namespace Step33Sub0CombinedCancellationSourceIntervalCert

abbrev data (cert : Step33Sub0CombinedCancellationSourceIntervalCert) :
    Step33Sub0CombinedCancellationHighOrderTaylorCert :=
  cert.highOrderData

/--
Proof-bearing validity predicate for source-interval rows.

`sourceCenterInterval` and `order16SourceInterval` are the real analytic row
obligations.  The remaining fields are exact rational budget bookkeeping that
connects those rows to `cert.highOrderData`.
-/
structure Valid (cert : Step33Sub0CombinedCancellationSourceIntervalCert) :
    Prop where
  coeffErrorNonneg :
    ∀ j : Fin 16, 0 <= (cert.data.coeffErrorAbs j : Real)
  remainderNonneg :
    0 <= (cert.data.remainderAbs : Real)
  sourceCenterInterval :
    ∀ j : Fin 16,
      (cert.coeffLower j : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
            j.1 ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
            j.1 <=
          (cert.coeffUpper j : Real)
  coeffErrorBudget :
    ∀ j : Fin 16,
      (cert.data.coeff j : Real) - (cert.data.coeffErrorAbs j : Real) <=
          (cert.coeffLower j : Real) ∧
        (cert.coeffUpper j : Real) <=
          (cert.data.coeff j : Real) + (cert.data.coeffErrorAbs j : Real)
  order16SourceInterval :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (cert.order16Lower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          (cert.order16Upper : Real)
  order16Budget :
    -(cert.data.order16Abs : Real) <= (cert.order16Lower : Real) ∧
      (cert.order16Upper : Real) <= (cert.data.order16Abs : Real)
  remainderBudget :
    (∑ j : Fin 16,
        (cert.data.coeffErrorAbs j : Real) * ((1 : Real) / 20) ^ j.1) +
        (cert.data.order16Abs : Real) * ((1 : Real) / 20) ^ 16 /
          (Nat.factorial 16 : Real) <=
      (cert.data.remainderAbs : Real)

namespace Valid

/-- Route a valid source-interval certificate into the high-order Taylor
payload validity predicate. -/
theorem to_highOrderValid
    {cert : Step33Sub0CombinedCancellationSourceIntervalCert}
    (h : cert.Valid) :
    cert.data.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_interval
    cert.data cert.coeffLower cert.coeffUpper cert.order16Lower
    cert.order16Upper h.coeffErrorNonneg h.remainderNonneg
    h.sourceCenterInterval h.coeffErrorBudget h.order16SourceInterval
    h.order16Budget h.remainderBudget

/--
Route a valid source-interval certificate plus Horner and target-budget rows to
the active whole-cell combined-cancellation interval.
-/
theorem to_hCombined
    {cert : Step33Sub0CombinedCancellationSourceIntervalCert}
    (h : cert.Valid)
    {polyLower polyUpper : Rat}
    {range :
      Step33Sub0CombinedCancellationHornerRangeCert
        (cert.data.toIntervalData polyLower polyUpper)}
    (hRange : range.Valid)
    (hBudgetLower :
      (step33Sub0CombinedCancellationTargetLower : Real) <=
        (polyLower : Real) - (cert.data.remainderAbs : Real))
    (hBudgetUpper :
      (polyUpper : Real) + (cert.data.remainderAbs : Real) <=
        (step33Sub0CombinedCancellationTargetUpper : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (h.to_highOrderValid).to_hCombined hRange hBudgetLower hBudgetUpper

/--
Same as `to_hCombined`, stated at the downstream residual-derivative interval
surface consumed by the landing proof.
-/
theorem to_fullTaylor_residual_deriv_interval
    {cert : Step33Sub0CombinedCancellationSourceIntervalCert}
    (h : cert.Valid)
    {polyLower polyUpper : Rat}
    {range :
      Step33Sub0CombinedCancellationHornerRangeCert
        (cert.data.toIntervalData polyLower polyUpper)}
    (hRange : range.Valid)
    (hBudgetLower :
      (step33Sub0CombinedCancellationTargetLower : Real) <=
        (polyLower : Real) - (cert.data.remainderAbs : Real))
    (hBudgetUpper :
      (polyUpper : Real) + (cert.data.remainderAbs : Real) <=
        (step33Sub0CombinedCancellationTargetUpper : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (h.to_highOrderValid).to_fullTaylor_residual_deriv_interval hRange
    hBudgetLower hBudgetUpper

end Valid
end Step33Sub0CombinedCancellationSourceIntervalCert

end Step33
end PSDpd
end Q3
