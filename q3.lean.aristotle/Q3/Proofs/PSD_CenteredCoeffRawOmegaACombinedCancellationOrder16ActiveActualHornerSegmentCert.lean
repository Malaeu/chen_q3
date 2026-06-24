import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRemainderBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof surface for future active-actual order-16 Horner segment rows.

This file defines the exact contract a generator must satisfy before the
active-actual row can feed the checked collapsed-expression adapter.  It does
not generate coefficients, prove interval rows, or claim Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/--
One future proof-bearing Horner row for the scaled active-actual order-16
derivative on a segment.

The coefficient row uses the same degree-29, center-`1/20` Taylor convention as
the active-actual/nominal adapter.  `polyErrorAbs` bounds the analytic
approximation error; it is not a budget row by itself.
-/
structure Step33Sub0ActiveActualOrder16HornerSegmentCert where
  cellL : Rat
  cellU : Rat
  coeff : Fin 30 -> Rat
  polyErrorAbs : Rat

namespace Step33Sub0ActiveActualOrder16HornerSegmentCert

/-- The active-actual polynomial carried by a future row certificate. -/
def poly
    (data : Step33Sub0ActiveActualOrder16HornerSegmentCert)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20) data.coeff eta

/--
Proof-bearing validity predicate for one active-actual Horner segment row.

The hard field is `remainderBound`; all concrete coefficients and interval or
rational proof data still have to be supplied by a generator or a formal source.
-/
structure Valid
    (data : Step33Sub0ActiveActualOrder16HornerSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  polyErrorNonneg : 0 <= (data.polyErrorAbs : Real)
  remainderBound :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          data.poly eta‖ <=
        (data.polyErrorAbs : Real)

namespace Valid

/--
Expose the active-actual segment remainder estimate in the exact normalization
needed by the checked activeActual-to-collapsed adapter.
-/
theorem to_activeActual_order16_segment_remainder
    {data : Step33Sub0ActiveActualOrder16HornerSegmentCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20) data.coeff eta‖ <=
        (data.polyErrorAbs : Real) := by
  intro eta hEta
  simpa [Step33Sub0ActiveActualOrder16HornerSegmentCert.poly] using
    h.remainderBound eta hEta

/--
Transport a valid active-actual Horner row into the collapsed-expression
remainder row consumed by the direct Step33A.1-A Horner receiver.
-/
theorem to_collapsed_segment_remainder
    {data : Step33Sub0ActiveActualOrder16HornerSegmentCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf
              data.coeff) eta‖ <=
        (data.polyErrorAbs : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActual
    data.coeff h.to_activeActual_order16_segment_remainder

end Valid
end Step33Sub0ActiveActualOrder16HornerSegmentCert

/--
Named receiver theorem for the live active-actual segment remainder source.

This is intentionally conditional on a `Valid` Horner segment certificate; it
does not assert that concrete active-actual rows already exist.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert
    {data : Step33Sub0ActiveActualOrder16HornerSegmentCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20) data.coeff eta‖ <=
        (data.polyErrorAbs : Real) :=
  h.to_activeActual_order16_segment_remainder

/--
Smoke theorem: a valid active-actual Horner segment certificate reaches the
checked collapsed-expression remainder normalization.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner
    {data : Step33Sub0ActiveActualOrder16HornerSegmentCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf
              data.coeff) eta‖ <=
        (data.polyErrorAbs : Real) :=
  h.to_collapsed_segment_remainder

end Step33
end PSDpd
end Q3
