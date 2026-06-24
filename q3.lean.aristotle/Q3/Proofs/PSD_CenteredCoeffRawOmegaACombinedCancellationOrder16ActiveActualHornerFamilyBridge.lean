import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Family-level bridge for future active-actual order-16 Horner rows.

The segment receiver already transports one valid active-actual row into the
checked collapsed-expression normalization.  This file only packages such rows
as the existing direct Horner family receiver expects them: one segment family,
Horner range rows, interval/budget rows, and a segment cover.

It does not generate coefficients, prove range rows, prove budget rows, or claim
Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/--
One active-actual Horner segment with the direct receiver's interval and budget
fields attached.

The approximation row remains the active-actual row.  The direct fields are the
already-existing Horner receiver fields after the checked activeActual-to-
collapsed normalization has been applied.
-/
structure Step33Sub0ActiveActualOrder16HornerDirectSegmentCert where
  cellL : Rat
  cellU : Rat
  coeff : Fin 30 -> Rat
  polyErrorAbs : Rat
  polyLower : Rat
  polyUpper : Rat
  lower : Rat
  upper : Rat
  residualAbs : Rat

namespace Step33Sub0ActiveActualOrder16HornerDirectSegmentCert

/-- Forget direct interval fields and expose the active-actual row contract. -/
def toActiveActualSegment
    (data : Step33Sub0ActiveActualOrder16HornerDirectSegmentCert) :
    Step33Sub0ActiveActualOrder16HornerSegmentCert where
  cellL := data.cellL
  cellU := data.cellU
  coeff := data.coeff
  polyErrorAbs := data.polyErrorAbs

/--
Convert an active-actual row into the direct Horner segment shape by using the
checked collapsed coefficient stream.
-/
def toDirectHornerSegment
    (data : Step33Sub0ActiveActualOrder16HornerDirectSegmentCert) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert where
  cellL := data.cellL
  cellU := data.cellU
  center := (1 : Rat) / 20
  degree := 29
  coeff :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf
      data.coeff
  polyErrorAbs := data.polyErrorAbs
  polyLower := data.polyLower
  polyUpper := data.polyUpper
  lower := data.lower
  upper := data.upper
  residualAbs := data.residualAbs

end Step33Sub0ActiveActualOrder16HornerDirectSegmentCert

/-- Horner range rows for the converted direct segment. -/
structure Step33Sub0ActiveActualOrder16HornerDirectRangeCert
    (data : Step33Sub0ActiveActualOrder16HornerDirectSegmentCert) where
  stageLower :
    Fin (data.toDirectHornerSegment.degree + 1) -> Rat
  stageUpper :
    Fin (data.toDirectHornerSegment.degree + 1) -> Rat

namespace Step33Sub0ActiveActualOrder16HornerDirectRangeCert

/-- Expose the existing direct Horner range certificate shape. -/
def toDirectHornerRange
    {data : Step33Sub0ActiveActualOrder16HornerDirectSegmentCert}
    (range : Step33Sub0ActiveActualOrder16HornerDirectRangeCert data) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert
      data.toDirectHornerSegment where
  stageLower := range.stageLower
  stageUpper := range.stageUpper

end Step33Sub0ActiveActualOrder16HornerDirectRangeCert

/--
Generator-facing active-actual Horner family.

The family is still conditional: it supplies a shape for future proof-grade row
data, not the row data itself.
-/
structure Step33Sub0ActiveActualOrder16HornerFamilyCert where
  n : Nat
  residualAbs : Rat
  seg : Fin n -> Step33Sub0ActiveActualOrder16HornerDirectSegmentCert
  range :
    (i : Fin n) ->
      Step33Sub0ActiveActualOrder16HornerDirectRangeCert (seg i)

namespace Step33Sub0ActiveActualOrder16HornerFamilyCert

/-- Convert the active-actual family into the existing direct Horner family. -/
def toDirectHornerFamily
    (cert : Step33Sub0ActiveActualOrder16HornerFamilyCert) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert where
  n := cert.n
  residualAbs := cert.residualAbs
  seg := fun i => (cert.seg i).toDirectHornerSegment
  range := fun i => (cert.range i).toDirectHornerRange

/--
Validity predicate for the active-actual family bridge.

The hard analytic row is still the per-segment active-actual `Valid` proof.
The remaining fields are exactly the range, interval, budget, and cover rows
already required by the direct Horner receiver.
-/
structure Valid
    (cert : Step33Sub0ActiveActualOrder16HornerFamilyCert) :
    Prop where
  activeValid :
    ∀ i : Fin cert.n, (cert.seg i).toActiveActualSegment.Valid
  rangeValid :
    ∀ i : Fin cert.n, (cert.range i).toDirectHornerRange.Valid
  intervalLowerBudget :
    ∀ i : Fin cert.n,
      (((cert.seg i).toDirectHornerSegment).lower : Real) <=
        (((cert.seg i).toDirectHornerSegment).polyLower : Real) -
          (((cert.seg i).toDirectHornerSegment).polyErrorAbs : Real)
  intervalUpperBudget :
    ∀ i : Fin cert.n,
      (((cert.seg i).toDirectHornerSegment).polyUpper : Real) +
          (((cert.seg i).toDirectHornerSegment).polyErrorAbs : Real) <=
        (((cert.seg i).toDirectHornerSegment).upper : Real)
  segmentResidualNonneg :
    ∀ i : Fin cert.n,
      0 <= ((((cert.seg i).toDirectHornerSegment).residualAbs : Rat) : Real)
  segmentLowerBudget :
    ∀ i : Fin cert.n,
      -(((((cert.seg i).toDirectHornerSegment).residualAbs : Rat) : Real)) <=
        (((cert.seg i).toDirectHornerSegment).lower : Real)
  segmentUpperBudget :
    ∀ i : Fin cert.n,
      (((cert.seg i).toDirectHornerSegment).upper : Real) <=
        ((((cert.seg i).toDirectHornerSegment).residualAbs : Rat) : Real)
  segmentBudget :
    ∀ i : Fin cert.n,
      ((((cert.seg i).toDirectHornerSegment).residualAbs : Rat) : Real) <=
        (cert.residualAbs : Real)
  cover :
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover
      cert.n (fun i => (cert.seg i).toDirectHornerSegment)

namespace Valid

/--
The checked bridge theorem: a valid active-actual Horner family is a valid
direct Horner family in the existing Step33A.1-A receiver.
-/
theorem to_directHornerFamilyValid
    {cert : Step33Sub0ActiveActualOrder16HornerFamilyCert}
    (h : cert.Valid) :
    cert.toDirectHornerFamily.Valid := by
  refine
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert.valid_of_collapsed_horner_rows
        (cert := cert.toDirectHornerFamily)
        ?_
        ?_
        ?_
        ?_
        ?_
        ?_
        ?_
        ?_
        ?_
        ?_
        ?_
  · intro i eta hEta
    exact (h.activeValid i).cellSubset eta hEta
  · intro i
    exact (h.activeValid i).polyErrorNonneg
  · intro i eta hEta
    have hCollapsed :=
      (h.activeValid i).to_collapsed_segment_remainder eta hEta
    simpa [
      Step33Sub0ActiveActualOrder16HornerFamilyCert.toDirectHornerFamily,
      Step33Sub0ActiveActualOrder16HornerDirectSegmentCert.toActiveActualSegment,
      Step33Sub0ActiveActualOrder16HornerDirectSegmentCert.toDirectHornerSegment,
      Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.poly] using
      hCollapsed
  · intro i
    exact h.rangeValid i
  · intro i
    exact h.intervalLowerBudget i
  · intro i
    exact h.intervalUpperBudget i
  · intro i
    exact h.segmentResidualNonneg i
  · intro i
    exact h.segmentLowerBudget i
  · intro i
    exact h.segmentUpperBudget i
  · intro i
    exact h.segmentBudget i
  · exact h.cover

theorem to_directPayloadTarget
    {cert : Step33Sub0ActiveActualOrder16HornerFamilyCert}
    (h : cert.Valid)
    (hResidualAbs :
      cert.residualAbs =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget
      cert.toDirectHornerFamily.toDirectFamily := by
  exact h.to_directHornerFamilyValid.to_directPayloadTarget hResidualAbs

theorem to_nonzeroModelSourceProp
    {cert : Step33Sub0ActiveActualOrder16HornerFamilyCert}
    (h : cert.Valid)
    (hResidualAbs :
      cert.residualAbs =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :=
  h.to_directHornerFamilyValid.to_nonzeroModelSourceProp hResidualAbs

end Valid
end Step33Sub0ActiveActualOrder16HornerFamilyCert

/--
Named theorem for the activeActual-family to direct-family bridge.

This remains conditional on proof-grade activeActual rows plus range/budget
rows; it is not a closure theorem.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily
    {cert : Step33Sub0ActiveActualOrder16HornerFamilyCert}
    (h : cert.Valid) :
    cert.toDirectHornerFamily.Valid :=
  h.to_directHornerFamilyValid

/--
Named theorem exposing the existing direct payload target from activeActual
Horner family rows.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily
    {cert : Step33Sub0ActiveActualOrder16HornerFamilyCert}
    (h : cert.Valid)
    (hResidualAbs :
      cert.residualAbs =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget
      cert.toDirectHornerFamily.toDirectFamily :=
  h.to_directPayloadTarget hResidualAbs

/--
Named theorem exposing the existing nonzero-model source proposition from
activeActual Horner family rows.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_nonzeroModelSourceProp_of_activeActualHornerFamily
    {cert : Step33Sub0ActiveActualOrder16HornerFamilyCert}
    (h : cert.Valid)
    (hResidualAbs :
      cert.residualAbs =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :=
  h.to_nonzeroModelSourceProp hResidualAbs

end Step33
end PSDpd
end Q3
