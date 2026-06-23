import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerRemainderBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Whole-expression interval payload surface for the Step33A.1-A sub0 biased
residual-Horner scaled remainder.

This file intentionally targets the complete signed scaled remainder

`ActiveScaleCoeff * D^16(ComponentProductCancellationResidual)
 + (ActiveScaleCoeff - NominalScaleCoeff) * D^16(ComponentProductNominal)`.

It does not split the two summands and does not provide numerical rows.  It
only records the proof-bearing interval certificate shape and the handoff into
`BiasedResidualHornerScaledRemainderSourceProp`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/--
One interval segment for the complete signed biased scaled remainder.

`lower` and `upper` must bound the whole expression on the same segment.
`remainderAbs` is the segment budget later spent as an absolute bound.
-/
structure Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert where
  cellL : Rat
  cellU : Rat
  lower : Rat
  upper : Rat
  remainderAbs : Rat

namespace Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert

/-- Proof-bearing validity predicate for one whole-expression interval row. -/
structure Valid
    (cert :
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  scaledInterval :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.lower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
            eta <=
          (cert.upper : Real)
  remainderNonneg : (0 : Real) <= (cert.remainderAbs : Real)
  lowerBudget :
    -(cert.remainderAbs : Real) <= (cert.lower : Real)
  upperBudget :
    (cert.upper : Real) <= (cert.remainderAbs : Real)

namespace Valid

theorem to_scaledRemainder_bound_on_segment
    {cert :
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
          eta‖ <=
        (cert.remainderAbs : Real) := by
  intro eta hEta
  have hInterval := h.scaledInterval eta hEta
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact h.lowerBudget.trans hInterval.1
  · exact hInterval.2.trans h.upperBudget

end Valid
end Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert

/-- A finite family of whole-expression interval rows covers `[0, 1/10]`. -/
def Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCover
    (n : Nat)
    (seg : Fin n ->
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert) :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ∃ i : Fin n,
      eta ∈ Set.Icc ((seg i).cellL : Real) ((seg i).cellU : Real)

structure Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert where
  n : Nat
  residualAbs : Rat
  seg : Fin n ->
    Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert

namespace Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert

/-- Proof-bearing validity predicate for a full-cell interval family. -/
structure Valid
    (cert :
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert) :
    Prop where
  segmentValid :
    ∀ i : Fin cert.n, (cert.seg i).Valid
  segmentBudget :
    ∀ i : Fin cert.n,
      (((cert.seg i).remainderAbs : Rat) : Real) <=
        (cert.residualAbs : Real)
  cover :
    Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCover
      cert.n cert.seg

namespace Valid

theorem to_scaledRemainderSourceProp
    {cert :
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
      cert.residualAbs := by
  intro eta hEta
  rcases h.cover eta hEta with ⟨i, hEtaSeg⟩
  exact
    le_trans
      ((h.segmentValid i).to_scaledRemainder_bound_on_segment eta hEtaSeg)
      (h.segmentBudget i)

end Valid
end Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert

/--
Canonical payload target for the next generated certificate.

The equality pins the interval-family budget to the canonical biased residual
budget already consumed by the residual-Horner route.
-/
def primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget
    (cert :
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert) :
    Prop :=
  cert.Valid ∧
    cert.residualAbs =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs

theorem primaryFiniteRow0Parent0Split100Sub0_scaledRemainderSourceProp_of_interval_payload_target
    {cert :
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert}
    (h :
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget
        cert) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs := by
  rcases h with ⟨hValid, hResidualAbs⟩
  simpa [hResidualAbs] using hValid.to_scaledRemainderSourceProp

theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_interval_payload
    {cert :
      Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert}
    (h :
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget
        cert) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta -
          rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff
            eta‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) :=
  primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound
    (primaryFiniteRow0Parent0Split100Sub0_scaledRemainderSourceProp_of_interval_payload_target
      h)

end Step33
end PSDpd
end Q3
