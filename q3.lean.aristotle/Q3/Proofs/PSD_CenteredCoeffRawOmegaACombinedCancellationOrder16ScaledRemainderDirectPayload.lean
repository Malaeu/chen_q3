import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderZeroModelPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Direct nonzero-model interval payload surface for the Step33A.1-A sub0
scaled-remainder route.

The checked zero-model bridge already identifies the biased scaled remainder
with

`CombinedCancellationOrder16ComponentSource - CombinedOrder16NonzeroModelPoly`.

This file makes that direct normalization the generator-facing target.  It
does not emit interval rows and does not claim Step33A.1-A closure.  The open
proof-producing gap is

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- One interval segment for the direct signed nonzero-model residual
`ComponentSource - NonzeroModelPoly`. -/
structure Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert where
  cellL : Rat
  cellU : Rat
  lower : Rat
  upper : Rat
  remainderAbs : Rat

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert

/-- Proof-bearing validity predicate for one direct nonzero-model residual row. -/
structure Valid
    (cert : Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  directInterval :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.lower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta <=
          (cert.upper : Real)
  remainderNonneg : (0 : Real) <= (cert.remainderAbs : Real)
  lowerBudget :
    -(cert.remainderAbs : Real) <= (cert.lower : Real)
  upperBudget :
    (cert.upper : Real) <= (cert.remainderAbs : Real)

namespace Valid

/-- Convert a direct signed interval row into the absolute source-bound row
needed by the zero-model checker. -/
theorem to_nonzeroModelResidual_bound_on_segment
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
            eta‖ <=
        (cert.remainderAbs : Real) := by
  intro eta hEta
  have hInterval := h.directInterval eta hEta
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact h.lowerBudget.trans hInterval.1
  · exact hInterval.2.trans h.upperBudget

end Valid
end Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert

/-- A finite family of direct nonzero-model residual rows covers `[0, 1/10]`. -/
def Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover
    (n : Nat)
    (seg : Fin n ->
      Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert) :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ∃ i : Fin n,
      eta ∈ Set.Icc ((seg i).cellL : Real) ((seg i).cellU : Real)

/-- Family data shape for future generated direct nonzero-model residual rows. -/
structure Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert where
  n : Nat
  residualAbs : Rat
  seg : Fin n ->
    Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert

/-- Proof-bearing validity predicate for a full direct interval family. -/
structure Valid
    (cert : Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert) :
    Prop where
  segmentValid :
    ∀ i : Fin cert.n, (cert.seg i).Valid
  segmentBudget :
    ∀ i : Fin cert.n,
      (((cert.seg i).remainderAbs : Rat) : Real) <=
        (cert.residualAbs : Real)
  cover :
    Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover cert.n cert.seg

namespace Valid

/-- Expose a valid direct interval family as the exact nonzero-model source
proposition consumed by the already checked zero-model payload. -/
theorem to_nonzeroModelSourceProp
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      cert.residualAbs := by
  intro eta hEta
  rcases h.cover eta hEta with ⟨i, hEtaSeg⟩
  exact
    le_trans
      ((h.segmentValid i).to_nonzeroModelResidual_bound_on_segment eta hEtaSeg)
      (h.segmentBudget i)

end Valid
end Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert

/-- Canonical payload target for future generated direct nonzero-model rows. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget
    (cert : Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert) :
    Prop :=
  cert.Valid ∧
    cert.residualAbs =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs

/-- A direct payload target supplies the exact source proposition needed by the
zero-model route in the canonical residual budget. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert}
    (h :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget
        cert) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs := by
  rcases h with ⟨hValid, hResidualAbs⟩
  simpa [hResidualAbs] using hValid.to_nonzeroModelSourceProp

/-- A direct payload target closes the already checked zero-model interval
payload target. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert}
    (h :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget
        cert) :
    primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget
      primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily :=
  primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual
    (primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload
      h)

/-- A direct signed interval on the full cell is the single-row theorem shape
requested by the route review.  The future generator should prove the premise,
not this adapter. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval
    (hInterval :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        -(primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
            Real) <=
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
                eta -
              primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
                eta ∧
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
                eta -
              primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
                eta <=
            (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
              Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs := by
  intro eta hEta
  have hBounds := hInterval eta hEta
  rw [Real.norm_eq_abs, abs_le]
  exact hBounds

end Step33
end PSDpd
end Q3
