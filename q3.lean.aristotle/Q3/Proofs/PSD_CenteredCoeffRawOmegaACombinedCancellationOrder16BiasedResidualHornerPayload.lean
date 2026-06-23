import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerCert
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Concrete payload target for the Step33A.1-A sub0 biased residual-Horner route.

The checked receiver in
`PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerCert`
already consumes a finite family of residual-Horner segments and transports it
to the biased nonzero-model direct interval receiver.  This file fixes the
canonical payload interface selected by the route review:

* the family must prove the same-unit residual target
  `ComponentSource - BiasedNonzeroModelPoly`;
* the global family residual budget must be exactly the canonical
  `BiasedResidualRemainderAbs`;
* once those rows are Lean-checked, the existing direct interval adapter is
  closed.

This file emits no segment rows and does not claim Step33A.1-A closure.  The
remaining proof-producing gap is

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- The canonical residual-Horner payload target.

A future generated payload should define concrete segment data and prove this
predicate.  The predicate is intentionally small: it asks for a checked valid
family and identifies its residual budget with the canonical direct-adapter
budget. -/
def primaryFiniteRow0Parent0Split100Sub0BiasedResidualHornerFamilyPayloadTarget
    (cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert) :
    Prop :=
  cert.Valid ∧
    cert.residualAbs =
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs

/-- Expose the residual source proposition in the exact canonical budget used
by the direct biased nonzero-model adapter. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerFamily_residualSourceProp_of_payload_target
    {cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert}
    (h :
      primaryFiniteRow0Parent0Split100Sub0BiasedResidualHornerFamilyPayloadTarget
        cert) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs := by
  rcases h with ⟨hValid, hResidualAbs⟩
  simpa [hResidualAbs] using hValid.to_residualSourceProp

/-- Main handoff for the concrete residual-Horner family payload route. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_biasedResidualHornerFamily_payload
    {cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert}
    (h :
      primaryFiniteRow0Parent0Split100Sub0BiasedResidualHornerFamilyPayloadTarget
        cert) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound
      (primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerFamily_residualSourceProp_of_payload_target
        h)

/-- Same handoff without forcing the canonical residual budget into the
payload target.  This is useful for generated families that first prove a
smaller residual budget and then supply the explicit same-unit comparison. -/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_biasedResidualHornerFamily_valid
    {cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert}
    (hValid : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid := by
  exact hValid.to_order16DirectIntervalValid

end Step33
end PSDpd
end Q3
