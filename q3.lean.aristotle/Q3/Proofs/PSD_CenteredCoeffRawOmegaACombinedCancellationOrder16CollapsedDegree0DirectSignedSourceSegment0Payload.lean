import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0LocalFactorTaylorModelPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Segment0 direct signed-source payload for the collapsed degree-0 Step33A.1-A
gate.

This file exposes the generator-facing interval theorem name for segment0 from
the checked local-factor Taylor18 payload.  It does not prove the full segment
cover, the derivative absolute budget, the degree-0 budget, or Step33A.1-A.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- First generated direct signed-source segment row.

The interval is for the already-subtracted source
`ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)` on
the segment0 cell `[0, 1/20]`.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated :
    ∀ eta ∈ Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.toSignedSegmentCert.cellL :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.toSignedSegmentCert.cellU :
          Real),
      (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.toSignedSegmentCert.lower :
          Real) <=
          primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
            eta <=
          (primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.toSignedSegmentCert.upper :
            Real) :=
  primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_of_localFactorTaylor18_payload.sourceInterval

/-- The same row packaged as the checked segment certificate receiver. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_valid_generated :
    primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.toSignedSegmentCert.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_of_localFactorTaylor18_payload

end Step33
end PSDpd
end Q3
