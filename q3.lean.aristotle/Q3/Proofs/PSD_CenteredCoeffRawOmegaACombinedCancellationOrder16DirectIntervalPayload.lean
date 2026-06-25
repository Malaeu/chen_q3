import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Direct order-16 interval target for the Step33A.1-A sub0 combined-cancellation
source.

Browser/Computer Use route review selected this route after the exact segmented
budget audit showed that naive centered-Taylor splitting would need radius
`1/2560`, i.e. 128 equal subsegments on `[0, 1/10]`.

This file is intentionally only a checked interface.  It does not emit rational
`lower`/`upper` rows and does not claim `Step33Sub0CombinedCancellationSourceIntervalCert.Valid`.
The remaining proof-producing gap is:

`STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_INTERVAL_CERT_GAP`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- Proof-producing target for the direct whole-expression order-16 source
interval.  A future certificate must supply concrete rational `lower` and
`upper` and prove this proposition without splitting the two product summands
into independent norm bounds. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget
    (lower upper : Rat) : Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    (lower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta ∧
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta <=
        (upper : Real)

/-- The direct interval target is exactly the order-16 source-interval field
needed by `Step33Sub0CombinedCancellationSourceIntervalCert.Valid`.  This is
only a normalization interface; it does not provide the future certificate's
concrete bounds. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_direct_interval_to_source_field
    {lower upper : Rat}
    (h :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget
        lower upper) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (lower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          (upper : Real) :=
  h

/--
Rational data shape for the direct whole-expression order-16 interval route.

`Valid` below is still the proof object: this structure alone is not a
certificate and carries no claim that the bounds are true.
-/
structure Step33Sub0CombinedCancellationOrder16DirectIntervalCert where
  lower : Rat
  upper : Rat
  order16Abs : Rat

namespace Step33Sub0CombinedCancellationOrder16DirectIntervalCert

/--
Proof-bearing validity predicate for a direct order-16 interval certificate.

The first field is the hard analytic interval certificate.  The second field is
the exact rational bookkeeping needed to spend that interval as the
`order16Abs` budget in the existing high-order receiver.
-/
structure Valid
    (cert : Step33Sub0CombinedCancellationOrder16DirectIntervalCert) :
    Prop where
  sourceInterval :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget
      cert.lower cert.upper
  order16Budget :
    -(cert.order16Abs : Real) <= (cert.lower : Real) ∧
      (cert.upper : Real) <= (cert.order16Abs : Real)

namespace Valid

/-- Expose the direct interval proof in the exact field shape consumed by
`Step33Sub0CombinedCancellationSourceIntervalCert.Valid`. -/
theorem to_order16SourceInterval
    {cert : Step33Sub0CombinedCancellationOrder16DirectIntervalCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (cert.lower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          (cert.upper : Real) :=
  h.sourceInterval

/-- Expose the exact rational order-16 budget field. -/
theorem to_order16Budget
    {cert : Step33Sub0CombinedCancellationOrder16DirectIntervalCert}
    (h : cert.Valid) :
    -(cert.order16Abs : Real) <= (cert.lower : Real) ∧
      (cert.upper : Real) <= (cert.order16Abs : Real) :=
  h.order16Budget

/-- Convert the direct lower/upper source interval into the norm bound required
by the already checked order-16 component-source bridge. -/
theorem to_componentSource_abs_bound
    {cert : Step33Sub0CombinedCancellationOrder16DirectIntervalCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta‖ <=
        (cert.order16Abs : Real) := by
  intro eta hEta
  have hInterval := h.sourceInterval eta hEta
  have hLower :
      -(cert.order16Abs : Real) <=
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta := by
    linarith [h.order16Budget.1, hInterval.1]
  have hUpper :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta <=
        (cert.order16Abs : Real) := by
    linarith [hInterval.2, h.order16Budget.2]
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hLower, hUpper⟩

/-- Route a valid direct interval certificate through the existing
whole-expression order-16 bridge. -/
theorem to_combinedCancellation_order16_abs_bound
    {cert : Step33Sub0CombinedCancellationOrder16DirectIntervalCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
          eta‖ <=
        (cert.order16Abs : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_bound_of_componentSource
    (cert.order16Abs : Real) h.to_componentSource_abs_bound

end Valid
end Step33Sub0CombinedCancellationOrder16DirectIntervalCert

end Step33
end PSDpd
end Q3
