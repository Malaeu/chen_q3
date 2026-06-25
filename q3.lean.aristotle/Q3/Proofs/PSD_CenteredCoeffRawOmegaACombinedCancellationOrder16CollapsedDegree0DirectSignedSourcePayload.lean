import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourceSegment0Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Parent direct signed-source payload surface for the collapsed degree-0
Step33A.1-A route.

This file intentionally does not claim the full segmented payload.  It records
the checked segment0 row at the expected parent surface and proves the exact
reason it cannot yet feed the family receiver: the one-segment family covers
only `[0, 1/20]`, not the full active cell `[0, 1/10]`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- Segment0 row packaged as a one-segment direct signed-source family. -/
def primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceSegment0OnlyFamily :
    Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert where
  n := 1
  derivAbs := 0
  polyErrorAbs := 0
  seg := fun _ =>
    primaryFiniteRow0Parent0Split100Sub0LocalFactorTaylor18Segment0.toSignedSegmentCert

/-- The segment0 row remains a valid segment row when viewed from the parent
direct signed-source surface. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_parent_valid :
    ∀ i :
        Fin
          primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceSegment0OnlyFamily.n,
      (primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceSegment0OnlyFamily.seg
        i).Valid := by
  intro i
  fin_cases i
  exact
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_valid_generated

/--
The checked segment0 row cannot be promoted to a segment-family cover.

This is the local Lean obstruction behind
`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_only_family_not_cover :
    ¬ Step33Sub0CollapsedDegree0SignedSourceSegmentCover
        primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceSegment0OnlyFamily.n
        primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceSegment0OnlyFamily.seg := by
  intro hCover
  have hEta :
      (3 / 40 : Real) ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
    norm_num
  rcases hCover (3 / 40 : Real) hEta with ⟨i, hSeg⟩
  fin_cases i
  have hUpper : (3 / 40 : Real) <= (1 / 20 : Real) := by
    simpa [
      primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceSegment0OnlyFamily,
      Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.toSignedSegmentCert,
      Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.toRawPolySegmentCert,
      Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.toRawD17SignedFactorSegmentCert,
      Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert.toRawPolySegmentCert,
      Step33Sub0CollapsedDegree0RawPolySegmentCert.toSignedSegmentCert,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU] using
      hSeg.2
  norm_num at hUpper

/--
Support-only sharp two-segment family obtained from the existing raw-D17
factorwise rows.

This family is deliberately not the active closure payload: its budget is
proved not spendable below.  It records the exact local obstruction for the
factorwise two-segment class.
-/
def primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily :
    Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert where
  n := 2
  derivAbs :=
    primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax
  polyErrorAbs :=
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs
  seg := fun i =>
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly
      i).toSignedSegmentCert

/-- The raw-D17 sharp two-segment class supplies valid signed-source segment
rows on both local segments. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_directSignedSource_rawD17SharpTwoSegment_segment_rows_valid :
    ∀ i :
        Fin
          primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily.n,
      (primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily.seg
        i).Valid := by
  intro i
  fin_cases i
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily] using
      primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_left_rawPoly_valid.to_signedSegmentValid
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily] using
      primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_right_rawPoly_valid.to_signedSegmentValid

/-- The support-only sharp two-segment family covers the full active cell. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_directSignedSource_rawD17SharpTwoSegment_cover :
    Step33Sub0CollapsedDegree0SignedSourceSegmentCover
      primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily.n
      primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily.seg := by
  intro eta hEta
  by_cases hLeft : eta <= (1 : Real) / 20
  · refine ⟨⟨0, by decide⟩, ?_⟩
    constructor
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily,
        Step33Sub0CollapsedDegree0RawPolySegmentCert.toSignedSegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly,
        Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert.toRawPolySegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
        primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL] using hEta.1
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily,
        Step33Sub0CollapsedDegree0RawPolySegmentCert.toSignedSegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly,
        Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert.toRawPolySegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
        primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] using hLeft
  · refine ⟨⟨1, by decide⟩, ?_⟩
    have hRightLower : (1 : Real) / 20 <= eta := by
      exact le_of_lt (lt_of_not_ge hLeft)
    constructor
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily,
        Step33Sub0CollapsedDegree0RawPolySegmentCert.toSignedSegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly,
        Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert.toRawPolySegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
        primaryFiniteRow0Parent0Split100Sub0RawD17SegmentL] using hRightLower
    · simpa [
        primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily,
        Step33Sub0CollapsedDegree0RawPolySegmentCert.toSignedSegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPoly,
        Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert.toRawPolySegmentCert,
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp,
        primaryFiniteRow0Parent0Split100Sub0RawD17SegmentU] using hEta.2

/-- The sharp two-segment factorwise support class is not spendable against the
current collapsed degree-0 budget. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_directSignedSource_rawD17SharpTwoSegment_budget_not_spendable :
    ¬
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily.derivAbs :
            Real) *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily.polyErrorAbs :
          Real) := by
  simpa [
    primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily] using
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_not_spendable

end Step33
end PSDpd
end Q3
