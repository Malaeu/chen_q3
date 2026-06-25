import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0CenterAudit

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Signed source certificate surface for the Step33A.1-A direct collapsed
degree-0 route.

This file fixes the proof object expected from the next generator:
lower/upper bounds for the already-subtracted derivative

`ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)`.

It emits no numeric rows and claims no Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

/-- The signed derivative source expression for the direct collapsed degree-0
receiver.  The actual-minus-nominal subtraction is part of the target before
taking norms. -/
def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
    (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
      iteratedDeriv 17
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
    deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta

/-- Proof-producing target for future lower/upper interval rows. -/
def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget
    (lower upper : Rat) : Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    (lower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta ∧
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta <=
        (upper : Real)

/--
Rational data shape for the collapsed degree-0 signed source certificate.

`Valid` below is the proof object.  This structure by itself is only data.
-/
structure Step33Sub0CollapsedDegree0SignedSourceCert where
  lower : Rat
  upper : Rat
  derivAbs : Rat
  polyErrorAbs : Rat

namespace Step33Sub0CollapsedDegree0SignedSourceCert

/--
Proof-bearing validity predicate for the signed source certificate.

The hard field is `sourceInterval`: it must bound the already-subtracted signed
derivative expression on the full cell.  The two budget fields are exact
rational bookkeeping.
-/
structure Valid (cert : Step33Sub0CollapsedDegree0SignedSourceCert) :
    Prop where
  sourceInterval :
    primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget
      cert.lower cert.upper
  derivAbsBudget :
    -(cert.derivAbs : Real) <= (cert.lower : Real) ∧
      (cert.upper : Real) <= (cert.derivAbs : Real)
  degree0Budget :
    (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
        Real) +
      (cert.derivAbs : Real) * ((1 : Real) / 20) <=
        (cert.polyErrorAbs : Real)

/-- Pack generated lower/upper signed-source rows and exact rational budgets
into the existing certificate validity predicate.  This is the intended bridge
for the next generated payload; it does not provide the generated rows. -/
theorem valid_of_signed_interval_and_budget
    {lower upper derivAbs polyErrorAbs : Rat}
    (hInterval :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget
        lower upper)
    (hDerivAbsBudget :
      -(derivAbs : Real) <= (lower : Real) ∧
        (upper : Real) <= (derivAbs : Real))
    (hDegree0Budget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (polyErrorAbs : Real)) :
    (⟨lower, upper, derivAbs, polyErrorAbs⟩ :
        Step33Sub0CollapsedDegree0SignedSourceCert).Valid where
  sourceInterval := hInterval
  derivAbsBudget := hDerivAbsBudget
  degree0Budget := hDegree0Budget

namespace Valid

/-- Convert lower/upper signed source rows into the absolute derivative bound
consumed by the checked degree-0 receiver. -/
theorem to_hSignedD17PolyDeriv
    {cert : Step33Sub0CollapsedDegree0SignedSourceCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
        (cert.derivAbs : Real) := by
  intro eta hEta
  have hInterval := h.sourceInterval eta hEta
  have hLower :
      -(cert.derivAbs : Real) <=
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta := by
    linarith [h.derivAbsBudget.1, hInterval.1]
  have hUpper :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta <=
        (cert.derivAbs : Real) := by
    linarith [hInterval.2, h.derivAbsBudget.2]
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hLower, hUpper⟩

/-- Route a valid signed source certificate into the checked collapsed
degree-0 receiver. -/
theorem to_collapsed_degree0_remainder
    {cert : Step33Sub0CollapsedDegree0SignedSourceCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (cert.polyErrorAbs : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_center_and_polyDeriv_source
    h.to_hSignedD17PolyDeriv
    h.degree0Budget

end Valid
end Step33Sub0CollapsedDegree0SignedSourceCert

/-- Named generator bridge: lower/upper signed-source rows plus exact rational
budgets produce the absolute derivative bound consumed by the checked direct
collapsed degree-0 receiver. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_of_signed_interval
    {lower upper derivAbs : Rat}
    (hInterval :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget
        lower upper)
    (hDerivAbsBudget :
      -(derivAbs : Real) <= (lower : Real) ∧
        (upper : Real) <= (derivAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
        (derivAbs : Real) := by
  intro eta hEta
  have hIntervalEta := hInterval eta hEta
  have hLower :
      -(derivAbs : Real) <=
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta := by
    linarith [hDerivAbsBudget.1, hIntervalEta.1]
  have hUpper :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta <=
        (derivAbs : Real) := by
    linarith [hIntervalEta.2, hDerivAbsBudget.2]
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hLower, hUpper⟩

/-- Named generator bridge: lower/upper signed-source rows and exact rational
budget rows produce the checked collapsed degree-0 remainder bound through the
existing certificate receiver. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_interval_and_budget
    {lower upper derivAbs polyErrorAbs : Rat}
    (hInterval :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget
        lower upper)
    (hDerivAbsBudget :
      -(derivAbs : Real) <= (lower : Real) ∧
        (upper : Real) <= (derivAbs : Real))
    (hDegree0Budget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (polyErrorAbs : Real) :=
  (Step33Sub0CollapsedDegree0SignedSourceCert.valid_of_signed_interval_and_budget
    hInterval hDerivAbsBudget hDegree0Budget).to_collapsed_degree0_remainder

/-- One segment of lower/upper rows for the already-subtracted signed source. -/
structure Step33Sub0CollapsedDegree0SignedSourceSegmentCert where
  cellL : Rat
  cellU : Rat
  lower : Rat
  upper : Rat

namespace Step33Sub0CollapsedDegree0SignedSourceSegmentCert

/-- Proof-bearing validity predicate for one signed-source segment. -/
structure Valid
    (cert : Step33Sub0CollapsedDegree0SignedSourceSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  sourceInterval :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.lower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
            eta <=
          (cert.upper : Real)

/-- Same-segment interval subtraction bridge for the next generator.

This uses component intervals only to produce signed lower/upper rows on the
same cell:
`raw - poly ∈ [rawLower - polyUpper, rawUpper - polyLower]`.  It is not an
independent norm-budget spend for either component. -/
theorem valid_of_raw_poly_intervals
    {cellL cellU rawLower rawUpper polyLower polyUpper lower upper : Rat}
    (hCellSubset :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hRaw :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        (rawLower : Real) <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
            (rawUpper : Real))
    (hPoly :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        (polyLower : Real) <=
            deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta ∧
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta <=
            (polyUpper : Real))
    (hLower :
      (lower : Real) <= (rawLower : Real) - (polyUpper : Real))
    (hUpper :
      (rawUpper : Real) - (polyLower : Real) <= (upper : Real)) :
    (⟨cellL, cellU, lower, upper⟩ :
      Step33Sub0CollapsedDegree0SignedSourceSegmentCert).Valid where
  cellSubset := hCellSubset
  sourceInterval := by
    intro eta hEta
    rcases hRaw eta hEta with ⟨hRawLowerEta, hRawUpperEta⟩
    rcases hPoly eta hEta with ⟨hPolyLowerEta, hPolyUpperEta⟩
    constructor
    · have hSignedLowerEta :
          (lower : Real) <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 17
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                    eta -
              deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
                eta := by
        linarith
          [hLower, hRawLowerEta, hPolyUpperEta]
      simpa
        [primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr]
        using hSignedLowerEta
    · have hSignedUpperEta :
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
                iteratedDeriv 17
                  primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                    eta -
              deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
                eta <=
            (upper : Real) := by
        linarith
          [hUpper, hRawUpperEta, hPolyLowerEta]
      simpa
        [primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr]
        using hSignedUpperEta

end Step33Sub0CollapsedDegree0SignedSourceSegmentCert

/-- Named generator-facing same-segment interval subtraction bridge. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSegmentValid_of_raw_poly_intervals
    {cellL cellU rawLower rawUpper polyLower polyUpper lower upper : Rat}
    (hCellSubset :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hRaw :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        (rawLower : Real) <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 17
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
            (rawUpper : Real))
    (hPoly :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        (polyLower : Real) <=
            deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta ∧
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta <=
            (polyUpper : Real))
    (hLower :
      (lower : Real) <= (rawLower : Real) - (polyUpper : Real))
    (hUpper :
      (rawUpper : Real) - (polyLower : Real) <= (upper : Real)) :
    (⟨cellL, cellU, lower, upper⟩ :
      Step33Sub0CollapsedDegree0SignedSourceSegmentCert).Valid :=
  Step33Sub0CollapsedDegree0SignedSourceSegmentCert.valid_of_raw_poly_intervals
    hCellSubset hRaw hPoly hLower hUpper

/-- One raw/poly same-segment row for the collapsed degree-0 signed source. -/
structure Step33Sub0CollapsedDegree0RawPolySegmentCert where
  cellL : Rat
  cellU : Rat
  rawLower : Rat
  rawUpper : Rat
  polyLower : Rat
  polyUpper : Rat
  lower : Rat
  upper : Rat

namespace Step33Sub0CollapsedDegree0RawPolySegmentCert

/-- Forget the component intervals after they have produced signed rows. -/
def toSignedSegmentCert
    (cert : Step33Sub0CollapsedDegree0RawPolySegmentCert) :
    Step33Sub0CollapsedDegree0SignedSourceSegmentCert where
  cellL := cert.cellL
  cellU := cert.cellU
  lower := cert.lower
  upper := cert.upper

/-- Proof-bearing validity predicate for one raw/poly same-segment row. -/
structure Valid
    (cert : Step33Sub0CollapsedDegree0RawPolySegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  rawInterval :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.rawLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
          (cert.rawUpper : Real)
  polyInterval :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.polyLower : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta <=
          (cert.polyUpper : Real)
  lowerFromRawPoly :
    (cert.lower : Real) <= (cert.rawLower : Real) - (cert.polyUpper : Real)
  upperFromRawPoly :
    (cert.rawUpper : Real) - (cert.polyLower : Real) <= (cert.upper : Real)

namespace Valid

/-- Convert one raw/poly row into the signed segment validity predicate. -/
theorem to_signedSegmentValid
    {cert : Step33Sub0CollapsedDegree0RawPolySegmentCert}
    (h : cert.Valid) :
    cert.toSignedSegmentCert.Valid :=
  Step33Sub0CollapsedDegree0SignedSourceSegmentCert.valid_of_raw_poly_intervals
    h.cellSubset h.rawInterval h.polyInterval h.lowerFromRawPoly
    h.upperFromRawPoly

end Valid
end Step33Sub0CollapsedDegree0RawPolySegmentCert

/-- A finite signed-source segment family covers the full active cell. -/
def Step33Sub0CollapsedDegree0SignedSourceSegmentCover
    (n : Nat)
    (seg : Fin n ->
      Step33Sub0CollapsedDegree0SignedSourceSegmentCert) :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ∃ i : Fin n,
      eta ∈ Set.Icc ((seg i).cellL : Real) ((seg i).cellU : Real)

/-- Segment-local signed lower/upper rows give the same norm bound consumed by
the checked direct collapsed degree-0 receiver. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover
    {n : Nat}
    {seg : Fin n ->
      Step33Sub0CollapsedDegree0SignedSourceSegmentCert}
    {derivAbs : Rat}
    (hValid : ∀ i : Fin n, (seg i).Valid)
    (hLowerBudget :
      ∀ i : Fin n, -(derivAbs : Real) <= ((seg i).lower : Real))
    (hUpperBudget :
      ∀ i : Fin n, ((seg i).upper : Real) <= (derivAbs : Real))
    (hCover :
      Step33Sub0CollapsedDegree0SignedSourceSegmentCover n seg) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
        (derivAbs : Real) := by
  intro eta hEta
  rcases hCover eta hEta with ⟨i, hEtaSeg⟩
  have hInterval := (hValid i).sourceInterval eta hEtaSeg
  have hLower :
      -(derivAbs : Real) <=
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta := by
    linarith [hLowerBudget i, hInterval.1]
  have hUpper :
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr
          eta <=
        (derivAbs : Real) := by
    linarith [hInterval.2, hUpperBudget i]
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hLower, hUpper⟩

/-- Segment-local signed-source rows plus the exact degree-0 budget row produce
the checked collapsed degree-0 remainder bound. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_cover_and_budget
    {n : Nat}
    {seg : Fin n ->
      Step33Sub0CollapsedDegree0SignedSourceSegmentCert}
    {derivAbs polyErrorAbs : Rat}
    (hValid : ∀ i : Fin n, (seg i).Valid)
    (hLowerBudget :
      ∀ i : Fin n, -(derivAbs : Real) <= ((seg i).lower : Real))
    (hUpperBudget :
      ∀ i : Fin n, ((seg i).upper : Real) <= (derivAbs : Real))
    (hCover :
      Step33Sub0CollapsedDegree0SignedSourceSegmentCover n seg)
    (hDegree0Budget :
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
        (derivAbs : Real) * ((1 : Real) / 20) <=
          (polyErrorAbs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (polyErrorAbs : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_center_and_polyDeriv_source
    (primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover
      hValid hLowerBudget hUpperBudget hCover)
    hDegree0Budget

/-- Generator-facing finite signed-source segment family. -/
structure Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert where
  n : Nat
  derivAbs : Rat
  polyErrorAbs : Rat
  seg : Fin n ->
    Step33Sub0CollapsedDegree0SignedSourceSegmentCert

namespace Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert

/-- Proof-bearing validity predicate for a signed-source segment family. -/
structure Valid
    (cert :
      Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert) :
    Prop where
  segmentValid :
    ∀ i : Fin cert.n, (cert.seg i).Valid
  lowerBudget :
    ∀ i : Fin cert.n,
      -(cert.derivAbs : Real) <= ((cert.seg i).lower : Real)
  upperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).upper : Real) <= (cert.derivAbs : Real)
  cover :
    Step33Sub0CollapsedDegree0SignedSourceSegmentCover cert.n cert.seg
  degree0Budget :
    (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
        Real) +
      (cert.derivAbs : Real) * ((1 : Real) / 20) <=
        (cert.polyErrorAbs : Real)

namespace Valid

theorem to_hSignedD17PolyDeriv
    {cert : Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
        (cert.derivAbs : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover
    h.segmentValid h.lowerBudget h.upperBudget h.cover

theorem to_collapsed_degree0_remainder
    {cert : Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (cert.polyErrorAbs : Real) :=
  primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_cover_and_budget
    h.segmentValid h.lowerBudget h.upperBudget h.cover h.degree0Budget

end Valid
end Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert

/-- A finite raw/poly same-segment family covers the full active cell. -/
def Step33Sub0CollapsedDegree0RawPolySegmentCover
    (n : Nat)
    (seg : Fin n ->
      Step33Sub0CollapsedDegree0RawPolySegmentCert) :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ∃ i : Fin n,
      eta ∈ Set.Icc ((seg i).cellL : Real) ((seg i).cellU : Real)

/-- Generator-facing finite raw/poly same-segment family. -/
structure Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert where
  n : Nat
  derivAbs : Rat
  polyErrorAbs : Rat
  seg : Fin n ->
    Step33Sub0CollapsedDegree0RawPolySegmentCert

namespace Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert

/-- Proof-bearing validity predicate for a raw/poly segment family. -/
structure Valid
    (cert :
      Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert) :
    Prop where
  segmentValid :
    ∀ i : Fin cert.n, (cert.seg i).Valid
  lowerBudget :
    ∀ i : Fin cert.n,
      -(cert.derivAbs : Real) <= ((cert.seg i).lower : Real)
  upperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).upper : Real) <= (cert.derivAbs : Real)
  cover :
    Step33Sub0CollapsedDegree0RawPolySegmentCover cert.n cert.seg
  degree0Budget :
    (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
        Real) +
      (cert.derivAbs : Real) * ((1 : Real) / 20) <=
        (cert.polyErrorAbs : Real)

namespace Valid

/-- Convert a raw/poly family into the signed-source segment family receiver. -/
theorem to_signedSegmentFamilyValid
    {cert : Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert}
    (h : cert.Valid) :
    ({ n := cert.n
       derivAbs := cert.derivAbs
       polyErrorAbs := cert.polyErrorAbs
       seg := fun i => (cert.seg i).toSignedSegmentCert } :
        Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert).Valid where
  segmentValid := fun i => (h.segmentValid i).to_signedSegmentValid
  lowerBudget := h.lowerBudget
  upperBudget := h.upperBudget
  cover := by
    intro eta hEta
    rcases h.cover eta hEta with ⟨i, hEtaSeg⟩
    exact ⟨i, hEtaSeg⟩
  degree0Budget := h.degree0Budget

theorem to_hSignedD17PolyDeriv
    {cert : Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
        (cert.derivAbs : Real) :=
  h.to_signedSegmentFamilyValid.to_hSignedD17PolyDeriv

theorem to_collapsed_degree0_remainder
    {cert : Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (cert.polyErrorAbs : Real) :=
  h.to_signedSegmentFamilyValid.to_collapsed_degree0_remainder

end Valid
end Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert

/-- Named receiver theorem for a future raw/poly segment-family payload. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_raw_poly_segment_family_cert
    {cert : Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (cert.polyErrorAbs : Real) :=
  h.to_collapsed_degree0_remainder

/-- Named receiver theorem for the future signed source payload. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_source_cert
    {cert : Step33Sub0CollapsedDegree0SignedSourceCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (cert.polyErrorAbs : Real) :=
  h.to_collapsed_degree0_remainder

/-- Named receiver theorem for a future segmented signed source payload. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_family_cert
    {cert : Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 0 ((1 : Rat) / 20)
            (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff
              primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0)
            eta‖ <=
        (cert.polyErrorAbs : Real) :=
  h.to_collapsed_degree0_remainder

end Step33
end PSDpd
end Q3
