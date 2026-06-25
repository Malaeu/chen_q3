import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Source
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SignedFactorChecker

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Signed-factor receiver for the collapsed degree-0 raw-D17 rows.

The global symmetric RawProduct18 majorant is proof-grade but too wide for the
collapsed degree-0 budget.  This file records the next local proof surface:
segment-local signed intervals for the factors in

`D18(OmegaActual * ShapeSqActual) = D17(ComponentProductActual)`.

It emits no numerical rows and does not close Step33A.1-A.  It only proves that
future factor rows and exact corner arithmetic feed the already-checked
raw/poly same-segment receiver.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_order18Signed_sum_interval
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    {x lower upper : ι -> Real}
    (hTerm : ∀ i ∈ s, lower i <= x i ∧ x i <= upper i) :
    (∑ i ∈ s, lower i) <= (∑ i ∈ s, x i) ∧
      (∑ i ∈ s, x i) <= (∑ i ∈ s, upper i) := by
  constructor
  · exact Finset.sum_le_sum (fun i hi => (hTerm i hi).1)
  · exact Finset.sum_le_sum (fun i hi => (hTerm i hi).2)

private theorem step22OmegaArchWeight_contDiff18_rawD17SignedRows :
    ContDiff Real 18
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight := by
  rw [show (18 : WithTop ENat) = (17 : WithTop ENat) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  constructor
  · exact fun eta =>
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt
        eta
  · constructor
    · intro h
      norm_num at h
    · have hDeriv :
          deriv Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight =
            step22OmegaArchWeightDerivClosedForm := by
        funext eta
        exact step22OmegaArchWeight_deriv_eq_closedForm eta
      rw [hDeriv]
      exact
        Step33Sub0OmegaPrimeOrder17Payload.step22OmegaArchWeightDerivClosedForm_contDiff17

private theorem primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17SignedRows :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
  simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
    step22OmegaArchWeight_contDiff18_rawD17SignedRows

private theorem primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17SignedRows :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  fun_prop

/-- Signed Leibniz term for `D18(OmegaActual * ShapeSqActual)`. -/
def primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm
    (k : Nat) (eta : Real) : Real :=
  (Nat.choose 18 k : Real) *
    (iteratedDeriv (18 - k)
        primaryFiniteRow0Parent0Split100Sub0OmegaActual eta *
      iteratedDeriv k
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta)

theorem
    primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz
    (eta : Real) :
    iteratedDeriv 18
        primaryFiniteRow0Parent0Split100Sub0RawProductActual eta =
      ∑ k ∈ Finset.range (18 + 1),
        primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta := by
  let omega := primaryFiniteRow0Parent0Split100Sub0OmegaActual
  let shapeSq := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  have h :=
    congrFun
      (primaryFiniteRow0Parent0Split100Sub0_iterate_deriv_mul 18
        omega shapeSq
        primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18_rawD17SignedRows
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18_rawD17SignedRows)
      eta
  simpa [
    iteratedDeriv_eq_iterate,
    primaryFiniteRow0Parent0Split100Sub0RawProductActual,
    primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm,
    omega,
    shapeSq,
    nsmul_eq_mul,
    Nat.cast_id] using h

/--
One raw-D17 signed-factor segment.

The factor rows are segment-local signed intervals for derivatives of
`OmegaActual` and `ShapeSqActual`.  The term rows are exact corner enclosures
for the Leibniz products.  The `rawLower/rawUpper` rows are the scaled raw-D17
interval consumed by the raw/poly same-segment bridge.
-/
structure Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert where
  cellL : Rat
  cellU : Rat
  omegaLower : Nat -> Rat
  omegaUpper : Nat -> Rat
  shapeSqLower : Nat -> Rat
  shapeSqUpper : Nat -> Rat
  termLower : Nat -> Rat
  termUpper : Nat -> Rat
  rawLower : Rat
  rawUpper : Rat

namespace Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert

/-- Corner arithmetic rows for the order-18 signed Leibniz terms. -/
def termCornerRows
    (cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert) :
    Prop :=
  ∀ k ∈ Finset.range (18 + 1),
    (cert.termLower k : Real) <=
        (Nat.choose 18 k : Real) *
          (cert.omegaLower (18 - k) : Real) *
          (cert.shapeSqLower k : Real) ∧
      (cert.termLower k : Real) <=
        (Nat.choose 18 k : Real) *
          (cert.omegaLower (18 - k) : Real) *
          (cert.shapeSqUpper k : Real) ∧
      (cert.termLower k : Real) <=
        (Nat.choose 18 k : Real) *
          (cert.omegaUpper (18 - k) : Real) *
          (cert.shapeSqLower k : Real) ∧
      (cert.termLower k : Real) <=
        (Nat.choose 18 k : Real) *
          (cert.omegaUpper (18 - k) : Real) *
          (cert.shapeSqUpper k : Real) ∧
      (Nat.choose 18 k : Real) *
          (cert.omegaLower (18 - k) : Real) *
          (cert.shapeSqLower k : Real) <=
        (cert.termUpper k : Real) ∧
      (Nat.choose 18 k : Real) *
          (cert.omegaLower (18 - k) : Real) *
          (cert.shapeSqUpper k : Real) <=
        (cert.termUpper k : Real) ∧
      (Nat.choose 18 k : Real) *
          (cert.omegaUpper (18 - k) : Real) *
          (cert.shapeSqLower k : Real) <=
        (cert.termUpper k : Real) ∧
      (Nat.choose 18 k : Real) *
          (cert.omegaUpper (18 - k) : Real) *
          (cert.shapeSqUpper k : Real) <=
        (cert.termUpper k : Real)

def toRawPolySegmentCert
    (cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert)
    (polyLower polyUpper lower upper : Rat) :
    Step33Sub0CollapsedDegree0RawPolySegmentCert where
  cellL := cert.cellL
  cellU := cert.cellU
  rawLower := cert.rawLower
  rawUpper := cert.rawUpper
  polyLower := polyLower
  polyUpper := polyUpper
  lower := lower
  upper := upper

/-- Proof-bearing predicate for one raw-D17 signed-factor segment. -/
structure Valid
    (cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  factorRows :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (18 + 1),
        (cert.omegaLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta <=
            (cert.omegaUpper k : Real) ∧
          (cert.shapeSqLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta <=
            (cert.shapeSqUpper k : Real)
  termCorners :
    cert.termCornerRows
  rawAssembly :
    (cert.rawLower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1), (cert.termLower k : Real)) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1), (cert.termUpper k : Real)) <=
        (cert.rawUpper : Real)

namespace Valid

theorem to_termRows
    {cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (18 + 1),
        (cert.termLower k : Real) <=
            primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta ∧
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta <=
            (cert.termUpper k : Real) := by
  intro eta hEta k hk
  have hk_sub_mem : 18 - k ∈ Finset.range (18 + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.sub_le 18 k))
  have hOmega := h.factorRows eta hEta (18 - k) hk_sub_mem
  have hShapeSq := h.factorRows eta hEta k hk
  have hCorners := h.termCorners k hk
  have hMul :=
    const_mul_mul_interval_bounds_of_four_corners
      (scale := (Nat.choose 18 k : Real))
      (a := (cert.omegaLower (18 - k) : Real))
      (b := (cert.omegaUpper (18 - k) : Real))
      (c := (cert.shapeSqLower k : Real))
      (d := (cert.shapeSqUpper k : Real))
      (x :=
        iteratedDeriv (18 - k)
          primaryFiniteRow0Parent0Split100Sub0OmegaActual eta)
      (y :=
        iteratedDeriv k
          primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta)
      (lower := (cert.termLower k : Real))
      (upper := (cert.termUpper k : Real))
      hOmega.1
      hOmega.2.1
      hShapeSq.2.2.1
      hShapeSq.2.2.2
      hCorners.1
      hCorners.2.1
      hCorners.2.2.1
      hCorners.2.2.2.1
      hCorners.2.2.2.2.1
      hCorners.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.1
      hCorners.2.2.2.2.2.2.2
  simpa [
    primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm,
    mul_assoc] using hMul

/-- Signed factor rows imply the scaled raw-D17 interval consumed by the
raw/poly same-segment receiver. -/
theorem to_rawInterval
    {cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.rawLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
          (cert.rawUpper : Real) := by
  intro eta hEta
  have hTerms :=
    primaryFiniteRow0Parent0Split100Sub0_order18Signed_sum_interval
      (Finset.range (18 + 1))
      (x := fun k =>
        primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta)
      (lower := fun k => (cert.termLower k : Real))
      (upper := fun k => (cert.termUpper k : Real))
      (fun k hk => h.to_termRows eta hEta k hk)
  have hActiveScaleNonneg :
      0 <= primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff := by
    unfold primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff
    positivity
  have hScaledLower :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1), (cert.termLower k : Real)) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta) :=
    mul_le_mul_of_nonneg_left hTerms.1 hActiveScaleNonneg
  have hScaledUpper :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1), (cert.termUpper k : Real)) :=
    mul_le_mul_of_nonneg_left hTerms.2 hActiveScaleNonneg
  have hRawTerm :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1),
            primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta) := by
    rw [
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18,
      primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz]
  constructor
  · calc
      (cert.rawLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            (∑ k ∈ Finset.range (18 + 1), (cert.termLower k : Real)) :=
          h.rawAssembly.1
      _ <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            (∑ k ∈ Finset.range (18 + 1),
              primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta) :=
          hScaledLower
      _ =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta := by
          rw [hRawTerm]
  · calc
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            (∑ k ∈ Finset.range (18 + 1),
              primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k eta) :=
          hRawTerm
      _ <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            (∑ k ∈ Finset.range (18 + 1), (cert.termUpper k : Real)) :=
          hScaledUpper
      _ <= (cert.rawUpper : Real) := h.rawAssembly.2

theorem to_rawPolySegmentValid
    {cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert}
    (h : cert.Valid)
    {polyLower polyUpper lower upper : Rat}
    (hPoly :
      ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
        (polyLower : Real) <=
            deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta ∧
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta <=
            (polyUpper : Real))
    (hLower :
      (lower : Real) <= (cert.rawLower : Real) - (polyUpper : Real))
    (hUpper :
      (cert.rawUpper : Real) - (polyLower : Real) <= (upper : Real)) :
    (cert.toRawPolySegmentCert polyLower polyUpper lower upper).Valid where
  cellSubset := h.cellSubset
  rawInterval := h.to_rawInterval
  polyInterval := hPoly
  lowerFromRawPoly := hLower
  upperFromRawPoly := hUpper

end Valid

end Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert

theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_interval_of_signed_factor_segment
    {cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      (cert.rawLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 17
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
          (cert.rawUpper : Real) :=
  h.to_rawInterval

theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment
    {cert : Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert}
    (h : cert.Valid)
    {polyLower polyUpper lower upper : Rat}
    (hPoly :
      ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
        (polyLower : Real) <=
            deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta ∧
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta <=
            (polyUpper : Real))
    (hLower :
      (lower : Real) <= (cert.rawLower : Real) - (polyUpper : Real))
    (hUpper :
      (cert.rawUpper : Real) - (polyLower : Real) <= (upper : Real)) :
    (cert.toRawPolySegmentCert polyLower polyUpper lower upper).Valid :=
  h.to_rawPolySegmentValid hPoly hLower hUpper

end Step33
end PSDpd
end Q3
