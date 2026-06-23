import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Direct source-polynomial/Horner checker for the Step33A.1-A sub0 biased
order-16 residual route.

This file is a proof surface only.  It does not emit concrete polynomial rows,
does not prove a source remainder estimate, and does not claim Step33A.1-A
closure.  Its purpose is to give the next generator a fail-closed target for
the route selected after the centered-Taylor signed segment rows were shown to
be budget-dead.

The checked output of this file is an existing
`Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert.Valid`, so it spends
only the biased nonzero-model source budget and never reuses the old zero-model
budget.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
One direct source-polynomial segment for the biased residual order-16 source.

The polynomial approximates
`primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource`
itself on `[cellL, cellU]`.  `sourceLower`/`sourceUpper` are the final source
interval rows that will be compared against the checked biased nonzero-model
range by the existing receiver.
-/
structure Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert where
  cellL : Rat
  cellU : Rat
  center : Rat
  degree : Nat
  coeff : Fin (degree + 1) -> Rat
  remainderAbs : Rat
  polyLower : Rat
  polyUpper : Rat
  sourceLower : Rat
  sourceUpper : Rat

namespace Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert

def poly
    (data : Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial data.degree data.center data.coeff eta

def toSourceSegment
    (data : Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert) :
    Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert where
  cellL := data.cellL
  cellU := data.cellU
  sourceLower := data.sourceLower
  sourceUpper := data.sourceUpper

/--
Proof-bearing validity predicate for a direct source-polynomial segment.

The hard analytic input is `source_remainder`: it must bound the assembled
order-16 component source directly, not separate product summands.  The
polynomial range may be supplied by the Horner checker below.
-/
structure Valid
    (data : Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  remainder_nonneg : 0 <= (data.remainderAbs : Real)
  source_remainder :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          data.poly eta‖ <=
        (data.remainderAbs : Real)
  poly_range :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.polyLower : Real) <= data.poly eta ∧
        data.poly eta <= (data.polyUpper : Real)
  source_lower_budget :
    (data.sourceLower : Real) <=
      (data.polyLower : Real) - (data.remainderAbs : Real)
  source_upper_budget :
    (data.polyUpper : Real) + (data.remainderAbs : Real) <=
      (data.sourceUpper : Real)

namespace Valid

theorem sourceInterval
    {data : Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.sourceLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          (data.sourceUpper : Real) := by
  intro eta hEta
  have hRem := h.source_remainder eta hEta
  rw [Real.norm_eq_abs] at hRem
  have hAbs := abs_le.mp hRem
  have hPoly := h.poly_range eta hEta
  constructor
  · have hPolyLower :
        (data.sourceLower : Real) <=
          data.poly eta - (data.remainderAbs : Real) := by
      linarith [h.source_lower_budget, hPoly.1]
    have hSourceLower :
        data.poly eta - (data.remainderAbs : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta := by
      linarith [hAbs.1]
    exact hPolyLower.trans hSourceLower
  · have hSourceUpper :
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta <=
          data.poly eta + (data.remainderAbs : Real) := by
      linarith [hAbs.2]
    have hPolyUpper :
        data.poly eta + (data.remainderAbs : Real) <=
          (data.sourceUpper : Real) := by
      linarith [h.source_upper_budget, hPoly.2]
    exact hSourceUpper.trans hPolyUpper

theorem to_sourceSegmentValid
    {data : Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert}
    (h : data.Valid)
    {residualAbs : Rat}
    (hLowerBudget :
      -(residualAbs : Real) <=
        (data.sourceLower : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
            Real))
    (hUpperBudget :
      (data.sourceUpper : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
            Real) <=
        (residualAbs : Real)) :
    (data.toSourceSegment).Valid residualAbs := by
  refine
    { cellSubset := ?_
      sourceInterval := ?_
      lowerBudget := ?_
      upperBudget := ?_ }
  · intro eta hEta
    exact h.cellSubset eta hEta
  · intro eta hEta
    exact h.sourceInterval eta hEta
  · exact hLowerBudget
  · exact hUpperBudget

end Valid
end Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert

namespace Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert

/-- Tail of the source polynomial starting at exponent `i`. -/
def hornerTail
    (data : Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert)
    (i : Nat) (eta : Real) : Real :=
  ∑ j : Fin (data.degree + 1),
    if _h : i <= j.1 then
      (data.coeff j : Real) *
        (eta - (data.center : Real)) ^ (j.1 - i)
    else
      0

theorem hornerTail_zero_eq_poly
    (data : Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert)
    (eta : Real) :
    hornerTail data 0 eta = data.poly eta := by
  unfold hornerTail poly rawOmegaATaylorPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  simp

end Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert

/--
Rational Horner stage bounds for a direct biased-residual source polynomial
segment.
-/
structure Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert
    (data :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert) where
  stageLower : Fin (data.degree + 1) -> Rat
  stageUpper : Fin (data.degree + 1) -> Rat

namespace Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert

structure Valid
    {data :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert}
    (range :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert data) :
    Prop where
  stage_bounds :
    ∀ i : Fin (data.degree + 1),
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        (range.stageLower i : Real) <=
          Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert.hornerTail
            data i.1 eta ∧
        Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert.hornerTail
            data i.1 eta <=
          (range.stageUpper i : Real)
  outputLower :
    (data.polyLower : Real) <=
      (range.stageLower ⟨0, Nat.succ_pos data.degree⟩ : Real)
  outputUpper :
    (range.stageUpper ⟨0, Nat.succ_pos data.degree⟩ : Real) <=
      (data.polyUpper : Real)

namespace Valid

theorem poly_range
    {data :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert}
    {range :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert data}
    (h : range.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.polyLower : Real) <= data.poly eta ∧
        data.poly eta <= (data.polyUpper : Real) := by
  intro eta hEta
  have hStage :=
    h.stage_bounds ⟨0, Nat.succ_pos data.degree⟩ eta hEta
  constructor
  · calc
      (data.polyLower : Real) <=
          (range.stageLower ⟨0, Nat.succ_pos data.degree⟩ : Real) :=
        h.outputLower
      _ <=
          Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert.hornerTail
            data 0 eta :=
        hStage.1
      _ = data.poly eta :=
        Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert.hornerTail_zero_eq_poly
          data eta
  · calc
      data.poly eta =
          Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert.hornerTail
            data 0 eta :=
        (Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert.hornerTail_zero_eq_poly
          data eta).symm
      _ <=
          (range.stageUpper ⟨0, Nat.succ_pos data.degree⟩ : Real) :=
        hStage.2
      _ <= (data.polyUpper : Real) :=
        h.outputUpper

end Valid
end Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert

namespace Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert

namespace Valid

/--
Constructor from a direct source remainder estimate and a Lean-checked Horner
range.  The residual budget rows are kept explicit so a generated payload must
prove the same-unit comparison against the biased nonzero model.
-/
theorem of_horner_range
    {data :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert}
    {range :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert data}
    (hCell :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hRemainderNonneg : 0 <= (data.remainderAbs : Real))
    (hRemainder :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            data.poly eta‖ <=
          (data.remainderAbs : Real))
    (hRange : range.Valid)
    (hSourceLower :
      (data.sourceLower : Real) <=
        (data.polyLower : Real) - (data.remainderAbs : Real))
    (hSourceUpper :
      (data.polyUpper : Real) + (data.remainderAbs : Real) <=
        (data.sourceUpper : Real)) :
    data.Valid := by
  exact
    { cellSubset := hCell
      remainder_nonneg := hRemainderNonneg
      source_remainder := hRemainder
      poly_range := hRange.poly_range
      source_lower_budget := hSourceLower
      source_upper_budget := hSourceUpper }

end Valid
end Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert

/--
The Horner-source segment family covers the active cell when the underlying
source-segment family covers it.
-/
def Step33Sub0CombinedOrder16BiasedResidualSourceHornerSegmentCover
    (n : Nat)
    (seg :
      Fin n ->
        Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert) :
    Prop :=
  Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover n
    (fun i => (seg i).toSourceSegment)

/--
A generator-facing Horner family certificate for the biased residual source.

This packages the per-segment Horner range rows, source remainder rows, the
same-unit residual budgets against the biased nonzero model, and the finite
cover into one object that feeds the already checked interval receiver.
-/
structure Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert where
  n : Nat
  residualAbs : Rat
  seg : Fin n -> Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert
  range :
    (i : Fin n) ->
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert (seg i)

namespace Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert

structure Valid
    (cert :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert) :
    Prop where
  cellSubset :
    ∀ i : Fin cert.n,
      ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  remainderNonneg :
    ∀ i : Fin cert.n,
      0 <= ((cert.seg i).remainderAbs : Real)
  sourceRemainder :
    ∀ i : Fin cert.n,
      ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
        ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            (cert.seg i).poly eta‖ <=
          ((cert.seg i).remainderAbs : Real)
  rangeValid :
    ∀ i : Fin cert.n, (cert.range i).Valid
  sourceLowerBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).sourceLower : Real) <=
        ((cert.seg i).polyLower : Real) -
          ((cert.seg i).remainderAbs : Real)
  sourceUpperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).polyUpper : Real) +
          ((cert.seg i).remainderAbs : Real) <=
        ((cert.seg i).sourceUpper : Real)
  biasedLowerBudget :
    ∀ i : Fin cert.n,
      -(cert.residualAbs : Real) <=
        ((cert.seg i).sourceLower : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyUpper :
            Real)
  biasedUpperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).sourceUpper : Real) -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData.polyLower :
            Real) <=
        (cert.residualAbs : Real)
  cover :
    Step33Sub0CombinedOrder16BiasedResidualSourceHornerSegmentCover
      cert.n cert.seg
  residualSlack :
    (cert.residualAbs : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
        Real)

namespace Valid

theorem to_segmentValid
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert}
    (h : cert.Valid)
    (i : Fin cert.n) :
    (cert.seg i).Valid := by
  exact
    Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert.Valid.of_horner_range
      (h.cellSubset i)
      (h.remainderNonneg i)
      (h.sourceRemainder i)
      (h.rangeValid i)
      (h.sourceLowerBudget i)
      (h.sourceUpperBudget i)

theorem to_sourceSegmentValid
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert}
    (h : cert.Valid) :
    ∀ i : Fin cert.n, ((cert.seg i).toSourceSegment).Valid cert.residualAbs := by
  intro i
  exact
    (h.to_segmentValid i).to_sourceSegmentValid
      (h.biasedLowerBudget i)
      (h.biasedUpperBudget i)

theorem to_residualSourceProp
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      cert.residualAbs := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover
      (n := cert.n)
      (seg := fun i => (cert.seg i).toSourceSegment)
      h.to_sourceSegmentValid
      h.cover

theorem to_order16DirectIntervalValid
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_source_segment_cover
      (n := cert.n)
      (seg := fun i => (cert.seg i).toSourceSegment)
      h.residualSlack
      h.to_sourceSegmentValid
      h.cover

end Valid
end Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert

end Step33
end PSDpd
end Q3
