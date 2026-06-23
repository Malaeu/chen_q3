import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Residual-polynomial/Horner checker for the Step33A.1-A sub0 biased order-16
route.

This receiver bounds the residual
`ComponentSource - BiasedNonzeroModelPoly` directly.  It avoids the loss in the
older source-interval adapter, where a source interval was compared against the
global biased-model range and therefore paid the full model width.

This file is still only a checked receiver.  It emits no numerical rows and
does not claim Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
One direct polynomial segment for the biased residual
`ComponentSource - BiasedNonzeroModelPoly`.
-/
structure Step33Sub0CombinedOrder16BiasedResidualHornerCert where
  cellL : Rat
  cellU : Rat
  center : Rat
  degree : Nat
  coeff : Fin (degree + 1) -> Rat
  remainderAbs : Rat
  polyLower : Rat
  polyUpper : Rat

namespace Step33Sub0CombinedOrder16BiasedResidualHornerCert

def poly
    (data : Step33Sub0CombinedOrder16BiasedResidualHornerCert)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial data.degree data.center data.coeff eta

def residualTarget (eta : Real) : Real :=
  primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
      eta -
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
      eta

/--
Proof-bearing validity predicate for one residual-Horner segment.

`residualAbs` is the global bound later spent by the already checked biased
nonzero-model interval receiver.
-/
structure Valid
    (residualAbs : Rat)
    (data : Step33Sub0CombinedOrder16BiasedResidualHornerCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  remainder_nonneg : 0 <= (data.remainderAbs : Real)
  residual_remainder :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖residualTarget eta - data.poly eta‖ <=
        (data.remainderAbs : Real)
  poly_range :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.polyLower : Real) <= data.poly eta ∧
        data.poly eta <= (data.polyUpper : Real)
  residual_lower_budget :
    -(residualAbs : Real) <=
      (data.polyLower : Real) - (data.remainderAbs : Real)
  residual_upper_budget :
    (data.polyUpper : Real) + (data.remainderAbs : Real) <=
      (residualAbs : Real)

namespace Valid

theorem to_residual_bound_on_segment
    {residualAbs : Rat}
    {data : Step33Sub0CombinedOrder16BiasedResidualHornerCert}
    (h : data.Valid residualAbs) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖residualTarget eta‖ <= (residualAbs : Real) := by
  intro eta hEta
  have hRem := h.residual_remainder eta hEta
  rw [Real.norm_eq_abs] at hRem
  have hAbs := abs_le.mp hRem
  have hPoly := h.poly_range eta hEta
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hPolyLower :
        -(residualAbs : Real) <=
          data.poly eta - (data.remainderAbs : Real) := by
      linarith [h.residual_lower_budget, hPoly.1]
    have hResidualLower :
        data.poly eta - (data.remainderAbs : Real) <=
          residualTarget eta := by
      linarith [hAbs.1]
    exact hPolyLower.trans hResidualLower
  · have hResidualUpper :
        residualTarget eta <= data.poly eta + (data.remainderAbs : Real) := by
      linarith [hAbs.2]
    have hPolyUpper :
        data.poly eta + (data.remainderAbs : Real) <=
          (residualAbs : Real) := by
      linarith [h.residual_upper_budget, hPoly.2]
    exact hResidualUpper.trans hPolyUpper

end Valid

/-- Tail of the residual polynomial starting at exponent `i`. -/
def hornerTail
    (data : Step33Sub0CombinedOrder16BiasedResidualHornerCert)
    (i : Nat) (eta : Real) : Real :=
  ∑ j : Fin (data.degree + 1),
    if _h : i <= j.1 then
      (data.coeff j : Real) *
        (eta - (data.center : Real)) ^ (j.1 - i)
    else
      0

theorem hornerTail_zero_eq_poly
    (data : Step33Sub0CombinedOrder16BiasedResidualHornerCert)
    (eta : Real) :
    hornerTail data 0 eta = data.poly eta := by
  unfold hornerTail poly rawOmegaATaylorPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  simp

end Step33Sub0CombinedOrder16BiasedResidualHornerCert

/-- Rational Horner stage bounds for one biased residual segment. -/
structure Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert
    (data : Step33Sub0CombinedOrder16BiasedResidualHornerCert) where
  stageLower : Fin (data.degree + 1) -> Rat
  stageUpper : Fin (data.degree + 1) -> Rat

namespace Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert

structure Valid
    {data : Step33Sub0CombinedOrder16BiasedResidualHornerCert}
    (range : Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert data) :
    Prop where
  stage_bounds :
    ∀ i : Fin (data.degree + 1),
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        (range.stageLower i : Real) <=
          Step33Sub0CombinedOrder16BiasedResidualHornerCert.hornerTail
            data i.1 eta ∧
        Step33Sub0CombinedOrder16BiasedResidualHornerCert.hornerTail
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
    {data : Step33Sub0CombinedOrder16BiasedResidualHornerCert}
    {range : Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert data}
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
          Step33Sub0CombinedOrder16BiasedResidualHornerCert.hornerTail
            data 0 eta :=
        hStage.1
      _ = data.poly eta :=
        Step33Sub0CombinedOrder16BiasedResidualHornerCert.hornerTail_zero_eq_poly
          data eta
  · calc
      data.poly eta =
          Step33Sub0CombinedOrder16BiasedResidualHornerCert.hornerTail
            data 0 eta :=
        (Step33Sub0CombinedOrder16BiasedResidualHornerCert.hornerTail_zero_eq_poly
          data eta).symm
      _ <=
          (range.stageUpper ⟨0, Nat.succ_pos data.degree⟩ : Real) :=
        hStage.2
      _ <= (data.polyUpper : Real) :=
        h.outputUpper

end Valid
end Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert

namespace Step33Sub0CombinedOrder16BiasedResidualHornerCert

namespace Valid

theorem of_horner_range
    {residualAbs : Rat}
    {data : Step33Sub0CombinedOrder16BiasedResidualHornerCert}
    {range : Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert data}
    (hCell :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hRemainderNonneg : 0 <= (data.remainderAbs : Real))
    (hRemainder :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        ‖residualTarget eta - data.poly eta‖ <=
          (data.remainderAbs : Real))
    (hRange : range.Valid)
    (hLower :
      -(residualAbs : Real) <=
        (data.polyLower : Real) - (data.remainderAbs : Real))
    (hUpper :
      (data.polyUpper : Real) + (data.remainderAbs : Real) <=
        (residualAbs : Real)) :
    data.Valid residualAbs := by
  exact
    { cellSubset := hCell
      remainder_nonneg := hRemainderNonneg
      residual_remainder := hRemainder
      poly_range := hRange.poly_range
      residual_lower_budget := hLower
      residual_upper_budget := hUpper }

end Valid
end Step33Sub0CombinedOrder16BiasedResidualHornerCert

def Step33Sub0CombinedOrder16BiasedResidualHornerSegmentCover
    (n : Nat)
    (seg : Fin n -> Step33Sub0CombinedOrder16BiasedResidualHornerCert) :
    Prop :=
  ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
    ∃ i : Fin n,
      eta ∈ Set.Icc ((seg i).cellL : Real) ((seg i).cellU : Real)

structure Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert where
  n : Nat
  residualAbs : Rat
  seg : Fin n -> Step33Sub0CombinedOrder16BiasedResidualHornerCert
  range :
    (i : Fin n) ->
      Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert (seg i)

namespace Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert

structure Valid
    (cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert) :
    Prop where
  cellSubset :
    ∀ i : Fin cert.n,
      ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  remainderNonneg :
    ∀ i : Fin cert.n, 0 <= ((cert.seg i).remainderAbs : Real)
  residualRemainder :
    ∀ i : Fin cert.n,
      ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
        ‖Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta -
            (cert.seg i).poly eta‖ <=
          ((cert.seg i).remainderAbs : Real)
  rangeValid :
    ∀ i : Fin cert.n, (cert.range i).Valid
  residualLowerBudget :
    ∀ i : Fin cert.n,
      -(cert.residualAbs : Real) <=
        ((cert.seg i).polyLower : Real) -
          ((cert.seg i).remainderAbs : Real)
  residualUpperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).polyUpper : Real) +
          ((cert.seg i).remainderAbs : Real) <=
        (cert.residualAbs : Real)
  cover :
    Step33Sub0CombinedOrder16BiasedResidualHornerSegmentCover cert.n cert.seg
  residualSlack :
    (cert.residualAbs : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
        Real)

namespace Valid

theorem to_segmentValid
    {cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert}
    (h : cert.Valid)
    (i : Fin cert.n) :
    (cert.seg i).Valid cert.residualAbs := by
  exact
    Step33Sub0CombinedOrder16BiasedResidualHornerCert.Valid.of_horner_range
      (h.cellSubset i)
      (h.remainderNonneg i)
      (h.residualRemainder i)
      (h.rangeValid i)
      (h.residualLowerBudget i)
      (h.residualUpperBudget i)

theorem to_residualSourceProp
    {cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      cert.residualAbs := by
  intro eta hEta
  rcases h.cover eta hEta with ⟨i, hEtaSeg⟩
  exact (h.to_segmentValid i).to_residual_bound_on_segment eta hEtaSeg

theorem to_order16DirectIntervalValid
    {cert : Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
      h.residualSlack
      h.to_residualSourceProp

end Valid
end Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert

end Step33
end PSDpd
end Q3
