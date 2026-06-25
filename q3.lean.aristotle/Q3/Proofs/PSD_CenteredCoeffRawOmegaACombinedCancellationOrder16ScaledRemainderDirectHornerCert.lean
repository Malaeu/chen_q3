import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Horner receiver for the direct Step33A.1-A sub0 scaled-remainder target.

The final target remains the whole signed expression

`ComponentSource - NonzeroModelPoly`.

This file only gives a proof surface: if a future generator supplies
proof-grade Horner stage bounds and a proof-grade whole-expression remainder
bound, the rows can be transported into the existing direct scaled-remainder
payload.  It emits no concrete rows and claims no Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
One Horner-polynomial row package for the direct signed residual
`ComponentSource - NonzeroModelPoly` on a segment.

`polyErrorAbs` bounds the approximation error between the signed residual and
the polynomial; `residualAbs` is the final direct budget spent by the existing
`Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert`.
-/
structure Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert where
  cellL : Rat
  cellU : Rat
  center : Rat
  degree : Nat
  coeff : Fin (degree + 1) -> Rat
  polyErrorAbs : Rat
  polyLower : Rat
  polyUpper : Rat
  lower : Rat
  upper : Rat
  residualAbs : Rat

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert

/-- The generated polynomial used to approximate the direct signed residual. -/
def poly
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial data.degree data.center data.coeff eta

/-- Forget the Horner polynomial and expose the existing direct segment shape. -/
def toDirectSegment
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert where
  cellL := data.cellL
  cellU := data.cellU
  lower := data.lower
  upper := data.upper
  remainderAbs := data.residualAbs

/-- Proof-bearing validity predicate for one direct Horner residual row. -/
structure Valid
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  polyErrorNonneg : 0 <= (data.polyErrorAbs : Real)
  directRemainder :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖(primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
            eta) -
          data.poly eta‖ <=
        (data.polyErrorAbs : Real)
  polyRange :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.polyLower : Real) <= data.poly eta ∧
        data.poly eta <= (data.polyUpper : Real)
  intervalLowerBudget :
    (data.lower : Real) <=
      (data.polyLower : Real) - (data.polyErrorAbs : Real)
  intervalUpperBudget :
    (data.polyUpper : Real) + (data.polyErrorAbs : Real) <=
      (data.upper : Real)
  residualNonneg : 0 <= (data.residualAbs : Real)
  lowerBudget :
    -(data.residualAbs : Real) <= (data.lower : Real)
  upperBudget :
    (data.upper : Real) <= (data.residualAbs : Real)

namespace Valid

theorem directInterval
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.lower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta <=
          (data.upper : Real) := by
  intro eta hEta
  have hRem := h.directRemainder eta hEta
  rw [Real.norm_eq_abs] at hRem
  have hAbs := abs_le.mp hRem
  have hPoly := h.polyRange eta hEta
  constructor
  · have hPolyLower :
        (data.lower : Real) <=
          data.poly eta - (data.polyErrorAbs : Real) := by
      linarith [h.intervalLowerBudget, hPoly.1]
    have hResidualLower :
        data.poly eta - (data.polyErrorAbs : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta := by
      linarith [hAbs.1]
    exact hPolyLower.trans hResidualLower
  · have hResidualUpper :
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta <=
          data.poly eta + (data.polyErrorAbs : Real) := by
      linarith [hAbs.2]
    have hPolyUpper :
        data.poly eta + (data.polyErrorAbs : Real) <=
          (data.upper : Real) := by
      linarith [h.intervalUpperBudget, hPoly.2]
    exact hResidualUpper.trans hPolyUpper

theorem to_directSegmentValid
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert}
    (h : data.Valid) :
    data.toDirectSegment.Valid := by
  refine
    { cellSubset := ?_
      directInterval := ?_
      remainderNonneg := ?_
      lowerBudget := ?_
      upperBudget := ?_ }
  · intro eta hEta
    exact h.cellSubset eta hEta
  · intro eta hEta
    exact h.directInterval eta hEta
  · exact h.residualNonneg
  · exact h.lowerBudget
  · exact h.upperBudget

end Valid

/-- Tail of the direct residual polynomial starting at exponent `i`. -/
def hornerTail
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert)
    (i : Nat) (eta : Real) : Real :=
  ∑ j : Fin (data.degree + 1),
    if _h : i <= j.1 then
      (data.coeff j : Real) *
        (eta - (data.center : Real)) ^ (j.1 - i)
    else
      0

theorem hornerTail_zero_eq_poly
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert)
    (eta : Real) :
    hornerTail data 0 eta = data.poly eta := by
  unfold hornerTail poly rawOmegaATaylorPolynomial
  apply Finset.sum_congr rfl
  intro j _hj
  simp

end Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert

/-- Rational Horner stage bounds for one direct residual segment. -/
structure Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert) where
  stageLower : Fin (data.degree + 1) -> Rat
  stageUpper : Fin (data.degree + 1) -> Rat

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert

structure Valid
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert}
    (range : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert data) :
    Prop where
  stageBounds :
    ∀ i : Fin (data.degree + 1),
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        (range.stageLower i : Real) <=
          Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.hornerTail
            data i.1 eta ∧
        Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.hornerTail
            data i.1 eta <=
          (range.stageUpper i : Real)
  outputLower :
    (data.polyLower : Real) <=
      (range.stageLower ⟨0, Nat.succ_pos data.degree⟩ : Real)
  outputUpper :
    (range.stageUpper ⟨0, Nat.succ_pos data.degree⟩ : Real) <=
      (data.polyUpper : Real)

namespace Valid

theorem polyRange
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert}
    {range : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert data}
    (h : range.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.polyLower : Real) <= data.poly eta ∧
        data.poly eta <= (data.polyUpper : Real) := by
  intro eta hEta
  have hStage :=
    h.stageBounds ⟨0, Nat.succ_pos data.degree⟩ eta hEta
  constructor
  · calc
      (data.polyLower : Real) <=
          (range.stageLower ⟨0, Nat.succ_pos data.degree⟩ : Real) :=
        h.outputLower
      _ <=
          Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.hornerTail
            data 0 eta :=
        hStage.1
      _ = data.poly eta :=
        Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.hornerTail_zero_eq_poly
          data eta
  · calc
      data.poly eta =
          Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.hornerTail
            data 0 eta :=
        (Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.hornerTail_zero_eq_poly
          data eta).symm
      _ <=
          (range.stageUpper ⟨0, Nat.succ_pos data.degree⟩ : Real) :=
        hStage.2
      _ <= (data.polyUpper : Real) :=
        h.outputUpper

end Valid
end Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert
namespace Valid

/-- Constructor from a direct residual remainder estimate and Horner range rows. -/
theorem of_horner_range
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert}
    {range : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert data}
    (hCell :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hPolyErrorNonneg : 0 <= (data.polyErrorAbs : Real))
    (hRemainder :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        ‖(primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta) -
            data.poly eta‖ <=
          (data.polyErrorAbs : Real))
    (hRange : range.Valid)
    (hIntervalLower :
      (data.lower : Real) <=
        (data.polyLower : Real) - (data.polyErrorAbs : Real))
    (hIntervalUpper :
      (data.polyUpper : Real) + (data.polyErrorAbs : Real) <=
        (data.upper : Real))
    (hResidualNonneg : 0 <= (data.residualAbs : Real))
    (hLowerBudget : -(data.residualAbs : Real) <= (data.lower : Real))
    (hUpperBudget : (data.upper : Real) <= (data.residualAbs : Real)) :
    data.Valid := by
  exact
    { cellSubset := hCell
      polyErrorNonneg := hPolyErrorNonneg
      directRemainder := hRemainder
      polyRange := hRange.polyRange
      intervalLowerBudget := hIntervalLower
      intervalUpperBudget := hIntervalUpper
      residualNonneg := hResidualNonneg
      lowerBudget := hLowerBudget
      upperBudget := hUpperBudget }

end Valid
end Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert

/-- The Horner segment family covers the active cell when its direct segments do. -/
def Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover
    (n : Nat)
    (seg :
      Fin n -> Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert) :
    Prop :=
  Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover n
    (fun i => (seg i).toDirectSegment)

/-- Generator-facing Horner family for the direct scaled-remainder target. -/
structure Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert where
  n : Nat
  residualAbs : Rat
  seg : Fin n -> Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert
  range :
    (i : Fin n) ->
      Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert (seg i)

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert

def toDirectFamily
    (cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert where
  n := cert.n
  residualAbs := cert.residualAbs
  seg := fun i => (cert.seg i).toDirectSegment

structure Valid
    (cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert) :
    Prop where
  cellSubset :
    ∀ i : Fin cert.n,
      ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  polyErrorNonneg :
    ∀ i : Fin cert.n, 0 <= ((cert.seg i).polyErrorAbs : Real)
  directRemainder :
    ∀ i : Fin cert.n,
      ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
        ‖(primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
              eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly
              eta) -
            (cert.seg i).poly eta‖ <=
          ((cert.seg i).polyErrorAbs : Real)
  rangeValid :
    ∀ i : Fin cert.n, (cert.range i).Valid
  intervalLowerBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).lower : Real) <=
        ((cert.seg i).polyLower : Real) -
          ((cert.seg i).polyErrorAbs : Real)
  intervalUpperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).polyUpper : Real) +
          ((cert.seg i).polyErrorAbs : Real) <=
        ((cert.seg i).upper : Real)
  segmentResidualNonneg :
    ∀ i : Fin cert.n, 0 <= ((cert.seg i).residualAbs : Real)
  segmentLowerBudget :
    ∀ i : Fin cert.n,
      -(((cert.seg i).residualAbs : Rat) : Real) <=
        ((cert.seg i).lower : Real)
  segmentUpperBudget :
    ∀ i : Fin cert.n,
      ((cert.seg i).upper : Real) <=
        (((cert.seg i).residualAbs : Rat) : Real)
  segmentBudget :
    ∀ i : Fin cert.n,
      (((cert.seg i).residualAbs : Rat) : Real) <= (cert.residualAbs : Real)
  cover :
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover
      cert.n cert.seg

namespace Valid

theorem to_segmentValid
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert}
    (h : cert.Valid)
    (i : Fin cert.n) :
    (cert.seg i).Valid := by
  exact
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_horner_range
      (h.cellSubset i)
      (h.polyErrorNonneg i)
      (h.directRemainder i)
      (h.rangeValid i)
      (h.intervalLowerBudget i)
      (h.intervalUpperBudget i)
      (h.segmentResidualNonneg i)
      (h.segmentLowerBudget i)
      (h.segmentUpperBudget i)

theorem to_directFamilyValid
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert}
    (h : cert.Valid) :
    cert.toDirectFamily.Valid := by
  refine
    { segmentValid := ?_
      segmentBudget := ?_
      cover := ?_ }
  · intro i
    exact (h.to_segmentValid i).to_directSegmentValid
  · intro i
    exact h.segmentBudget i
  · exact h.cover

theorem to_directPayloadTarget
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert}
    (h : cert.Valid)
    (hResidualAbs :
      cert.residualAbs =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget
      cert.toDirectFamily := by
  exact ⟨h.to_directFamilyValid, hResidualAbs⟩

theorem to_nonzeroModelSourceProp
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert}
    (h : cert.Valid)
    (hResidualAbs :
      cert.residualAbs =
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload
    (h.to_directPayloadTarget hResidualAbs)

end Valid
end Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert

end Step33
end PSDpd
end Q3
