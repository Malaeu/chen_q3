import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Exact range-checker surface for the Step33A.1-A sub0 combined-cancellation
polynomial.

This file intentionally does not provide the concrete combined-cancellation
payload and does not prove the analytic Taylor remainder bound.  It isolates the
next proof-producing arithmetic layer: a generated certificate may prove exact
rational bounds for the Horner tails of `data.poly`; this checker then converts
those bounds into the `poly_range` field required by
`Step33Sub0CombinedCancellationIntervalCert.Valid`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

namespace Step33Sub0CombinedCancellationIntervalCert

/-- Tail of the Taylor polynomial starting at exponent `i`, normalized so that
`hornerTail data 0` is exactly `data.poly`. -/
def hornerTail
    (data : Step33Sub0CombinedCancellationSegmentCert)
    (i : Nat) (eta : Real) : Real :=
  ∑ j : Fin (data.degree + 1),
    if _h : i <= j.1 then
      (data.coeff j : Real) *
        (eta - (data.center : Real)) ^ (j.1 - i)
    else
      0

theorem hornerTail_zero_eq_poly
    (data : Step33Sub0CombinedCancellationSegmentCert)
    (eta : Real) :
    hornerTail data 0 eta =
      Step33Sub0CombinedCancellationIntervalCert.poly data eta := by
  unfold hornerTail poly rawOmegaATaylorPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  simp

end Step33Sub0CombinedCancellationIntervalCert

/--
Rational stage bounds for the Horner tails of a
`Step33Sub0CombinedCancellationSegmentCert`.

`stageLower 0`/`stageUpper 0` bound the full polynomial.  Later generated
payloads can fill all stages with exact rational arithmetic rows before
spending the result as `poly_range`.
-/
structure Step33Sub0CombinedCancellationHornerRangeCert
    (data : Step33Sub0CombinedCancellationSegmentCert) where
  stageLower : Fin (data.degree + 1) -> Rat
  stageUpper : Fin (data.degree + 1) -> Rat

namespace Step33Sub0CombinedCancellationHornerRangeCert

structure Valid
    {data : Step33Sub0CombinedCancellationSegmentCert}
    (range : Step33Sub0CombinedCancellationHornerRangeCert data) : Prop where
  stage_bounds :
    ∀ i : Fin (data.degree + 1),
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        (range.stageLower i : Real) <=
          Step33Sub0CombinedCancellationIntervalCert.hornerTail data i.1
            eta ∧
        Step33Sub0CombinedCancellationIntervalCert.hornerTail data i.1
            eta <= (range.stageUpper i : Real)
  outputLower :
    (data.polyLower : Real) <=
      (range.stageLower ⟨0, Nat.succ_pos data.degree⟩ : Real)
  outputUpper :
    (range.stageUpper ⟨0, Nat.succ_pos data.degree⟩ : Real) <=
      (data.polyUpper : Real)

namespace Valid

theorem poly_range
    {data : Step33Sub0CombinedCancellationSegmentCert}
    {range : Step33Sub0CombinedCancellationHornerRangeCert data}
    (h : range.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      (data.polyLower : Real) <=
          Step33Sub0CombinedCancellationIntervalCert.poly data eta ∧
        Step33Sub0CombinedCancellationIntervalCert.poly data eta <=
          (data.polyUpper : Real) := by
  intro eta hEta
  have hStage :=
    h.stage_bounds ⟨0, Nat.succ_pos data.degree⟩ eta hEta
  constructor
  · calc
      (data.polyLower : Real) <=
          (range.stageLower ⟨0, Nat.succ_pos data.degree⟩ : Real) :=
        h.outputLower
      _ <=
          Step33Sub0CombinedCancellationIntervalCert.hornerTail data 0 eta :=
        hStage.1
      _ = Step33Sub0CombinedCancellationIntervalCert.poly data eta :=
        Step33Sub0CombinedCancellationIntervalCert.hornerTail_zero_eq_poly
          data eta
  · calc
      Step33Sub0CombinedCancellationIntervalCert.poly data eta =
          Step33Sub0CombinedCancellationIntervalCert.hornerTail data 0 eta :=
        (Step33Sub0CombinedCancellationIntervalCert.hornerTail_zero_eq_poly
          data eta).symm
      _ <=
          (range.stageUpper ⟨0, Nat.succ_pos data.degree⟩ : Real) :=
        hStage.2
      _ <= (data.polyUpper : Real) :=
        h.outputUpper

theorem poly_range_unit_cell
    {data : Step33Sub0CombinedCancellationSegmentCert}
    {range : Step33Sub0CombinedCancellationHornerRangeCert data}
    (h : range.Valid)
    (hCellL : data.cellL = 0)
    (hCellU : data.cellU = (1 : Rat) / 10) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (data.polyLower : Real) <=
          Step33Sub0CombinedCancellationIntervalCert.poly data eta ∧
        Step33Sub0CombinedCancellationIntervalCert.poly data eta <=
          (data.polyUpper : Real) := by
  intro eta hEta
  have hEtaData :
      eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real) := by
    constructor
    · simpa [hCellL] using hEta.1
    · have hU : ((data.cellU : Rat) : Real) = (1 : Real) / 10 := by
        rw [hCellU]
        norm_num
      simpa [hU] using hEta.2
  exact h.poly_range eta hEtaData

end Valid
end Step33Sub0CombinedCancellationHornerRangeCert

namespace Step33Sub0CombinedCancellationHornerRangeSmoke

def coeff (_i : Fin 3) : Rat :=
  0

def stageLower (_i : Fin 3) : Rat :=
  0

def stageUpper (_i : Fin 3) : Rat :=
  0

def data : Step33Sub0CombinedCancellationSegmentCert where
  cellL := 0
  cellU := 1
  center := 0
  degree := 2
  coeff := coeff
  remainderAbs := 0
  polyLower := 0
  polyUpper := 0

def range : Step33Sub0CombinedCancellationHornerRangeCert data where
  stageLower := stageLower
  stageUpper := stageUpper

theorem range_valid :
    range.Valid := by
  refine
    { stage_bounds := ?_
      outputLower := ?_
      outputUpper := ?_ }
  · intro i eta hEta
    fin_cases i <;>
      simp [range, stageLower, stageUpper, data, coeff,
        Step33Sub0CombinedCancellationIntervalCert.hornerTail]
  · norm_num [range, stageLower, data]
  · norm_num [range, stageUpper, data]

theorem degree_two_smoke_poly_range :
    ∀ eta ∈ Set.Icc (0 : Real) (1 : Real),
      (0 : Real) <=
          Step33Sub0CombinedCancellationIntervalCert.poly data eta ∧
        Step33Sub0CombinedCancellationIntervalCert.poly data eta <=
          (0 : Real) := by
  simpa [data] using
    Step33Sub0CombinedCancellationHornerRangeCert.Valid.poly_range
      range_valid

end Step33Sub0CombinedCancellationHornerRangeSmoke

end Step33
end PSDpd
end Q3
