import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedTaylorSource

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Interval-row receiver for the direct Step33A.1-A sub0 collapsed-expression route.

This file is intentionally one layer before the Taylor receiver in
`...DirectCollapsedTaylorSource`.  It does not provide generated rows and does
not close Step33A.1-A.  It only proves that a generator may supply rational
lower/upper source intervals for the collapsed expression center jets and the
order-16 source row, and Lean can turn those intervals into the existing
absolute-error Taylor certificate.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
Generator-facing interval data for one direct collapsed-expression Taylor
segment.

The `data` field is the already checked absolute-error Taylor row container.
The interval rows below are the proof-producing source a generator must emit:
they bound the exact center-jet coefficients and the exact order-16 derivative
of the same collapsed expression on the same cell.
-/
structure Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert where
  data : Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert
  coeffLower : Fin 16 -> Rat
  coeffUpper : Fin 16 -> Rat
  order16Lower : Rat
  order16Upper : Rat

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert

structure Valid
    (cert :
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (cert.data.cellL : Real) (cert.data.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  centerMem :
    (cert.data.center : Real) ∈
      Set.Icc (cert.data.cellL : Real) (cert.data.cellU : Real)
  smooth :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
  coeffErrorNonneg :
    ∀ j : Fin 16, 0 <= (cert.data.coeffErrorAbs j : Real)
  remainderNonneg :
    0 <= (cert.data.remainderAbs : Real)
  sourceCenterInterval :
    ∀ j : Fin 16,
      (cert.coeffLower j : Real) <=
          iteratedDeriv j.1
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            (cert.data.center : Real) /
            (Nat.factorial j.1 : Real) ∧
        iteratedDeriv j.1
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            (cert.data.center : Real) /
            (Nat.factorial j.1 : Real) <=
          (cert.coeffUpper j : Real)
  coeffErrorBudget :
    ∀ j : Fin 16,
      (cert.data.coeff j : Real) - (cert.data.coeffErrorAbs j : Real) <=
          (cert.coeffLower j : Real) ∧
        (cert.coeffUpper j : Real) <=
          (cert.data.coeff j : Real) + (cert.data.coeffErrorAbs j : Real)
  order16SourceInterval :
    ∀ eta ∈ Set.Icc (cert.data.cellL : Real) (cert.data.cellU : Real),
      (cert.order16Lower : Real) <=
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta ∧
        iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta <=
          (cert.order16Upper : Real)
  order16Budget :
    -(cert.data.order16Abs : Real) <= (cert.order16Lower : Real) ∧
      (cert.order16Upper : Real) <= (cert.data.order16Abs : Real)
  radiusBound :
    ∀ eta ∈ Set.Icc (cert.data.cellL : Real) (cert.data.cellU : Real),
      ‖eta - (cert.data.center : Real)‖ <= (cert.data.radius : Real)
  remainderBudget :
    (∑ j : Fin 16,
        (cert.data.coeffErrorAbs j : Real) * (cert.data.radius : Real) ^ j.1) +
        (cert.data.order16Abs : Real) * (cert.data.radius : Real) ^ 16 /
          (Nat.factorial 16 : Real) <=
      (cert.data.remainderAbs : Real)

namespace Valid

theorem centerJet
    {cert :
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert}
    (h : cert.Valid) :
    ∀ j : Fin 16,
      ‖iteratedDeriv j.1
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
          (cert.data.center : Real) /
          (Nat.factorial j.1 : Real) -
        (cert.data.coeff j : Real)‖ <=
        (cert.data.coeffErrorAbs j : Real) := by
  intro j
  rw [Real.norm_eq_abs]
  exact abs_le.mpr
    ⟨by
      have hLo := (h.sourceCenterInterval j).1
      have hBudgetLo := (h.coeffErrorBudget j).1
      linarith,
    by
      have hHi := (h.sourceCenterInterval j).2
      have hBudgetHi := (h.coeffErrorBudget j).2
      linarith⟩

theorem order16
    {cert :
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.data.cellL : Real) (cert.data.cellU : Real),
      ‖iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
          eta‖ <=
        (cert.data.order16Abs : Real) := by
  intro eta hEta
  rw [Real.norm_eq_abs]
  exact abs_le.mpr
    ⟨by
      have hLo := (h.order16SourceInterval eta hEta).1
      have hBudgetLo := h.order16Budget.1
      linarith,
    by
      have hHi := (h.order16SourceInterval eta hEta).2
      have hBudgetHi := h.order16Budget.2
      linarith⟩

theorem to_collapsedTaylorValid
    {cert :
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert}
    (h : cert.Valid) :
    cert.data.Valid where
  cellSubset := h.cellSubset
  centerMem := h.centerMem
  smooth := h.smooth
  coeffErrorNonneg := h.coeffErrorNonneg
  remainderNonneg := h.remainderNonneg
  centerJet := h.centerJet
  order16 := h.order16
  radiusBound := h.radiusBound
  remainderBudget := h.remainderBudget

end Valid

end Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsedTaylorValid_of_source_interval
    {cert :
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert}
    (h : cert.Valid) :
    cert.data.Valid :=
  h.to_collapsedTaylorValid

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_source_interval
    {cert :
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert}
    (h : cert.Valid) :
    ∀ eta ∈ Set.Icc (cert.data.cellL : Real) (cert.data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          cert.data.poly eta‖ <=
        (cert.data.remainderAbs : Real) :=
  h.to_collapsedTaylorValid.remainder_bound

end Step33
end PSDpd
end Q3
