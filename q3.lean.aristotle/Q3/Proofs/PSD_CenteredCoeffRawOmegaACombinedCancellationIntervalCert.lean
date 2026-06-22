import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof checker surface for the Step33A.1-A sub0 combined cancellation interval.

This file does not provide a concrete certificate.  It defines the exact
single-cell certificate shape that a future interval/rational backend must
populate, and proves that a valid certificate supplies the `hCombined`
assumption consumed by the checked combined interval receiver.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def step33Sub0CombinedCancellationTargetLower : Rat :=
  (-94119513411 : Rat) / 500000000000000000000000000000

def step33Sub0CombinedCancellationTargetUpper : Rat :=
  (1866608532757 : Rat) / 500000000000000000000000000000

/--
A single-segment certificate for the whole combined cancellation expression.

The polynomial must approximate
`primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr` itself,
not the two summands separately.
-/
structure Step33Sub0CombinedCancellationSegmentCert where
  cellL : Rat
  cellU : Rat
  center : Rat
  degree : Nat
  coeff : Fin (degree + 1) -> Rat
  remainderAbs : Rat
  polyLower : Rat
  polyUpper : Rat

abbrev Step33Sub0CombinedCancellationIntervalCert :=
  Step33Sub0CombinedCancellationSegmentCert

namespace Step33Sub0CombinedCancellationIntervalCert

def poly (data : Step33Sub0CombinedCancellationIntervalCert)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial data.degree data.center data.coeff eta

structure Valid (data : Step33Sub0CombinedCancellationIntervalCert) : Prop where
  cellL_eq : data.cellL = 0
  cellU_eq : data.cellU = (1 : Rat) / 10
  remainder_nonneg : 0 <= (data.remainderAbs : Real)
  remainder_bound :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
          data.poly eta‖ <= (data.remainderAbs : Real)
  poly_range :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (data.polyLower : Real) <= data.poly eta ∧
        data.poly eta <= (data.polyUpper : Real)
  budget_lower :
    (step33Sub0CombinedCancellationTargetLower : Real) <=
      (data.polyLower : Real) - (data.remainderAbs : Real)
  budget_upper :
    (data.polyUpper : Real) + (data.remainderAbs : Real) <=
      (step33Sub0CombinedCancellationTargetUpper : Real)

theorem Valid.to_hCombined
    {data : Step33Sub0CombinedCancellationIntervalCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) := by
  intro eta hEta
  have hRem := h.remainder_bound eta hEta
  rw [Real.norm_eq_abs] at hRem
  have hAbs := abs_le.mp hRem
  have hPoly := h.poly_range eta hEta
  constructor
  · have hPolyLower :
        (step33Sub0CombinedCancellationTargetLower : Real) <=
          data.poly eta - (data.remainderAbs : Real) := by
      linarith [h.budget_lower, hPoly.1]
    have hExprLower :
        data.poly eta - (data.remainderAbs : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta := by
      linarith [hAbs.1]
    exact hPolyLower.trans hExprLower
  · have hExprUpper :
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <=
          data.poly eta + (data.remainderAbs : Real) := by
      linarith [hAbs.2]
    have hPolyUpper :
        data.poly eta + (data.remainderAbs : Real) <=
          (step33Sub0CombinedCancellationTargetUpper : Real) := by
      linarith [h.budget_upper, hPoly.2]
    exact hExprUpper.trans hPolyUpper

theorem Valid.to_fullTaylor_residual_deriv_interval
    {data : Step33Sub0CombinedCancellationIntervalCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  by
    have hCombined :
        ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
          ((-94119513411 : Real) /
              500000000000000000000000000000) <=
              primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
                eta ∧
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
                eta <=
              ((1866608532757 : Real) /
                500000000000000000000000000000) := by
      intro eta hEta
      simpa [step33Sub0CombinedCancellationTargetLower,
        step33Sub0CombinedCancellationTargetUpper] using
        h.to_hCombined eta hEta
    have hDeriv :=
      primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combined_bounds
        hCombined
    intro eta hEta
    simpa [step33Sub0CombinedCancellationTargetLower,
      step33Sub0CombinedCancellationTargetUpper] using hDeriv eta hEta

end Step33Sub0CombinedCancellationIntervalCert

end Step33
end PSDpd
end Q3
