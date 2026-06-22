import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
C1 source checker for the Step33A.1-A sub0 combined-cancellation remainder.

This file does not provide the analytic anchor or derivative enclosures.  It
proves the small Lean bridge requested for the current live route: a
proof-grade center error plus a proof-grade uniform derivative bound imply the
whole-expression remainder premise consumed by the concrete interval payload.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

structure Step33Sub0CombinedCancellationC1SourceCert where
  anchorErrorAbs : Rat
  derivAbs : Rat

namespace Step33Sub0CombinedCancellationC1SourceCert

def cell : Set Real :=
  Set.Icc (0 : Real) ((1 : Real) / 10)

def center : Real :=
  (1 : Real) / 20

structure Valid
    (src : Step33Sub0CombinedCancellationC1SourceCert) : Prop where
  hPolyConst :
    ∀ eta : Real,
      Step33Sub0CombinedCancellationIntervalCert.poly
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
          eta =
        Step33Sub0CombinedCancellationIntervalCert.poly
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
          center
  hDifferentiable :
    ∀ eta ∈ cell,
      DifferentiableAt Real
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta
  hAnchor :
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
        center -
      Step33Sub0CombinedCancellationIntervalCert.poly
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
        center‖ <=
      (src.anchorErrorAbs : Real)
  hDeriv :
    ∀ eta ∈ cell,
      ‖deriv
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
          eta‖ <=
        (src.derivAbs : Real)
  hBudget :
    (src.anchorErrorAbs : Real) +
        ((1 : Real) / 20) * (src.derivAbs : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
        Real)

theorem concrete_poly_const (eta : Real) :
    Step33Sub0CombinedCancellationIntervalCert.poly
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
        eta =
      Step33Sub0CombinedCancellationIntervalCert.poly
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
        center := by
  simp [
    center,
    Step33Sub0CombinedCancellationIntervalCert.poly,
    rawOmegaATaylorPolynomial,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalCoeff,
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationMidpoint]

namespace Valid

theorem remainder_bound
    {src : Step33Sub0CombinedCancellationC1SourceCert}
    (h : src.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp := by
  intro eta hEta
  have hCenter : center ∈ cell := by
    norm_num [center, cell]
  have hDerivAbsNonneg : 0 <= (src.derivAbs : Real) := by
    exact
      (norm_nonneg
        (deriv
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
          center)).trans (h.hDeriv center hCenter)
  have hEtaInCell : eta ∈ cell := by
    simpa [cell] using hEta
  have hRadius : ‖eta - center‖ <= (1 : Real) / 20 := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · dsimp [center]
      linarith [hEta.1]
    · dsimp [center]
      linarith [hEta.2]
  have hLipBase :
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            center‖ <=
        (src.derivAbs : Real) * ‖eta - center‖ := by
    exact
      (convex_Icc (0 : Real) ((1 : Real) / 10)).norm_image_sub_le_of_norm_deriv_le
        (f := primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr)
        (C := (src.derivAbs : Real))
        h.hDifferentiable h.hDeriv hCenter hEtaInCell
  have hLip :
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            center‖ <=
        ((1 : Real) / 20) * (src.derivAbs : Real) := by
    calc
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            center‖ <=
          (src.derivAbs : Real) * ‖eta - center‖ := hLipBase
      _ <= (src.derivAbs : Real) * ((1 : Real) / 20) :=
        mul_le_mul_of_nonneg_left hRadius hDerivAbsNonneg
      _ = ((1 : Real) / 20) * (src.derivAbs : Real) := by ring
  have hSplit :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
          Step33Sub0CombinedCancellationIntervalCert.poly
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
            center =
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
              center) +
          (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
              center -
            Step33Sub0CombinedCancellationIntervalCert.poly
              primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
              center) := by
    ring
  calc
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
        Step33Sub0CombinedCancellationIntervalCert.poly
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
          eta‖ =
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
        Step33Sub0CombinedCancellationIntervalCert.poly
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
          center‖ := by
        rw [h.hPolyConst eta]
    _ =
      ‖(primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
              center) +
          (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
              center -
            Step33Sub0CombinedCancellationIntervalCert.poly
              primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
              center)‖ := by
        rw [hSplit]
    _ <=
        ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta -
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
              center‖ +
          ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
              center -
            Step33Sub0CombinedCancellationIntervalCert.poly
              primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
              center‖ :=
        norm_add_le _ _
    _ <=
        ((1 : Real) / 20) * (src.derivAbs : Real) +
          (src.anchorErrorAbs : Real) :=
        add_le_add hLip h.hAnchor
    _ =
        (src.anchorErrorAbs : Real) +
          ((1 : Real) / 20) * (src.derivAbs : Real) := by
        ring
    _ <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
          Real) :=
        h.hBudget

end Valid
end Step33Sub0CombinedCancellationC1SourceCert

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_c1_source
    {src : Step33Sub0CombinedCancellationC1SourceCert}
    (h : src.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound
    h.remainder_bound

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_hCombined_of_c1_source
    {src : Step33Sub0CombinedCancellationC1SourceCert}
    (h : src.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta ∧
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_c1_source
    h).to_hCombined

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_c1_source
    {src : Step33Sub0CombinedCancellationC1SourceCert}
    (h : src.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (step33Sub0CombinedCancellationTargetLower : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert.residual
            eta <= (step33Sub0CombinedCancellationTargetUpper : Real) :=
  (primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_c1_source
    h).to_fullTaylor_residual_deriv_interval

end Step33
end PSDpd
end Q3
