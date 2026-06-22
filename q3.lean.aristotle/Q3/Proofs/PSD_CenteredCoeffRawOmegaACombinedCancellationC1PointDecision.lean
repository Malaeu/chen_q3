import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationC1Source

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Point-decision bridge for the Step33A.1-A sub0 constant C1 source.

This file does not prove the required point separation.  It only records the
small fail-closed implication: if a future proof-grade scalar certificate shows
that the derivative at `0` is already too large for the C1 budget, then the
current constant-midpoint C1 source class cannot be valid.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationC1Source_not_valid_of_budget_lt_twentieth_deriv_abs
    (src : Step33Sub0CombinedCancellationC1SourceCert)
    (hSep :
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
          Real) <
        ((1 : Real) / 20) *
          ‖deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            (0 : Real)‖) :
    ¬ src.Valid := by
  intro h
  have hZeroIn :
      (0 : Real) ∈ Step33Sub0CombinedCancellationC1SourceCert.cell := by
    norm_num [Step33Sub0CombinedCancellationC1SourceCert.cell]
  have hDerivAtZero :=
    h.hDeriv (0 : Real) hZeroIn
  have hDerivTerm :
      ((1 : Real) / 20) *
          ‖deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            (0 : Real)‖ <=
        ((1 : Real) / 20) * (src.derivAbs : Real) := by
    exact mul_le_mul_of_nonneg_left hDerivAtZero (by norm_num)
  have hAnchorNonneg : 0 <= (src.anchorErrorAbs : Real) := by
    exact
      (norm_nonneg
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            Step33Sub0CombinedCancellationC1SourceCert.center -
          Step33Sub0CombinedCancellationIntervalCert.poly
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData
            Step33Sub0CombinedCancellationC1SourceCert.center)).trans h.hAnchor
  have hDerivTermToBudget :
      ((1 : Real) / 20) * (src.derivAbs : Real) <=
        (src.anchorErrorAbs : Real) +
          ((1 : Real) / 20) * (src.derivAbs : Real) := by
    linarith
  have hBudgetAtZero :
      ((1 : Real) / 20) *
          ‖deriv
            primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
            (0 : Real)‖ <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
          Real) :=
    hDerivTerm.trans (hDerivTermToBudget.trans h.hBudget)
  exact not_lt_of_ge hBudgetAtZero hSep

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationC1Source_not_valid_of_twenty_mul_budget_lt_deriv_abs
    (src : Step33Sub0CombinedCancellationC1SourceCert)
    (hSep :
      20 *
          (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalData.remainderAbs :
            Real) <
        ‖deriv
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
          (0 : Real)‖) :
    ¬ src.Valid := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellationC1Source_not_valid_of_budget_lt_twentieth_deriv_abs
      src ?_
  nlinarith

end Step33
end PSDpd
end Q3
