import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Thin payload adapter for the Step33A.1-A sub0 biased residual route.

The earlier source-Horner family receiver is useful as a row ledger, but it is
not the right way to spend a residual bound against the biased nonzero model:
its source-segment budget compares independent global extrema and can pay the
full biased-model width.  The checked receiver below uses the existing
pointwise residual normalization directly.

This file proves no analytic residual bound and claims no Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- The canonical residual budget for the biased nonzero-model route. -/
def primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat

/--
Named direct adapter for a proof-grade residual bound in the checked same-unit
normalization.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound
    {residualAbs : Rat}
    (hResidualBudget :
      (residualAbs : Real) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
          Real))
    (hRemainder :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
        residualAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
      hResidualBudget
      hRemainder

/--
The target one-premise version: once a proof-grade bound fits inside the chosen
slack exactly, the existing direct interval receiver is closed.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound
    (hRemainder :
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid := by
  refine
    primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound
      ?_ hRemainder
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs
  exact le_rfl

end Step33
end PSDpd
end Q3
