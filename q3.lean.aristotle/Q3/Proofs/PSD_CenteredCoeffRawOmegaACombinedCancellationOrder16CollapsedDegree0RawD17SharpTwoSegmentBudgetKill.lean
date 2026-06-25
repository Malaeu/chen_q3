import Q3.Proofs.PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Fail-closed kill for the sharp raw-D17 two-segment signed-factor class.

The sharp local center-jet rows and the two-segment signed-factor receiver are
Lean-checked in
`PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload`.  This file
records the remaining exact arithmetic obstruction under the route-facing name
used by the active monitor: even after the sharp local transfer, the
two-segment factorwise class is not spendable against the current collapsed
degree-0 biased residual budget.

This kills only this factorwise two-segment class.  It does not close
Step33A.1-A and does not rule out a direct whole-expression row source.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

/-- Route-facing spelling of the exact rational budget failure for the sharp
raw-D17 two-segment signed-factor class. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
        primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax /
          20 :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_fail_rat

/-- Real-valued route-facing spelling: the sharp two-segment signed-factor
radius cannot be spent from the current collapsed degree-0 budget. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_not_spendable :
    ¬
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharpRawPolyAbsMax :
            Real) *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) :=
  primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_budget_not_spendable

end Step33
end PSDpd
end Q3
