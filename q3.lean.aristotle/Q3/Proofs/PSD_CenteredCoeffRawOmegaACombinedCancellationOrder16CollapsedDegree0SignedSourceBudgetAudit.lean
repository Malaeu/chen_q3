import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-!
Budget audit for the collapsed degree-0 signed-source route.

This file is a fail-closed guard.  It checks the tempting independent
absolute-value estimate

`|activeScale * D17(ComponentProductActual)| + |deriv(NominalOrder16Poly)|`

against the current direct collapsed degree-0 budget.  The audit proves that
this triangle estimate is too large to spend.  It does not rule out the real
signed whole-expression row, and it does not close Step33A.1-A.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
Coarse independent triangle derivative bound candidate.

This is deliberately not the signed whole-expression source row required by
the live receiver.  It is only the candidate class being killed by the budget
check below.
-/
def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalScaleAbsBound *
      primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantRat +
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat

/-- Exact arithmetic kill: the independent absolute/triangle derivative
candidate already exceeds the current direct collapsed degree-0 budget. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_triangle_budget_fail_rat :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs <
      primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat /
          20 := by
  native_decide

/-- Real-valued spelling of the same kill, for ledger consumers. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_triangle_budget_not_spendable :
    ¬
      (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs :
          Real) +
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat :
            Real) *
            ((1 : Real) / 20) <=
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) := by
  have h :
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs :
          Real) <
        (primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs +
            primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat /
              20 :
          Rat) := by
    exact_mod_cast
      primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_triangle_budget_fail_rat
  rw [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at h
  have hDiv :
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat :
          Real) /
          20 =
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat :
          Real) *
          ((1 : Real) / 20) := by
    ring
  rw [hDiv] at h
  exact not_le_of_gt h

end Step33
end PSDpd
end Q3
