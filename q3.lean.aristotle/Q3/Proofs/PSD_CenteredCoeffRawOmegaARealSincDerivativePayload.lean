import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincDerivativeCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Exact coarse rational payload for the Step33A.1-A sub0 `realSinc`
derivative majorant.

This file intentionally keeps the payload separate from the analytic bridge.
It proves a named `Valid` certificate and then reuses the already checked
`providesAnalyticMajorant_of_valid` bridge from
`PSD_CenteredCoeffRawOmegaARealSincDerivativeCert.lean`.
-/

namespace Q3
namespace PSDpd
namespace Step33
namespace Step33Sub0RealSincDerivativeMajorantCert

/-- Coarse exact row budget for all realSinc derivative rows `0, ..., 17`.

The value `2` is deliberately not optimized.  It is a proof-grade payload used
to test the downstream scaled-sinc receiver before spending effort on tighter
row budgets. -/
def coarseTwoBaseAbs : Step33Sub0RealSincDerivativeMajorantCert where
  prefixN := fun _ => 0
  tailAbs := fun _ => 2
  baseAbs := fun _ => 2

/-- The coarse `2` row budget satisfies the rational prefix/tail checker. -/
theorem coarseTwoBaseAbs_valid : Valid coarseTwoBaseAbs := by
  constructor
  · intro k
    fin_cases k <;> native_decide
  · intro k
    fin_cases k <;> native_decide

/-- The coarse rational payload supplies the analytic majorants required by
the scaled-sinc receiver interface. -/
theorem coarseTwoBaseAbs_providesAnalyticMajorant :
    ProvidesAnalyticMajorant coarseTwoBaseAbs :=
  providesAnalyticMajorant_of_valid coarseTwoBaseAbs_valid

end Step33Sub0RealSincDerivativeMajorantCert
end Step33
end PSDpd
end Q3
