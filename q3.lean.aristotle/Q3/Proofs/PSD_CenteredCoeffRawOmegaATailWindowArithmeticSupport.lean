import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend

set_option linter.mathlibStandardSet false
set_option autoImplicit false

/-!
Raw-Omega Step33 `A` tail-window arithmetic payload interfaces.

This small module is intentionally independent of the prime/live generated
support imports.  Generated rational arithmetic for the raw-Omega `A` side can
check against these structures without rebuilding the whole Step33 prime/P0
payload graph.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport

open CenteredCoeffPayloadImport

/-- Arithmetic-only part of the primary raw-Omega tail-window payload.  This is
the part a rational generated import can close without proving comparison
integral enclosures. -/
structure PrimaryK11RawOmegaAComparisonTailWindowArithmeticPayload where
  cutoff : Real
  tailEnd : Real
  finiteLower : CoeffIndex23 -> Real
  finiteUpper : CoeffIndex23 -> Real
  tailWindowLower : CoeffIndex23 -> Real
  tailWindowUpper : CoeffIndex23 -> Real
  tailRemainderRadius : CoeffIndex23 -> Real
  tailRadius : CoeffIndex23 -> Real
  hCutoff_nonneg : 0 <= cutoff
  hTailWindow : cutoff <= tailEnd
  hTailLowerArith : forall n : CoeffIndex23,
    -tailRadius n <= tailWindowLower n - tailRemainderRadius n
  hTailUpperArith : forall n : CoeffIndex23,
    tailWindowUpper n + tailRemainderRadius n <= tailRadius n
  hPayloadLowerArith : forall n : CoeffIndex23,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceLower n <=
      finiteLower n - tailRadius n
  hPayloadUpperArith : forall n : CoeffIndex23,
    finiteUpper n + tailRadius n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.primaryK11RawOmegaAAbsDistanceUpper n

/-- Arithmetic-only part of the control raw-Omega tail-window payload. -/
structure ControlK9RawOmegaAComparisonTailWindowArithmeticPayload where
  cutoff : Real
  tailEnd : Real
  finiteLower : CoeffIndex23 -> Real
  finiteUpper : CoeffIndex23 -> Real
  tailWindowLower : CoeffIndex23 -> Real
  tailWindowUpper : CoeffIndex23 -> Real
  tailRemainderRadius : CoeffIndex23 -> Real
  tailRadius : CoeffIndex23 -> Real
  hCutoff_nonneg : 0 <= cutoff
  hTailWindow : cutoff <= tailEnd
  hTailLowerArith : forall n : CoeffIndex23,
    -tailRadius n <= tailWindowLower n - tailRemainderRadius n
  hTailUpperArith : forall n : CoeffIndex23,
    tailWindowUpper n + tailRemainderRadius n <= tailRadius n
  hPayloadLowerArith : forall n : CoeffIndex23,
    Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceLower n <=
      finiteLower n - tailRadius n
  hPayloadUpperArith : forall n : CoeffIndex23,
    finiteUpper n + tailRadius n <=
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.controlK9RawOmegaAAbsDistanceUpper n

end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
