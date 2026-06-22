import Q3.Proofs.PSD_CenteredCoeffRawOmegaARealSincShapeSqPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

/-!
Coarse Taylor-source feed for the active Step33A.1-A ShapeSqDeriv layer.

This file checks only the interface from the proof-grade coarse ShapeSqDeriv
interval certificate into the existing Taylor-source receiver.  The resulting
budget is deliberately coarse and is not claimed to be sharp enough for the
final chunk certificate.
-/

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- The exact coarse ShapeSqDeriv interval certificate data used by the Taylor
source feed below. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData :
    ShapeSqDerivTaylorIntervalCert :=
  ShapeSqDerivTaylorIntervalCert.singleAbs
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs
    primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqOrder16Abs

/-- Exact remainder expression required by
`ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource` for the
coarse certificate. -/
def primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs :
    Real :=
  (∑ j : Fin 16,
      (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeffErrorAbs j :
        Real) *
        ((1 : Real) / 20) ^ j.1) +
    (primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqOrder16Abs : Real) *
      ((1 : Real) / 20) ^ 16 / (Nat.factorial 16 : Real)

/-- Feed the checked coarse ShapeSqDeriv interval certificate into the existing
degree-15 derivative Taylor-source receiver. -/
theorem primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTaylorSource_of_coarseTwo :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv eta -
        rawOmegaATaylorPolynomial 15 (1 / 20 : Rat)
          primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqCoeff
          eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs := by
  exact
    ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource
      (data := primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData)
      (remainderAbs :=
        primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs)
      (by
        simpa [primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData] using
          primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_coarseTwo)
      (by
        unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorData
        unfold primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqDerivTaylorRemainderAbs
        rfl)

end Step33
end PSDpd
end Q3
