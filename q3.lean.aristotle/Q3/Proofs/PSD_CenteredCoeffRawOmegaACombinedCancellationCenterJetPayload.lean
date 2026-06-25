import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Midpoint/error center-jet rows for the Step33A.1-A sub0 combined-cancellation
payload.

This file closes only the signed-row to center-jet absolute-error adapter.  It
does not provide the order-16 source interval, Horner rows, target-budget rows,
or a `Step33Sub0CombinedCancellationSourceIntervalCert.Valid` payload.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeff
    (j : Fin 16) : Rat :=
  (primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower j +
      primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper j) / 2

def primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs
    (j : Fin 16) : Rat :=
  (primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper j -
      primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower j) / 2

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_coeffErrorAbs_nonneg
    (j : Fin 16) :
    0 <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs
        j : Real) := by
  have hRows :=
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceCenterInterval_of_activeActual_interval
      primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower
      primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper
      primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows
      j
  dsimp [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs]
  norm_num [Rat.cast_div, Rat.cast_sub]
  linarith

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_componentSource_centerJet_abs_generated
    (j : Fin 16) :
    ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
        j.1 -
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeff j :
        Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs
        j : Real) := by
  have hRows :=
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceCenterInterval_of_activeActual_interval
      primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower
      primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper
      primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows
      j
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeff,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs]
    norm_num [Rat.cast_div, Rat.cast_add, Rat.cast_sub]
    linarith
  · dsimp [
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeff,
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs]
    norm_num [Rat.cast_div, Rat.cast_add, Rat.cast_sub]
    linarith

theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_abs_generated
    (j : Fin 16) :
    ‖primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
        j.1 -
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeff j :
        Real)‖ <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs
        j : Real) := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_componentSource
      j]
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_componentSource_centerJet_abs_generated
      j

end Step33
end PSDpd
end Q3
