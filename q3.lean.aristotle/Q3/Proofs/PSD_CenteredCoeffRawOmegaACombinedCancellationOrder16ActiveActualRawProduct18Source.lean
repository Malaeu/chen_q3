import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18MajorantReceiver
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17RationalPayload
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeSqOrder18Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-grade RawProduct18 source for the Step33A.1-A sub0 degree-0 gate.

The factor Leibniz receiver is already checked.  This file supplies the
remaining factor arrays through order 18:

* `OmegaActual` rows `0..17` reuse the existing centered-Taylor order-17
  source;
* `OmegaActual` row `18` is shifted to the checked OmegaPrime order-17 rational
  payload;
* `ShapeSqActual` rows `0..18` use the checked sharp ShapeSq order-18 source.

It closes the uniform `D^18 RawProductActual` source, and therefore the
uniform `D^17 ComponentProductActual` source consumed downstream by the
degree-0 active-actual row.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_center_mem_rawProduct18Source :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter ∈
      Set.Icc (0 : Real) ((1 : Real) / 10) := by
  norm_num [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter]

private theorem step22OmegaArchWeight_contDiff18_rawProduct18Source :
    ContDiff Real 18
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight := by
  rw [show (18 : WithTop ENat) = (17 : WithTop ENat) + 1 by norm_num,
    contDiff_succ_iff_deriv]
  constructor
  · exact fun eta =>
      Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight_differentiableAt
        eta
  · constructor
    · intro h
      norm_num at h
    · have hDeriv :
          deriv Q3.PSDpd.CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeight =
            step22OmegaArchWeightDerivClosedForm := by
        funext eta
        exact step22OmegaArchWeight_deriv_eq_closedForm eta
      rw [hDeriv]
      exact
        Step33Sub0OmegaPrimeOrder17Payload.step22OmegaArchWeightDerivClosedForm_contDiff17

private theorem primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18 :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
  simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
    step22OmegaArchWeight_contDiff18_rawProduct18Source

private theorem primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18 :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
  unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  fun_prop

theorem primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv18_eq_omegaPrime17
    (eta : Real) :
    iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual eta =
      iteratedDeriv 17 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual
        eta := by
  simpa using
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv_succ_eq_omegaPrime
      17 eta

/-- Public derivative-majorant array for the integrated Omega factor through
row 18. -/
def primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18
    (k : Nat) : Real :=
  if _hk : k < 19 then
    if _hk17 : k <= 17 then
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17 k
    else
      (Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs :
        Real)
  else
    0

private theorem
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18_nonneg
    (k : Nat) (hk : k <= 18) :
    0 <=
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18 k := by
  have hk19 : k < 19 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18
  simp [hk19]
  by_cases hk17 : k <= 17
  · simp [hk17]
    have hBound :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs17
        primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
        primaryFiniteRow0Parent0Split100Sub0_center_mem_rawProduct18Source
        k hk17
    exact (norm_nonneg _).trans hBound
  · have hk_eq : k = 18 := by omega
    simp [hk_eq,
      Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs]
    norm_num

theorem primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18
    (eta : Real) (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (k : Nat) (hk : k <= 18) :
    ‖iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18
        k := by
  have hk19 : k < 19 := Nat.lt_succ_of_le hk
  unfold primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18
  simp [hk19]
  by_cases hk17 : k <= 17
  · simp [hk17]
    exact
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs17
        eta heta k hk17
  · have hk_eq : k = 18 := by omega
    simp [hk_eq]
    have hShift :=
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv18_eq_omegaPrime17
        eta
    have hBase :=
      Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated
        eta heta
    rw [hShift]
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using hBase

/-- The generated RawProduct18 majorant in the checked local normalization. -/
def primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantGenerated :
    Real :=
  primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant
    primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18
    primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18

theorem primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_generated :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 18
          primaryFiniteRow0Parent0Split100Sub0RawProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantGenerated := by
  simpa [primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantGenerated] using
    primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs
      primaryFiniteRow0Parent0Split100Sub0OmegaActual_contDiff18
      primaryFiniteRow0Parent0Split100Sub0ShapeSqActual_contDiff18
      primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18_nonneg
      primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs18
      primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18

theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_generated :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta‖ <=
        primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantGenerated := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs
      primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18MajorantGenerated
      primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_generated

end Step33
end PSDpd
end Q3
