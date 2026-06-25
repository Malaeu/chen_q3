import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16SignedFactorChecker
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Bridge from existing centered-Taylor absolute derivative majorants to the
signed factor-row field used by the Step33A.1-A order-16 signed-factor checker.

This file does not emit concrete rational rows and does not claim Step33A.1-A
closure.  It proves that a future generator may certify signed factor rows by
enclosing the existing proof-grade absolute majorant arrays.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound
    {x m lower upper : Real}
    (hAbs : ‖x‖ <= m)
    (hLower : lower <= -m)
    (hUpper : m <= upper) :
    lower <= x ∧ x <= upper := by
  rw [Real.norm_eq_abs] at hAbs
  have hBounds := abs_le.mp hAbs
  constructor <;> linarith

namespace Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert

/--
Rational row enclosures for the four existing centered-Taylor absolute
derivative majorant arrays.
-/
def centeredTaylorAbsEnclosures
    (cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert) :
    Prop :=
  (∀ k ∈ Finset.range (16 + 1),
      (cert.omegaPrimeLower k : Real) <=
          -primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
            k ∧
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActualDerivativeMajorant
            k <=
          (cert.omegaPrimeUpper k : Real)) ∧
    (∀ k ∈ Finset.range (16 + 1),
      (cert.omegaLower k : Real) <=
          -primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
            k ∧
        primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant
            k <=
          (cert.omegaUpper k : Real)) ∧
    (∀ k ∈ Finset.range (16 + 1),
      (cert.shapeSqLower k : Real) <=
          -primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
            k ∧
        primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant
            k <=
          (cert.shapeSqUpper k : Real)) ∧
    (∀ k ∈ Finset.range (16 + 1),
      (cert.shapeSqDerivLower k : Real) <=
          -primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
            k ∧
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActualDerivativeMajorant
            k <=
          (cert.shapeSqDerivUpper k : Real))

/--
The existing absolute derivative majorant arrays are enough to populate the
checker `factorRows` field once the future payload provides rational rows
enclosing each `[-majorant, +majorant]`.
-/
theorem factorRows_of_centeredTaylorAbsEnclosures
    {cert : Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert}
    (hCell :
      ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hRows : cert.centeredTaylorAbsEnclosures) :
    ∀ eta ∈ Set.Icc (cert.cellL : Real) (cert.cellU : Real),
      ∀ k ∈ Finset.range (16 + 1),
        (cert.omegaPrimeLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual eta <=
            (cert.omegaPrimeUpper k : Real) ∧
          (cert.omegaLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0OmegaActual eta <=
            (cert.omegaUpper k : Real) ∧
          (cert.shapeSqLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta <=
            (cert.shapeSqUpper k : Real) ∧
          (cert.shapeSqDerivLower k : Real) <=
            iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta ∧
          iteratedDeriv k
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual eta <=
            (cert.shapeSqDerivUpper k : Real) := by
  intro eta hEta k hk
  have hEtaCell := hCell eta hEta
  have hkLe : k <= 16 :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hOmegaPrimeAbs :=
    primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_derivative_abs_of_centeredTaylor
      eta hEtaCell k hkLe
  have hOmegaAbs :=
    primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs_of_centeredTaylor
      eta hEtaCell k hkLe
  have hShapeSqAbs :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_centeredTaylor
      eta hEtaCell k hkLe
  have hShapeSqDerivAbs :=
    primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivActual_derivative_abs_of_centeredTaylor
      eta hEtaCell k hkLe
  have hOmegaPrimeRows := hRows.1 k hk
  have hOmegaRows := hRows.2.1 k hk
  have hShapeSqRows := hRows.2.2.1 k hk
  have hShapeSqDerivRows := hRows.2.2.2 k hk
  have hOmegaPrime :=
    primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound
      hOmegaPrimeAbs hOmegaPrimeRows.1 hOmegaPrimeRows.2
  have hOmega :=
    primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound
      hOmegaAbs hOmegaRows.1 hOmegaRows.2
  have hShapeSq :=
    primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound
      hShapeSqAbs hShapeSqRows.1 hShapeSqRows.2
  have hShapeSqDeriv :=
    primaryFiniteRow0Parent0Split100Sub0_interval_of_abs_bound
      hShapeSqDerivAbs hShapeSqDerivRows.1 hShapeSqDerivRows.2
  exact
    ⟨hOmegaPrime.1, hOmegaPrime.2, hOmega.1, hOmega.2, hShapeSq.1,
      hShapeSq.2, hShapeSqDeriv.1, hShapeSqDeriv.2⟩

end Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert

end Step33
end PSDpd
end Q3
