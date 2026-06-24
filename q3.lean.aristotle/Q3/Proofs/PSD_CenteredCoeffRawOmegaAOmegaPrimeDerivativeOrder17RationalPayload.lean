import Q3.Proofs.PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17Payload

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
Rational OmegaPrime derivative row-17 payload.

This file closes the rational tail/prefix budget for the analytic row-17
OmegaPrime `tsum` majorant.  It deliberately does not emit the downstream
RawProduct18 or degree-0 payload; those budgets must consume this row through
their own checked interfaces.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

namespace Step33Sub0OmegaPrimeOrder17Payload

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN : Nat := 2

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixAbs : Rat :=
  1024379792916533707003286859546624 / 152587890625

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TailAbs : Rat :=
  745930601206382592 / 30517578125

def primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs : Rat :=
  1024379792916537436656292891459584 / 152587890625

theorem omegaPrimeTrigammaDerivCoeff_norm_eq_order17 :
    ‖Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivCoeff 17‖ =
      ((Nat.factorial 18 : Real) / (2 : Real) ^ 17) := by
  norm_num [
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivCoeff,
    Finset.prod_range_succ]

theorem omegaPrimeTrigammaDerivMajorant_order17_zero :
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
        17 0 =
      (13426750821714886656000 : Real) := by
  rw [
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant_eq_coeff_norm_mul_shifted_rpow,
    omegaPrimeTrigammaDerivCoeff_norm_eq_order17]
  norm_num

theorem omegaPrimeTrigammaDerivMajorant_order17_one :
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
        17 1 =
      ((107414006573719093248 : Rat) / 152587890625 : Rat) := by
  rw [
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant_eq_coeff_norm_mul_shifted_rpow,
    omegaPrimeTrigammaDerivCoeff_norm_eq_order17]
  norm_num

theorem omegaPrimeOrder17_half_prefix_majorant_le_generated :
    (1 / 2 : Real) *
        (Finset.range primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN).sum
          (fun n : Nat =>
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
              17 n) <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixAbs : Real) := by
  rw [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN]
  norm_num [
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN,
    primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixAbs,
    Finset.sum_range_succ,
    omegaPrimeTrigammaDerivMajorant_order17_zero,
    omegaPrimeTrigammaDerivMajorant_order17_one]

theorem omegaPrimeOrder17_half_shifted_tsum_le_generated :
    (1 / 2 : Real) *
        (∑' k : Nat,
          Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
            17 (k + primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN))
      <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TailAbs : Real) := by
  have htail :=
    Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant_shifted_tsum_le_coeff_norm_rpow_bound
        17 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN
        (by norm_num [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN])
  have hscaled :
      (1 / 2 : Real) *
          (∑' k : Nat,
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
              17 (k + primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN))
        <=
        (1 / 2 : Real) *
          (‖Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivCoeff 17‖ *
            ((((primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN : Real) -
                    (3 / 4 : Real)) ^ (-((17 : Real) + 1))) /
              ((17 : Real) + 1))) := by
    exact mul_le_mul_of_nonneg_left htail (by norm_num)
  rw [omegaPrimeTrigammaDerivCoeff_norm_eq_order17] at hscaled
  exact hscaled.trans (by
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN,
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TailAbs])

theorem half_tsum_majorant_le_generated :
    (1 / 2 : Real) *
        (∑' n : Nat,
          Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
            17 n) <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs : Real) := by
  have hsplit :=
    (Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant_summable 17).sum_add_tsum_nat_add
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN
  have hprefix := omegaPrimeOrder17_half_prefix_majorant_le_generated
  have htail := omegaPrimeOrder17_half_shifted_tsum_le_generated
  calc
    (1 / 2 : Real) *
        (∑' n : Nat,
          Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
            17 n)
        =
      (1 / 2 : Real) *
          (Finset.range primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN).sum
            (fun n : Nat =>
              Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
                17 n) +
        (1 / 2 : Real) *
          (∑' k : Nat,
            Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeTrigammaDerivMajorant
              17
                (k + primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixN)) := by
            rw [← hsplit]
            ring
    _ <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixAbs : Real) +
        (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TailAbs : Real) :=
          add_le_add hprefix htail
    _ = (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs : Real) := by
          norm_num [
            primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17PrefixAbs,
            primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17TailAbs,
            primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs]

theorem primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated
    (eta : Real)
    (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖iteratedDeriv 17 step22OmegaArchWeightDerivClosedForm eta‖ <=
      (primaryFiniteRow0Parent0Split100Sub0OmegaPrimeOrder17Abs : Real) := by
  exact
    (primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_tsum
      eta heta).trans half_tsum_majorant_le_generated

end Step33Sub0OmegaPrimeOrder17Payload

end Step33
end PSDpd
end Q3
