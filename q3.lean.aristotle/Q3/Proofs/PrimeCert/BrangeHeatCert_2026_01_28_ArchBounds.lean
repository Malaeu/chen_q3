import Mathlib
import Q3.Axioms
import Q3.Proofs.A1_density
import Q3.Proofs.Params_Critical
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatIntegrable

noncomputable section

namespace Q3.Proofs.PrimeCert

open MeasureTheory
open Q3

/-- Symmetric arch integrand used in the PrimeHeat certificate. -/
def prime_heat_arch_integrand (ξ : ℝ) : ℝ :=
  |a_star ξ| * heat_weight t_critical ξ

lemma prime_cert_B_max_pos : 0 < prime_cert_B_max := by
  norm_num [prime_cert_B_max]

lemma prime_heat_arch_integrand_even (ξ : ℝ) :
    prime_heat_arch_integrand (-ξ) = prime_heat_arch_integrand ξ := by
  simp [prime_heat_arch_integrand, heat_weight, Q3.a_star_even, pow_two, mul_comm,
    mul_left_comm, mul_assoc]

lemma prime_heat_arch_integrable :
    Integrable prime_heat_arch_integrand := by
  simpa [prime_heat_arch_integrand] using
    (integrable_abs_a_star_mul_heat_weight t_critical t_critical_pos)

lemma prime_heat_arch_integrableOn_symm :
    IntegrableOn prime_heat_arch_integrand
      (Set.Icc (-prime_cert_B_max) prime_cert_B_max) := by
  exact prime_heat_arch_integrable.integrableOn

lemma prime_heat_arch_integrableOn_pos :
    IntegrableOn prime_heat_arch_integrand
      (Set.Icc 0 prime_cert_B_max) := by
  exact prime_heat_arch_integrable.integrableOn

lemma prime_heat_arch_integral_eq_two_mul :
    ∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        prime_heat_arch_integrand ξ
      = 2 * ∫ ξ in Set.Icc 0 prime_cert_B_max, prime_heat_arch_integrand ξ := by
  have hsplit :=
    integral_Icc_eq_integral_Icc_add_neg
      prime_cert_B_max prime_cert_B_max_pos prime_heat_arch_integrand
      prime_heat_arch_integrableOn_symm
  calc
    ∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        prime_heat_arch_integrand ξ
      = ∫ ξ in Set.Icc 0 prime_cert_B_max,
          (prime_heat_arch_integrand ξ + prime_heat_arch_integrand (-ξ)) := hsplit
    _ = ∫ ξ in Set.Icc 0 prime_cert_B_max, (2 * prime_heat_arch_integrand ξ) := by
          congr 1
          ext ξ
          rw [prime_heat_arch_integrand_even]
          ring
    _ = 2 * ∫ ξ in Set.Icc 0 prime_cert_B_max, prime_heat_arch_integrand ξ := by
          rw [MeasureTheory.integral_const_mul]

/-- Envelope reduction: once `|a_star|` is bounded on `[0, B_max]`, the symmetric
PrimeHeat arch integral is reduced to a one-sided weighted integral. -/
theorem prime_heat_bounds_arch_data_of_envelope
    (U : ℝ → ℝ)
    (hU_integrable :
      IntegrableOn
        (fun ξ => U ξ * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * ξ))
        (Set.Icc 0 prime_cert_B_max))
    (hU_bound :
      ∀ ξ ∈ Set.Icc 0 prime_cert_B_max, |a_star ξ| ≤ U ξ)
    (hU_int :
      2 * ∫ ξ in Set.Icc 0 prime_cert_B_max,
        U ξ * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * ξ)
        ≤ prime_cert_L_arch_heat_raw) :
    ∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |a_star ξ| * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * |ξ|)
      ≤ prime_cert_L_arch_heat_raw := by
  have hmono_pos :
      ∫ ξ in Set.Icc 0 prime_cert_B_max, prime_heat_arch_integrand ξ
        ≤
      ∫ ξ in Set.Icc 0 prime_cert_B_max,
        U ξ * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * ξ) := by
    apply MeasureTheory.setIntegral_mono_on
    · exact prime_heat_arch_integrableOn_pos
    · exact hU_integrable
    · exact measurableSet_Icc
    · intro ξ hξ
      have hξ_nonneg : 0 ≤ ξ := hξ.1
      have hweight_nonneg :
          0 ≤ Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * ξ := by
        exact mul_nonneg (Real.exp_nonneg _) hξ_nonneg
      calc
        prime_heat_arch_integrand ξ
            = |a_star ξ| * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * ξ) := by
                simp [prime_heat_arch_integrand, heat_weight, abs_of_nonneg hξ_nonneg]
        _ ≤ U ξ * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * ξ) := by
                exact mul_le_mul_of_nonneg_right (hU_bound ξ hξ) hweight_nonneg
  calc
    ∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |a_star ξ| * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * |ξ|)
      = 2 * ∫ ξ in Set.Icc 0 prime_cert_B_max, prime_heat_arch_integrand ξ := by
          exact prime_heat_arch_integral_eq_two_mul
    _ ≤ 2 * ∫ ξ in Set.Icc 0 prime_cert_B_max,
          U ξ * (Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * ξ) := by
            exact mul_le_mul_of_nonneg_left hmono_pos (by norm_num)
    _ ≤ prime_cert_L_arch_heat_raw := hU_int

end Q3.Proofs.PrimeCert
