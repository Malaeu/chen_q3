import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_Data

/-!
Reusable analytic majorant lemmas for the archimedean heat integral

  ∫_{[-Bmax,Bmax]} |f(ξ)| * exp(-4π² t_critical ξ²) * |ξ| dξ.

This module is checker-free and keeps only kernel-safe measure-theoretic
reductions (pointwise majorant -> integral bound).
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

def arch_heat_kernel_tc (ξ : ℝ) : ℝ :=
  Real.exp (-4 * Real.pi ^ 2 * t_critical * ξ ^ 2) * |ξ|

lemma arch_heat_kernel_tc_nonneg (ξ : ℝ) : 0 ≤ arch_heat_kernel_tc ξ := by
  exact mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)

lemma arch_heat_integral_mono_on_brange
    {f g : ℝ → ℝ}
    (h_int_f :
      MeasureTheory.IntegrableOn
        (fun ξ => |f ξ| * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_int_g :
      MeasureTheory.IntegrableOn
        (fun ξ => g ξ * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (hfg : ∀ ξ, |f ξ| ≤ g ξ) :
      (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |f ξ| * arch_heat_kernel_tc ξ)
      ≤
      (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        g ξ * arch_heat_kernel_tc ξ) := by
  let s : Set ℝ := Set.Icc (-prime_cert_B_max) prime_cert_B_max
  have h_le :
      (fun ξ => |f ξ| * arch_heat_kernel_tc ξ) ≤ᵐ[MeasureTheory.volume.restrict s]
        (fun ξ => g ξ * arch_heat_kernel_tc ξ) := by
    refine Filter.Eventually.of_forall ?_
    intro ξ
    exact mul_le_mul_of_nonneg_right (hfg ξ) (arch_heat_kernel_tc_nonneg ξ)
  simpa [s] using MeasureTheory.integral_mono_ae h_int_f h_int_g h_le

lemma arch_heat_integral_le_of_abs_le_const
    {f : ℝ → ℝ}
    {M : ℝ}
    (h_int_f :
      MeasureTheory.IntegrableOn
        (fun ξ => |f ξ| * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_int_kernel :
      MeasureTheory.IntegrableOn
        arch_heat_kernel_tc
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (hM : ∀ ξ, |f ξ| ≤ M) :
    (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |f ξ| * arch_heat_kernel_tc ξ)
      ≤
      M *
        (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
          arch_heat_kernel_tc ξ) := by
  have h_int_g :
      MeasureTheory.IntegrableOn
        (fun ξ => M * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_int_kernel.const_mul M
  have hmono :=
    arch_heat_integral_mono_on_brange
      (f := f) (g := fun _ => M) h_int_f h_int_g hM
  have hconst :
      (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
          M * arch_heat_kernel_tc ξ)
        =
        M *
          (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
            arch_heat_kernel_tc ξ) := by
    simpa using
      (MeasureTheory.integral_const_mul
        (μ := MeasureTheory.volume.restrict (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
        M (fun ξ => arch_heat_kernel_tc ξ))
  calc
    (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |f ξ| * arch_heat_kernel_tc ξ)
      ≤
      (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        M * arch_heat_kernel_tc ξ) := hmono
    _ =
      M *
        (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
          arch_heat_kernel_tc ξ) := hconst

lemma prime_heat_bounds_arch_of_uniform_abs_bound
    {M : ℝ}
    (h_int_f :
      MeasureTheory.IntegrableOn
        (fun ξ => |a_star ξ| * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_int_kernel :
      MeasureTheory.IntegrableOn
        arch_heat_kernel_tc
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (hM : ∀ ξ, |a_star ξ| ≤ M)
    (h_int :
      M *
          (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
            arch_heat_kernel_tc ξ)
        ≤
        prime_cert_L_arch_heat_raw) :
    (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |a_star ξ| * arch_heat_kernel_tc ξ)
      ≤
      prime_cert_L_arch_heat_raw := by
  have h_le :=
    arch_heat_integral_le_of_abs_le_const
      (f := a_star) h_int_f h_int_kernel hM
  exact h_le.trans h_int

lemma prime_heat_bounds_arch_of_majorant
    (g : ℝ → ℝ)
    (h_int_f :
      MeasureTheory.IntegrableOn
        (fun ξ => |a_star ξ| * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_int_g :
      MeasureTheory.IntegrableOn
        (fun ξ => g ξ * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_majorant : ∀ ξ, |a_star ξ| ≤ g ξ)
    (h_int :
      (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
          g ξ * arch_heat_kernel_tc ξ)
        ≤
        prime_cert_L_arch_heat_raw) :
    (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |a_star ξ| * arch_heat_kernel_tc ξ)
      ≤
      prime_cert_L_arch_heat_raw := by
  exact
    (arch_heat_integral_mono_on_brange
      (f := a_star) (g := g) h_int_f h_int_g h_majorant).trans h_int

lemma prime_heat_bounds_arch_of_linear_abs_bound
    {C0 C1 : ℝ}
    (h_int_f :
      MeasureTheory.IntegrableOn
        (fun ξ => |a_star ξ| * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_int_g :
      MeasureTheory.IntegrableOn
        (fun ξ => (C0 + C1 * |ξ|) * arch_heat_kernel_tc ξ)
        (Set.Icc (-prime_cert_B_max) prime_cert_B_max))
    (h_growth : ∀ ξ, |a_star ξ| ≤ C0 + C1 * |ξ|)
    (h_int :
      (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
          (C0 + C1 * |ξ|) * arch_heat_kernel_tc ξ)
        ≤
        prime_cert_L_arch_heat_raw) :
    (∫ ξ in Set.Icc (-prime_cert_B_max) prime_cert_B_max,
        |a_star ξ| * arch_heat_kernel_tc ξ)
      ≤
      prime_cert_L_arch_heat_raw := by
  exact
    prime_heat_bounds_arch_of_majorant
      (g := fun ξ => C0 + C1 * |ξ|)
      h_int_f h_int_g h_growth h_int

end Q3.Proofs.PrimeCert
