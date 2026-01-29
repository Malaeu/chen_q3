import Mathlib
import Q3.Basic.Defs
import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28
import Q3.Proofs.PrimeCert.Brange_Lipschitz_Analytic
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatScaffold
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatIntegrable
import Q3.Proofs.Q_nonneg_atoms_helpers

/-!
Target: heat-weighted Lipschitz proof on the B-range for t_critical, tau = 0.
This file is intended to close `prime_margin_Lipschitz_on_Brange` using the
heat-weighted numeric certificate from `BrangeHeatCert_2026_01_28.lean`.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open MeasureTheory
open Q3

/-! ### Heat-weighted bounds (assumed inputs)

These are the two numeric inequalities produced by the script:
- arch integral bound
- prime sum bound

They should eventually be certified, but for now they are hypotheses in the
lemmas below so Aristotle can focus on the analytic reduction.
-/

abbrev heat_weight_tc (xi : ℝ) : ℝ :=
  heat_weight t_critical xi

lemma arch_heat_weight_integrable :
    Integrable (fun ξ => |a_star ξ| * heat_weight t_critical ξ) := by
  simpa using
    (integrable_abs_a_star_mul_heat_weight (t := t_critical) t_critical_pos)

lemma arch_term_abs_integral_bound
    (B1 B2 : ℝ)
    (h_int1 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ))
    (h_int2 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B2 ξ)) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      ∫ ξ, |a_star ξ| * |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| := by
  have h_diff :
      arch_term (phi_shift_critical_tau0 B1) -
        arch_term (phi_shift_critical_tau0 B2) =
        ∫ ξ, a_star ξ * phi_shift_critical_tau0 B1 ξ -
          a_star ξ * phi_shift_critical_tau0 B2 ξ := by
    unfold arch_term
    simpa using (MeasureTheory.integral_sub h_int1 h_int2).symm
  calc
    |arch_term (phi_shift_critical_tau0 B1) -
        arch_term (phi_shift_critical_tau0 B2)|
        = |∫ ξ, a_star ξ * phi_shift_critical_tau0 B1 ξ -
              a_star ξ * phi_shift_critical_tau0 B2 ξ| := by
          simpa [h_diff]
    _ = |∫ ξ, a_star ξ * (phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ)| := by
          have hfun :
              (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ -
                a_star ξ * phi_shift_critical_tau0 B2 ξ) =
              (fun ξ => a_star ξ * (phi_shift_critical_tau0 B1 ξ -
                phi_shift_critical_tau0 B2 ξ)) := by
            funext ξ; ring
          simpa [hfun]
    _ ≤ ∫ ξ, |a_star ξ * (phi_shift_critical_tau0 B1 ξ -
            phi_shift_critical_tau0 B2 ξ)| := by
          simpa [Real.norm_eq_abs] using
            (MeasureTheory.abs_integral_le_integral_abs
              (f := fun ξ => a_star ξ *
                (phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ)))
    _ = ∫ ξ, |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| := by
          congr 1; ext ξ; simp [abs_mul]

lemma arch_term_Lipschitz_heat_step1
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_int : Integrable (fun ξ => |a_star ξ| * heat_weight_tc ξ))
    (h_int1 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ))
    (h_int2 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B2 ξ)) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (|B1 - B2| / (B_min ^ 2)) * ∫ ξ, |a_star ξ| * heat_weight_tc ξ := by
  have hB1' : B_min ≤ B1 := hB1.1
  have hB2' : B_min ≤ B2 := hB2.1
  have hphi :
      ∀ ξ, |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| ≤
        heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2) := by
    intro ξ
    simpa [phi_shift_critical_tau0, heat_weight_tc, heat_weight] using
      (phi_shift_lipschitz_B_exp (B1:=B1) (B2:=B2) (xi:=ξ) hB1' hB2')
  set C : ℝ := |B1 - B2| / (B_min ^ 2) with hC
  have h_abs := arch_term_abs_integral_bound (B1:=B1) (B2:=B2) h_int1 h_int2
  have h_point :
      ∀ ξ, |a_star ξ| * |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|
        ≤ |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2)) := by
    intro ξ
    have := hphi ξ
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have h_mono :
      ∫ ξ, |a_star ξ| * |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| ≤
        ∫ ξ, |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2)) := by
    have h_nonneg : 0 ≤ᵐ[volume]
        (fun ξ => |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) := by
      exact MeasureTheory.ae_of_all _ (by
        intro ξ; exact mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h_le :
        (fun ξ => |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) ≤ᵐ[volume]
          (fun ξ => |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))) := by
      exact MeasureTheory.ae_of_all _ h_point
    have h_int_rhs :
        Integrable (fun ξ => |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))) := by
      have h_int_const :
          Integrable (fun ξ => (|a_star ξ| * heat_weight_tc ξ) * C) := by
        exact h_int.mul_const C
      simpa [hC, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h_int_const
    exact MeasureTheory.integral_mono_of_nonneg h_nonneg h_int_rhs h_le
  have h_const :
      ∫ ξ, |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))
        = (|B1 - B2| / (B_min ^ 2)) * ∫ ξ, |a_star ξ| * heat_weight_tc ξ := by
    have hfun :
        (fun ξ => |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))) =
          (fun ξ => (|a_star ξ| * heat_weight_tc ξ) * C) := by
      funext ξ; ring
    simpa [hC, hfun, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      (MeasureTheory.integral_mul_const C (fun ξ => |a_star ξ| * heat_weight_tc ξ))
  calc
    |arch_term (phi_shift_critical_tau0 B1) -
        arch_term (phi_shift_critical_tau0 B2)|
        ≤ ∫ ξ, |a_star ξ| *
            |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| := h_abs
    _ ≤ ∫ ξ, |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2)) := h_mono
    _ = (|B1 - B2| / (B_min ^ 2)) * ∫ ξ, |a_star ξ| * heat_weight_tc ξ := h_const

lemma arch_term_Lipschitz_heat_with_int
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_int : Integrable (fun ξ => |a_star ξ| * heat_weight_tc ξ))
    (h_int1 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ))
    (h_int2 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B2 ξ))
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight_tc ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  have h_step :=
    arch_term_Lipschitz_heat_step1 (B1:=B1) (B2:=B2) hB1 hB2 h_int h_int1 h_int2
  have h_bound :
      (|B1 - B2| / (B_min ^ 2)) * ∫ ξ, |a_star ξ| * heat_weight_tc ξ
        ≤ (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
    calc
      (|B1 - B2| / (B_min ^ 2)) * ∫ ξ, |a_star ξ| * heat_weight_tc ξ
          ≤ (|B1 - B2| / (B_min ^ 2)) * prime_cert_L_arch_heat_raw := by
            exact mul_le_mul_of_nonneg_left h_arch_heat (by
              have : 0 ≤ |B1 - B2| / (B_min ^ 2) := by
                have hBmin : 0 ≤ B_min ^ 2 := by nlinarith [B_min_pos]
                exact div_nonneg (abs_nonneg _) hBmin
              exact this)
      _ = (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
            ring
  exact le_trans h_step h_bound

lemma arch_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight_tc ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  have h_int : Integrable (fun ξ => |a_star ξ| * heat_weight_tc ξ) :=
    arch_heat_weight_integrable
  have hB1pos : 0 < B1 := lt_of_lt_of_le B_min_pos hB1.1
  have hB2pos : 0 < B2 := lt_of_lt_of_le B_min_pos hB2.1
  have h_int1 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ) := by
    simpa [phi_shift_critical_tau0] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
        (B:=B1) (t:=t_critical) (tau:=0) hB1pos)
  have h_int2 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B2 ξ) := by
    simpa [phi_shift_critical_tau0] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
        (B:=B2) (t:=t_critical) (tau:=0) hB2pos)
  exact arch_term_Lipschitz_heat_with_int
    (B1:=B1) (B2:=B2) hB1 hB2 h_int h_int1 h_int2 h_arch_heat

lemma prime_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight_tc (xi_n n) ≤ prime_cert_L_prime_heat_raw) :
    |prime_term (phi_shift_critical_tau0 B1) -
      prime_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  have hB1pos : 0 < B1 := lt_of_lt_of_le B_min_pos hB1.1
  have hB2pos : 0 < B2 := lt_of_lt_of_le B_min_pos hB2.1
  have hsum1 : Summable (fun n => w_Q n * phi_shift_critical_tau0 B1 (xi_n n)) := by
    simpa [phi_shift_critical_tau0] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
        (B:=B1) (t:=t_critical) (tau:=0) hB1pos)
  have hsum2 : Summable (fun n => w_Q n * phi_shift_critical_tau0 B2 (xi_n n)) := by
    simpa [phi_shift_critical_tau0] using
      (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
        (B:=B2) (t:=t_critical) (tau:=0) hB2pos)
  have h_diff :
      prime_term (phi_shift_critical_tau0 B1) -
        prime_term (phi_shift_critical_tau0 B2) =
        ∑' n, w_Q n *
          (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n)) := by
    unfold prime_term
    rw [← hsum1.tsum_sub hsum2]
    congr 1
    ext n
    ring
  have hB1' : B_min ≤ B1 := hB1.1
  have hB2' : B_min ≤ B2 := hB2.1
  set C : ℝ := |B1 - B2| / (B_min ^ 2) with hC
  have hC_nonneg : 0 ≤ C := by
    have hBmin : 0 ≤ B_min ^ 2 := by nlinarith [B_min_pos]
    exact div_nonneg (abs_nonneg _) hBmin
  have hphi :
      ∀ n, |phi_shift_critical_tau0 B1 (xi_n n) -
        phi_shift_critical_tau0 B2 (xi_n n)| ≤
        heat_weight_tc (xi_n n) * C := by
    intro n
    have h := phi_shift_lipschitz_B_exp (B1:=B1) (B2:=B2) (xi:=xi_n n) hB1' hB2'
    simpa [phi_shift_critical_tau0, heat_weight_tc, heat_weight, hC, mul_comm, mul_left_comm,
      mul_assoc, div_eq_mul_inv] using h
  have hsum_heat : Summable (fun n => w_Q n * heat_weight_tc (xi_n n)) := by
    simpa [heat_weight_tc, heat_weight] using
      (Q3.w_Q_heat_weight_summable t_critical t_critical_pos)
  have hsum_bound :
      Summable (fun n => (w_Q n * heat_weight_tc (xi_n n)) * C) :=
    hsum_heat.mul_right C
  have h_bound :
      ∀ n, ‖w_Q n *
        (phi_shift_critical_tau0 B1 (xi_n n) -
          phi_shift_critical_tau0 B2 (xi_n n))‖ ≤
        (w_Q n * heat_weight_tc (xi_n n)) * C := by
    intro n
    have hw_nonneg : 0 ≤ w_Q n := w_Q_nonneg n
    have h_eq :
        ‖w_Q n *
          (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n))‖ =
          w_Q n *
            |phi_shift_critical_tau0 B1 (xi_n n) -
              phi_shift_critical_tau0 B2 (xi_n n)| := by
      simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nonneg]
    calc
      ‖w_Q n * (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n))‖
          = w_Q n * |phi_shift_critical_tau0 B1 (xi_n n) -
              phi_shift_critical_tau0 B2 (xi_n n)| := h_eq
      _ ≤ w_Q n * (heat_weight_tc (xi_n n) * C) := by
            exact mul_le_mul_of_nonneg_left (hphi n) hw_nonneg
      _ = (w_Q n * heat_weight_tc (xi_n n)) * C := by ring
  have h_tsum :
      |∑' n, w_Q n *
          (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n))| ≤
        ∑' n, (w_Q n * heat_weight_tc (xi_n n)) * C := by
    simpa [Real.norm_eq_abs] using
      (tsum_of_norm_bounded
        (f := fun n => w_Q n *
          (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n)))
        (g := fun n => (w_Q n * heat_weight_tc (xi_n n)) * C)
        (a := ∑' n, (w_Q n * heat_weight_tc (xi_n n)) * C)
        hsum_bound.hasSum
        h_bound)
  have h_const :
      (∑' n, (w_Q n * heat_weight_tc (xi_n n)) * C) =
        C * ∑' n, w_Q n * heat_weight_tc (xi_n n) := by
    have h := hsum_heat.tsum_mul_right C
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h_tsum' :
      |prime_term (phi_shift_critical_tau0 B1) -
          prime_term (phi_shift_critical_tau0 B2)| ≤
        C * ∑' n, w_Q n * heat_weight_tc (xi_n n) := by
    simpa [h_diff, h_const] using h_tsum
  have h_final :
      C * ∑' n, w_Q n * heat_weight_tc (xi_n n) ≤
        C * prime_cert_L_prime_heat_raw := by
    exact mul_le_mul_of_nonneg_left h_prime_heat hC_nonneg
  have h_rewrite :
      C * prime_cert_L_prime_heat_raw =
        (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
    simp [hC, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  exact le_trans h_tsum' (by simpa [h_rewrite] using h_final)

lemma margin_Lipschitz_heat_of_bounds
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight_tc ξ ≤ prime_cert_L_arch_heat_raw)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight_tc (xi_n n) ≤ prime_cert_L_prime_heat_raw)
    (h_total :
      (prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2) ≤
        prime_cert_L_total_heat_ub) :
    |margin_tau0 B1 - margin_tau0 B2| ≤
      prime_cert_L_total_heat_ub * |B1 - B2| := by
  have h_arch := arch_term_Lipschitz_heat (B1:=B1) (B2:=B2) hB1 hB2 h_arch_heat
  have h_prime := prime_term_Lipschitz_heat (B1:=B1) (B2:=B2) hB1 hB2 h_prime_heat
  have h_triangle :
      |margin_tau0 B1 - margin_tau0 B2| ≤
        |arch_term (phi_shift_critical_tau0 B1) -
            arch_term (phi_shift_critical_tau0 B2)| +
        |prime_term (phi_shift_critical_tau0 B1) -
            prime_term (phi_shift_critical_tau0 B2)| := by
    unfold margin_tau0
    have h :
        |(arch_term (phi_shift_critical_tau0 B1) -
            prime_term (phi_shift_critical_tau0 B1)) -
          (arch_term (phi_shift_critical_tau0 B2) -
            prime_term (phi_shift_critical_tau0 B2))|
          ≤
          |arch_term (phi_shift_critical_tau0 B1) -
              arch_term (phi_shift_critical_tau0 B2)| +
          |prime_term (phi_shift_critical_tau0 B1) -
              prime_term (phi_shift_critical_tau0 B2)| := by
      have h1 :
          |(arch_term (phi_shift_critical_tau0 B1) -
              arch_term (phi_shift_critical_tau0 B2)) +
            (-(prime_term (phi_shift_critical_tau0 B1) -
                prime_term (phi_shift_critical_tau0 B2)))|
            ≤
            |arch_term (phi_shift_critical_tau0 B1) -
                arch_term (phi_shift_critical_tau0 B2)| +
            |prime_term (phi_shift_critical_tau0 B1) -
                prime_term (phi_shift_critical_tau0 B2)| := by
        simpa [Real.norm_eq_abs, abs_neg, abs_sub_comm, add_comm, add_left_comm, add_assoc] using
          (norm_add_le
            (arch_term (phi_shift_critical_tau0 B1) -
              arch_term (phi_shift_critical_tau0 B2))
            (-(prime_term (phi_shift_critical_tau0 B1) -
                prime_term (phi_shift_critical_tau0 B2))))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have h_sum :
      |arch_term (phi_shift_critical_tau0 B1) -
          arch_term (phi_shift_critical_tau0 B2)| +
        |prime_term (phi_shift_critical_tau0 B1) -
          prime_term (phi_shift_critical_tau0 B2)| ≤
      ((prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2)) *
        |B1 - B2| := by
    have h_sum' :
        |arch_term (phi_shift_critical_tau0 B1) -
            arch_term (phi_shift_critical_tau0 B2)| +
          |prime_term (phi_shift_critical_tau0 B1) -
            prime_term (phi_shift_critical_tau0 B2)| ≤
        (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| +
          (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
      exact add_le_add h_arch h_prime
    have h_rewrite :
        (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| +
          (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| =
        ((prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2)) *
          |B1 - B2| := by
      ring
    exact h_sum'.trans_eq h_rewrite
  have h_total' :
      ((prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2)) *
        |B1 - B2| ≤ prime_cert_L_total_heat_ub * |B1 - B2| := by
    exact mul_le_mul_of_nonneg_right h_total (abs_nonneg _)
  exact le_trans h_triangle (le_trans h_sum h_total')

end Q3.Proofs.PrimeCert
