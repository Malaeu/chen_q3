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

abbrev brange_Icc : Set ℝ :=
  Set.Icc (-prime_cert_B_max) prime_cert_B_max

lemma heat_weight_tc_continuous : Continuous heat_weight_tc := by
  unfold heat_weight_tc heat_weight
  fun_prop

lemma arch_heat_weight_integrableOn_Icc (R : ℝ) :
    IntegrableOn (fun ξ => |a_star ξ| * heat_weight t_critical ξ) (Set.Icc (-R) R) := by
  have hcont : Continuous (fun ξ => |a_star ξ| * heat_weight t_critical ξ) := by
    exact Q3.a_star_continuous.abs.mul (by
      unfold heat_weight
      fun_prop)
  have hcomp : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  have hcont_on : ContinuousOn (fun ξ => |a_star ξ| * heat_weight t_critical ξ) (Set.Icc (-R) R) :=
    hcont.continuousOn
  simpa using hcont_on.integrableOn_compact hcomp

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
          simp [h_diff]
    _ = |∫ ξ, a_star ξ * (phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ)| := by
          have hfun :
              (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ -
                a_star ξ * phi_shift_critical_tau0 B2 ξ) =
              (fun ξ => a_star ξ * (phi_shift_critical_tau0 B1 ξ -
                phi_shift_critical_tau0 B2 ξ)) := by
            funext ξ; ring
          simp [hfun]
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
    (h_int : IntegrableOn (fun ξ => |a_star ξ| * heat_weight_tc ξ) brange_Icc)
    (h_int1 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ))
    (h_int2 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B2 ξ)) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (|B1 - B2| / (B_min ^ 2)) * ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ := by
  have hB1' : B_min ≤ B1 := hB1.1
  have hB2' : B_min ≤ B2 := hB2.1
  have hB1pos : 0 < B1 := lt_of_lt_of_le B_min_pos hB1.1
  have hB2pos : 0 < B2 := lt_of_lt_of_le B_min_pos hB2.1
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
      ∫ ξ in brange_Icc, |a_star ξ| * |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| ≤
        ∫ ξ in brange_Icc, |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2)) := by
    have h_nonneg : 0 ≤ᵐ[volume.restrict brange_Icc]
        (fun ξ => |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) := by
      exact MeasureTheory.ae_of_all _ (by
        intro ξ; exact mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h_le :
        (fun ξ => |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) ≤ᵐ[volume.restrict brange_Icc]
          (fun ξ => |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))) := by
      exact MeasureTheory.ae_of_all _ h_point
    have h_int_rhs :
        IntegrableOn (fun ξ => |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))) brange_Icc := by
      have h_int_const :
          IntegrableOn (fun ξ => (|a_star ξ| * heat_weight_tc ξ) * C) brange_Icc := by
        exact h_int.mul_const C
      simpa [hC, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h_int_const
    exact MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict brange_Icc) h_nonneg h_int_rhs h_le
  have h_const :
      ∫ ξ in brange_Icc, |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))
        = (|B1 - B2| / (B_min ^ 2)) * ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ := by
    have hfun :
        (fun ξ => |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2))) =
          (fun ξ => (|a_star ξ| * heat_weight_tc ξ) * C) := by
      funext ξ; ring
    simpa [hC, hfun, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      (MeasureTheory.integral_mul_const (μ := volume.restrict brange_Icc)
        C (fun ξ => |a_star ξ| * heat_weight_tc ξ))
  have h_supp :
      ∫ ξ, |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| =
        ∫ ξ in brange_Icc, |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| := by
    have h_eq :
        (fun ξ => |a_star ξ| *
            |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) =
          (brange_Icc).indicator
            (fun ξ => |a_star ξ| *
              |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) := by
      funext ξ
      by_cases hξ : ξ ∈ brange_Icc
      · simp [hξ]
      · have habs : prime_cert_B_max < |ξ| := by
          have hnot : ¬ |ξ| ≤ prime_cert_B_max := by
            intro hle
            have hmem : ξ ∈ brange_Icc := by
              exact (abs_le.mp hle)
            exact hξ hmem
          exact lt_of_not_ge hnot
        have hB1lt : B1 < |ξ| := lt_of_le_of_lt hB1.2 habs
        have hB2lt : B2 < |ξ| := lt_of_le_of_lt hB2.2 habs
        have hzero1 :
            phi_shift_critical_tau0 B1 ξ = 0 := by
          simpa [phi_shift_critical_tau0] using
            (Q3.Proofs.ShiftedWindows.phi_shift_support B1 t_critical 0 ξ hB1pos
              (by simpa using hB1lt))
        have hzero2 :
            phi_shift_critical_tau0 B2 ξ = 0 := by
          simpa [phi_shift_critical_tau0] using
            (Q3.Proofs.ShiftedWindows.phi_shift_support B2 t_critical 0 ξ hB2pos
              (by simpa using hB2lt))
        simp [hξ, hzero1, hzero2]
    have h_eq_int :
        ∫ ξ, |a_star ξ| *
            |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| =
          ∫ ξ, brange_Icc.indicator
              (fun ξ => |a_star ξ| *
                |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) ξ := by
      have h_eq' := congrArg (fun f => ∫ ξ, f ξ) h_eq
      simpa using h_eq'
    calc
      ∫ ξ, |a_star ξ| *
          |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|
          = ∫ ξ, brange_Icc.indicator
              (fun ξ => |a_star ξ| *
                |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ|) ξ := h_eq_int
      _ = ∫ ξ in brange_Icc, |a_star ξ| *
            |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| := by
            simp [MeasureTheory.integral_indicator]
  calc
    |arch_term (phi_shift_critical_tau0 B1) -
        arch_term (phi_shift_critical_tau0 B2)|
        ≤ ∫ ξ, |a_star ξ| *
            |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| := h_abs
    _ = ∫ ξ in brange_Icc, |a_star ξ| *
            |phi_shift_critical_tau0 B1 ξ - phi_shift_critical_tau0 B2 ξ| := h_supp
    _ ≤ ∫ ξ in brange_Icc, |a_star ξ| * (heat_weight_tc ξ * |B1 - B2| / (B_min ^ 2)) := h_mono
    _ = (|B1 - B2| / (B_min ^ 2)) * ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ := h_const

lemma arch_term_Lipschitz_heat_with_int
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_int : IntegrableOn (fun ξ => |a_star ξ| * heat_weight_tc ξ) brange_Icc)
    (h_int1 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B1 ξ))
    (h_int2 : Integrable (fun ξ => a_star ξ * phi_shift_critical_tau0 B2 ξ))
    (h_arch_heat :
      ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  have h_step :=
    arch_term_Lipschitz_heat_step1 (B1:=B1) (B2:=B2) hB1 hB2 h_int h_int1 h_int2
  have h_bound :
      (|B1 - B2| / (B_min ^ 2)) * ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ
        ≤ (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
    calc
      (|B1 - B2| / (B_min ^ 2)) * ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ
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
      ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  have h_int : IntegrableOn (fun ξ => |a_star ξ| * heat_weight_tc ξ) brange_Icc :=
    arch_heat_weight_integrableOn_Icc (R := prime_cert_B_max)
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
      ∑' n, (w_Q n * heat_weight_tc (xi_n n)) *
        (if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0) ≤ prime_cert_L_prime_heat_raw) :
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
  have hphi0 :
      ∀ n, |phi_shift_critical_tau0 B1 (xi_n n) -
        phi_shift_critical_tau0 B2 (xi_n n)| ≤
        heat_weight_tc (xi_n n) * C := by
    intro n
    have h := phi_shift_lipschitz_B_exp (B1:=B1) (B2:=B2) (xi:=xi_n n) hB1' hB2'
    simpa [phi_shift_critical_tau0, heat_weight_tc, heat_weight, hC, mul_comm, mul_left_comm,
      mul_assoc, div_eq_mul_inv] using h
  let brange_ind : ℕ → ℝ :=
    fun n => if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0
  have hphi :
      ∀ n, |phi_shift_critical_tau0 B1 (xi_n n) -
        phi_shift_critical_tau0 B2 (xi_n n)| ≤
        heat_weight_tc (xi_n n) * C * brange_ind n := by
    intro n
    by_cases hxi : |xi_n n| ≤ prime_cert_B_max
    · have h := hphi0 n
      simpa [brange_ind, hxi, mul_assoc] using h
    · have hxi' : prime_cert_B_max < |xi_n n| := lt_of_not_ge hxi
      have hB1lt : B1 < |xi_n n| := lt_of_le_of_lt hB1.2 hxi'
      have hB2lt : B2 < |xi_n n| := lt_of_le_of_lt hB2.2 hxi'
      have hzero1 :
          phi_shift_critical_tau0 B1 (xi_n n) = 0 := by
        simpa [phi_shift_critical_tau0] using
          (Q3.Proofs.ShiftedWindows.phi_shift_support B1 t_critical 0 (xi_n n) hB1pos
            (by simpa using hB1lt))
      have hzero2 :
          phi_shift_critical_tau0 B2 (xi_n n) = 0 := by
        simpa [phi_shift_critical_tau0] using
          (Q3.Proofs.ShiftedWindows.phi_shift_support B2 t_critical 0 (xi_n n) hB2pos
            (by simpa using hB2lt))
      simp [brange_ind, hxi, hzero1, hzero2]
  have hsum_heat :
      Summable (fun n => (w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) := by
    let N := Nat.ceil (Real.exp (2 * Real.pi * prime_cert_B_max)) + 1
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    have h_xi_large : xi_n k > prime_cert_B_max := by
      apply Q3.Proofs.Q_nonneg_lemmas.xi_n_large_of_k_large
      omega
    have hBmax_pos : 0 < prime_cert_B_max := by
      norm_num [prime_cert_B_max]
    have hpos : 0 < xi_n k := lt_trans hBmax_pos h_xi_large
    have h_abs : |xi_n k| > prime_cert_B_max := by
      simpa [abs_of_pos hpos] using h_xi_large
    have hnot : ¬ |xi_n k| ≤ prime_cert_B_max := by
      exact not_le_of_gt h_abs
    simp [brange_ind, hnot]
  have hsum_bound :
      Summable (fun n => ((w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) * C) :=
    hsum_heat.mul_right C
  have h_bound :
      ∀ n, ‖w_Q n *
        (phi_shift_critical_tau0 B1 (xi_n n) -
          phi_shift_critical_tau0 B2 (xi_n n))‖ ≤
        ((w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) * C := by
    intro n
    have hw_nonneg : 0 ≤ w_Q n := w_Q_nonneg n
    have hind_nonneg : 0 ≤ brange_ind n := by
      by_cases hxi : |xi_n n| ≤ prime_cert_B_max <;> simp [brange_ind, hxi]
    have h_eq :
        ‖w_Q n *
          (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n))‖ =
          w_Q n *
            |phi_shift_critical_tau0 B1 (xi_n n) -
              phi_shift_critical_tau0 B2 (xi_n n)| := by
      simp [Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
    calc
      ‖w_Q n * (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n))‖
          = w_Q n * |phi_shift_critical_tau0 B1 (xi_n n) -
              phi_shift_critical_tau0 B2 (xi_n n)| := h_eq
      _ ≤ w_Q n * (heat_weight_tc (xi_n n) * C * brange_ind n) := by
            exact mul_le_mul_of_nonneg_left (hphi n) hw_nonneg
      _ = ((w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) * C := by
            ring
  have h_tsum :
      |∑' n, w_Q n *
          (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n))| ≤
        ∑' n, ((w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) * C := by
    simpa [Real.norm_eq_abs] using
      (tsum_of_norm_bounded
        (f := fun n => w_Q n *
          (phi_shift_critical_tau0 B1 (xi_n n) -
            phi_shift_critical_tau0 B2 (xi_n n)))
        (g := fun n => ((w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) * C)
        (a := ∑' n, ((w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) * C)
        hsum_bound.hasSum
        h_bound)
  have h_const :
      (∑' n, ((w_Q n * heat_weight_tc (xi_n n)) * brange_ind n) * C) =
        C * ∑' n, (w_Q n * heat_weight_tc (xi_n n)) * brange_ind n := by
    have h := hsum_heat.tsum_mul_right C
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h_tsum' :
      |prime_term (phi_shift_critical_tau0 B1) -
          prime_term (phi_shift_critical_tau0 B2)| ≤
        C * ∑' n, (w_Q n * heat_weight_tc (xi_n n)) * brange_ind n := by
    simpa [h_diff, h_const] using h_tsum
  have h_final :
      C * ∑' n, (w_Q n * heat_weight_tc (xi_n n)) * brange_ind n ≤
        C * prime_cert_L_prime_heat_raw := by
    exact mul_le_mul_of_nonneg_left h_prime_heat hC_nonneg
  have h_rewrite :
      C * prime_cert_L_prime_heat_raw =
        (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
    simp [hC, div_eq_mul_inv, mul_comm, mul_left_comm]
  exact le_trans h_tsum' (by simpa [h_rewrite] using h_final)

lemma margin_Lipschitz_heat_of_bounds
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ in brange_Icc, |a_star ξ| * heat_weight_tc ξ ≤ prime_cert_L_arch_heat_raw)
    (h_prime_heat :
      ∑' n, (w_Q n * heat_weight_tc (xi_n n)) *
        (if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0) ≤ prime_cert_L_prime_heat_raw)
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
