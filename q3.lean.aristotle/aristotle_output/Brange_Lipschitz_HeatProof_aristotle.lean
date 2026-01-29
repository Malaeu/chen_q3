/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8f48791a-4121-462f-ad6d-98e72cc114fc

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error while processing imports for this file.
Details:
Axioms were added during init_sorries: ['Q3.Szego_Bottcher_eigenvalue_bound', 'Q3.explicit_formula', 'Q3.eigenvalue_le_norm', 'Q3.A3_bridge_rayleigh_axiom', 'Q3.Q_nonneg_on_atoms_uniform', 'Q3.Weil_criterion_tau0', 'Q3.c_star_le_c_arch', 'Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom', 'Q3.A1_density_WK_axiom', 'Q3.Schur_test', 'Q3.Q_Lipschitz_on_W_K', 'Q3.S_K_small_axiom', 'Q3.A1_density_axiom', 'Q3.node_spacing_axiom', 'Q3.RKHS_contraction_axiom', 'Q3.off_diag_exp_sum_axiom', 'Q3.A3_bridge_uniform', 'Q3.A3_bridge_axiom', 'Q3.c_arch_pos', 'Q3.Weil_criterion', 'Q3.Szego_Rayleigh_lower_bound', 'Q3.T_P_row_sum_bound_axiom', 'Q3.W_sum_finite_axiom', 'Q3.Szego_Bottcher_convergence']
-/

import Mathlib
import Q3.Basic.Defs
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28
import Q3.Proofs.PrimeCert.Brange_Lipschitz_Analytic
import Q3.Proofs.PrimeCert.Brange_Lipschitz_HeatScaffold

/-!
Target: heat-weighted Lipschitz proof on the B-range for t_critical, tau = 0.
This file is intended to close `prime_margin_Lipschitz_on_Brange` using the
heat-weighted numeric certificate from `BrangeHeatCert_2026_01_28.lean`.
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

/-! ### Heat-weighted bounds (assumed inputs)

These are the two numeric inequalities produced by the script:
- arch integral bound
- prime sum bound

They should eventually be certified, but for now they are hypotheses in the
lemmas below so Aristotle can focus on the analytic reduction.
-/

def heat_weight (xi : ℝ) : ℝ :=
  Real.exp (-4 * Real.pi ^ 2 * t_critical * xi ^ 2) * |xi|

lemma arch_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw) :
    |arch_term (phi_shift_critical_tau0 B1) -
      arch_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_arch_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  -- TODO: use phi_shift_lipschitz_B_exp + |∫ f| ≤ ∫ |f| + bound integrand
  sorry

lemma prime_term_Lipschitz_heat
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw) :
    |prime_term (phi_shift_critical_tau0 B1) -
      prime_term (phi_shift_critical_tau0 B2)| ≤
      (prime_cert_L_prime_heat_raw / (B_min ^ 2)) * |B1 - B2| := by
  -- TODO: use phi_shift_lipschitz_B_exp + triangle inequality for tsum
  sorry

lemma margin_Lipschitz_heat_of_bounds
    (B1 B2 : ℝ)
    (hB1 : B1 ∈ Set.Icc B_min prime_cert_B_max)
    (hB2 : B2 ∈ Set.Icc B_min prime_cert_B_max)
    (h_arch_heat :
      ∫ ξ, |a_star ξ| * heat_weight ξ ≤ prime_cert_L_arch_heat_raw)
    (h_prime_heat :
      ∑' n, w_Q n * heat_weight (xi_n n) ≤ prime_cert_L_prime_heat_raw)
    (h_total :
      (prime_cert_L_arch_heat_raw + prime_cert_L_prime_heat_raw) / (B_min ^ 2) ≤
        prime_cert_L_total_heat_ub) :
    |margin_tau0 B1 - margin_tau0 B2| ≤
      prime_cert_L_total_heat_ub * |B1 - B2| := by
  -- TODO: combine the two Lipschitz bounds and apply h_total.
  sorry

end Q3.Proofs.PrimeCert
