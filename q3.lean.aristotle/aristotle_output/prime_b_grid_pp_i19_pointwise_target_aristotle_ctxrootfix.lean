/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: b85dd49d-ecbc-4cc3-9e1b-0e7970963e39

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Aristotle encountered an error while processing imports for this file.
Details:
Axioms were added during init_sorries: ['Q3.Szego_Bottcher_eigenvalue_bound', 'Q3.explicit_formula', 'Q3.eigenvalue_le_norm', 'Q3.A3_bridge_rayleigh_axiom', 'Q3.Q_nonneg_on_atoms_uniform', 'Q3.Weil_criterion_tau0', 'Q3.c_star_le_c_arch', 'Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom', 'Q3.a_star_linear_growth', 'Q3.A1_density_WK_axiom', 'Q3.Schur_test', 'Q3.Q_Lipschitz_on_W_K', 'Q3.S_K_small_axiom', 'Q3.A1_density_axiom', 'Q3.node_spacing_axiom', 'Q3.w_Q_heat_weight_summable', 'Q3.RKHS_contraction_axiom', 'Q3.off_diag_exp_sum_axiom', 'Q3.A3_bridge_uniform', 'Q3.A3_bridge_axiom', 'Q3.c_arch_pos', 'Q3.Weil_criterion', 'Q3.Szego_Rayleigh_lower_bound', 'Q3.T_P_row_sum_bound_axiom', 'Q3.W_sum_finite_axiom', 'Q3.Szego_Bottcher_convergence']
-/

import Mathlib
import Q3.Proofs.PrimeCert.BrangeGrid_PrimeSum_2026_01_30_PrimePow_i19_PPCover

noncomputable section

namespace Q3.Proofs.PrimeCert

/--
Pointwise prime-power term bound needed to close the i=19 pp-cover chain.
Targeted Aristotle request: no extra goals, no unrelated sorries.
-/
theorem prime_b_grid_weight_term_le_pp_i19_all_ub_target :
    ∀ n : ℕ, IsPrimePow n → n ≤ prime_cert_N →
      prime_b_grid_weight_term prime_b_grid_i19 n ≤ prime_b_grid_pp_i19_all_ub n := by
  sorry

end Q3.Proofs.PrimeCert
