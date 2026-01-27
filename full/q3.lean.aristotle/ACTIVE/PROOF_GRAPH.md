# Proof Graph (auto) — 2026-01-27 00:30 UTC

**Purpose:** Machine + human index of the main-chain proof nodes, with alternatives.
**Sources:** `ACTIVE/DEPS_TREE_MAIN.json` + `ACTIVE/ALTERNATIVE_PATHS.json`

## propext
- Status: `classical`

## Classical.choice
- Status: `classical`

## Q3.Schur_test
- Status: `classical`
- File: `Q3/Axioms.lean`
- Axioms in file: 24
  - Weil_criterion@L51, explicit_formula@L60, Szego_Bottcher_eigenvalue_bound@L180, Szego_Bottcher_convergence@L186, Szego_Rayleigh_lower_bound@L212, Schur_test@L224, c_arch_pos@L242, c_star_le_c_arch@L279, eigenvalue_le_norm@L290, Weil_criterion_tau0@L407, A1_density_WK_axiom@L427, A1_density_axiom@L440, W_sum_finite_axiom@L461, Q_Lipschitz_on_W_K@L471, RKHS_contraction_axiom@L483, T_P_row_sum_bound_axiom@L499, S_K_small_axiom@L513, node_spacing_axiom@L524, off_diag_exp_sum_axiom@L536, A3_bridge_axiom@L551, A3_bridge_uniform@L569, A3_bridge_rayleigh_axiom@L582, Q_nonneg_on_atoms_of_A3_RKHS_axiom@L653, Q_nonneg_on_atoms_uniform@L665

## Q3.Weil_criterion
- Status: `classical`
- File: `Q3/Axioms.lean`
- Axioms in file: 24
  - Weil_criterion@L51, explicit_formula@L60, Szego_Bottcher_eigenvalue_bound@L180, Szego_Bottcher_convergence@L186, Szego_Rayleigh_lower_bound@L212, Schur_test@L224, c_arch_pos@L242, c_star_le_c_arch@L279, eigenvalue_le_norm@L290, Weil_criterion_tau0@L407, A1_density_WK_axiom@L427, A1_density_axiom@L440, W_sum_finite_axiom@L461, Q_Lipschitz_on_W_K@L471, RKHS_contraction_axiom@L483, T_P_row_sum_bound_axiom@L499, S_K_small_axiom@L513, node_spacing_axiom@L524, off_diag_exp_sum_axiom@L536, A3_bridge_axiom@L551, A3_bridge_uniform@L569, A3_bridge_rayleigh_axiom@L582, Q_nonneg_on_atoms_of_A3_RKHS_axiom@L653, Q_nonneg_on_atoms_uniform@L665

## Q3.prime_cert_margin_on_Brange_axiom
- Status: `axiom`
- File: `Q3/Proofs/PrimeCert/BrangeCert_2046.lean`
- Axioms in file: 2
  - prime_b_grid_val_le_margin@L19, prime_margin_Lipschitz_on_Brange@L25
- Alternatives:
  - Grid + Lipschitz certificate (numeric) (active)
  - Analytic bound via RKHS cap + Toeplitz floor (idea)

## Q3.prime_term_le_at_t_critical_axiom
- Status: `axiom`
- File: `Q3/Proofs/Q_nonneg_t_critical.lean`
- Axioms in file: 1
  - prime_term_le_at_t_critical_axiom@L366
- Alternatives:
  - Split: B in [B_min, B_max] via margin + outside via generic axiom (active)
  - Direct numeric certificate at t_critical (idea)

## Quot.sound
- Status: `classical`

