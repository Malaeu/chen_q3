/-
Q3 Axioms with Tier-2 as Theorems
=================================

This file replaces Tier-2 axioms with proven theorems.
Tier-1 axioms (classical results) remain as axioms.

Usage: Import this instead of Q3.Axioms to get axiom-free Tier-2.
-/

import Q3.Basic.Defs

-- Import all integrated proofs (they import Q3.Axioms internally)
import Q3.Proofs.A1_density_integrated
import Q3.Proofs.A3_bridge_integrated
import Q3.Proofs.Q_Lipschitz_integrated
import Q3.Proofs.Q_nonneg_on_atoms_integrated
import Q3.Proofs.RKHS_contraction_integrated
import Q3.Proofs.S_K_small_integrated
import Q3.Proofs.W_sum_finite_integrated
import Q3.Proofs.node_spacing_integrated
import Q3.Proofs.off_diag_exp_sum_integrated

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Classical Pointwise Matrix.Norms.L2Operator

namespace Q3.Theorems

/-!
# TIER-1: CLASSICAL AXIOMS (remain as axioms)
These are re-exported from Q3.Axioms
-/

-- Tier-1 axioms are already available via Q3.Axioms (imported by _integrated files)
#check Q3.Weil_criterion
#check Q3.explicit_formula
#check Q3.a_star_pos
#check Q3.Szego_Bottcher_eigenvalue_bound
#check Q3.Szego_Bottcher_convergence
#check Q3.Schur_test
#check Q3.c_arch_pos
#check Q3.eigenvalue_le_norm

/-!
# TIER-2: Q3 PAPER CONTRIBUTIONS (now theorems!)
These are proven by Aristotle and close the corresponding axioms.
-/

/-- A1' Density: Fejér×heat atoms dense in W_K (THEOREM) -/
theorem A1_density_WK : ∀ (K : ℝ) (hK : K > 0),
    ∀ Φ ∈ Q3.W_K K, ∀ ε > 0,
      ∃ g ∈ Q3.AtomCone_K K,
        sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε :=
  Q3.Proofs.A1_Density.closes_A1_density_axiom

/-- W_sum finiteness (THEOREM) -/
theorem W_sum_finite : ∀ (K : ℝ) (hK : K > 0), ∃ B, Q3.W_sum_axiom K ≤ B :=
  Q3.Proofs.W_sum.closes_W_sum_axiom

/-- Q is Lipschitz on W_K (THEOREM) -/
theorem Q_Lipschitz : ∀ (K : ℝ) (hK : K > 0),
    ∃ L > 0, ∀ Φ₁ ∈ Q3.W_K K, ∀ Φ₂ ∈ Q3.W_K K,
      |Q3.Q Φ₁ - Q3.Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K} :=
  Q3.Proofs.Q_Lipschitz.closes_Q_Lipschitz_axiom

/-- RKHS contraction (THEOREM) -/
theorem RKHS_contraction : ∀ (K : ℝ) (hK : K ≥ 1),
    ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧ ∀ (Nodes_K : Set ℕ) [Fintype Nodes_K],
      ∀ (T_P : Matrix Nodes_K Nodes_K ℝ), T_P.IsSymm →
      (∀ i j : Nodes_K, T_P i j = Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
        Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t))) →
      ‖T_P‖ ≤ ρ :=
  Q3.Proofs.RKHS_Contraction.closes_RKHS_axiom

/-- S_K small for small t (THEOREM) -/
theorem S_K_small : ∀ (K t η : ℝ), K ≥ 1 → η > 0 → t ≤ Q3.t_min K η → Q3.S_K K t ≤ η :=
  Q3.Proofs.S_K_Small.closes_S_K_small_axiom

/-- Node spacing (THEOREM) -/
theorem node_spacing : ∀ (K : ℝ) (hK : K ≥ 1),
    ∀ (n₁ n₂ : ℕ), n₁ ∈ Q3.Nodes K → n₂ ∈ Q3.Nodes K → n₁ < n₂ →
      Q3.xi_n n₂ - Q3.xi_n n₁ ≥ Q3.delta_K K :=
  Q3.Proofs.NodeSpacing.node_spacing

/-- Off-diagonal exponential sum bound (THEOREM) -/
theorem off_diag_exp_sum : ∀ (K t : ℝ) (hK : K ≥ 1) (ht : t > 0),
    ∀ (Nodes_K : Set ℕ) [Fintype Nodes_K] (i : Nodes_K),
      ∑ j : Nodes_K, (if (j : ℕ) ≠ (i : ℕ) then
        Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t)) else 0) ≤ Q3.S_K K t :=
  Q3.Proofs.OffDiagExpSum.closes_off_diag_axiom

/-- A3 bridge (THEOREM) -/
theorem A3_bridge : ∀ (K : ℝ) (hK : K ≥ 1),
    ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
      ∀ (v : Fin M → ℝ), v ≠ 0 →
      (∑ i, ∑ j, v i * v j * (Q3.ToeplitzMatrix M Q3.a_star i j -
        Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
        Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t)))) /
      (∑ i, v i ^ 2) ≥ Q3.c_arch K / 4 :=
  Q3.Proofs.A3_Bridge.closes_A3_bridge_axiom

/-- Q ≥ 0 on atoms (THEOREM) -/
theorem Q_nonneg_on_atoms : ∀ (K : ℝ) (hK : K ≥ 1),
    Q3.A3_bridge_data K → Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 :=
  Q3.Proofs.Q_Nonneg.closes_Q_nonneg_axiom

end Q3.Theorems

/-!
# Summary

Tier-1 axioms (8): Remain as axioms in Q3.Axioms
- Weil_criterion, explicit_formula, a_star_pos
- Szego_Bottcher_*, Schur_test, c_arch_pos, eigenvalue_le_norm

Tier-2 theorems (9): Now proven!
- A1_density_WK, W_sum_finite, Q_Lipschitz
- RKHS_contraction, S_K_small, node_spacing
- off_diag_exp_sum, A3_bridge, Q_nonneg_on_atoms
-/
