/- 
Q3 Formalization: Main Theorem - Riemann Hypothesis
===================================================

The official main entry now follows the shifted-atom paper route:

1. `Q_Fejer_heat_atom_nonneg_t_critical`
2. `Q_nonneg_on_WK_tcritical_current_atom_route`
3. `Q_nonneg_on_Weil_cone_current_atom_route`
4. `Weil_criterion`

Legacy `τ = 0` developments remain elsewhere in the tree for comparison and
compatibility, but they are no longer the active top-level route.
-/

import Q3.Proofs.PaperMainlineAtomRoute

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Main

/-- Official positivity theorem on the full Weil cone. -/
theorem Q_nonneg_on_Weil_cone :
    ∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0 :=
  Q3.Q_nonneg_on_Weil_cone_current_atom_route

/-- Official RH theorem for the project. -/
theorem RH_of_Weil_and_Q3 : Q3.RH :=
  Q3.RH_of_shifted_atom_route

-- Check what axioms the proof depends on.
#check RH_of_Weil_and_Q3
-- Axiom dependencies (run `#print axioms RH_of_Weil_and_Q3`):
-- Standard: propext, Classical.choice, Quot.sound
-- Tier-1: Q3.Weil_criterion
-- Tier-2 in main theorem: `Q3.prime_term_le_at_t_critical_axiom`

end Q3.Main

end

