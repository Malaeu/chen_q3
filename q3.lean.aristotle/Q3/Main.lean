/- 
Q3 Formalization: current top-level route to RH
==============================================

The current main entry follows the shifted-atom paper route:

1. `Q_Fejer_heat_atom_nonneg_t_critical`
2. `Q_nonneg_on_WK_tcritical_current_atom_route`
3. `Q_nonneg_on_Weil_cone_current_atom_route`
4. `Weil_criterion`

Legacy `τ = 0` developments remain elsewhere in the tree for comparison and
compatibility, but they are no longer the active top-level route.

Important: this is the current compiled route, not yet an honest fully closed
proof object, because the scalar layer still inherits
`Q3.prime_term_le_at_t_critical_axiom`.
-/

import Q3.Proofs.PaperMainlineAtomRoute

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Main

/-- Current top-level positivity theorem on the full Weil cone.

This export reflects the active compiled route and its live axiom profile; it
should not be read as saying that every closure gate `G0..G6` is already closed
mathematically. -/
theorem Q_nonneg_on_Weil_cone :
    ∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0 :=
  Q3.Q_nonneg_on_Weil_cone_current_atom_route

/-- Current top-level RH theorem for the project.

Its present meaning is structural: it records the active route and axiom profile
used by `Q3.Main`, while the scalar closure gate is still unresolved. -/
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
