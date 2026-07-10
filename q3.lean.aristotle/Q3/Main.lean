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

Important: this is the current compiled broad-cone route, not the frozen public
RH contract after the 2026-03-07 target-cone audit. It is retained because the
scalar layer still carries reusable local lemmas, but the public manuscript has
pivoted to a corrected positive-definite target cone.

Fatal square-class audit note (2026-06-25): this file still records the legacy
broad-cone wrapper through `Weil_cone`/`Weil_criterion`.  It is not the corrected
Weil-square RH export route; the new interface starts at
`Q3.Basic.WeilSquareClass`.
-/

import Q3.Proofs.PaperMainlineAtomRoute

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Main

/-- Current top-level broad-cone positivity export.

This export reflects the active compiled route and its live axiom profile; it
should not be read as the frozen public RH contract after the target-cone audit
or after the 2026-06-25 Weil-square audit. -/
theorem Q_nonneg_on_Weil_cone :
    ∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0 :=
  Q3.Q_nonneg_on_Weil_cone_current_atom_route

/-- Current top-level RH wrapper for the compiled broad-cone route.

Its present meaning is structural: it records the active route and axiom profile
used by `Q3.Main`, while the scalar closure gate is still unresolved and the
public target cone has already been narrowed in the paper/control-doc layer.
This wrapper must not be used as the corrected Weil-square RH export. -/
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
