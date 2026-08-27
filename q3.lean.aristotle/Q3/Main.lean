/- 
Deprecated compatibility surface for the compiled broad-cone route
====================================================================

The retained implementation follows the shifted-atom broad-cone route:

1. `Q_Fejer_heat_atom_nonneg_t_critical`
2. `Q_nonneg_on_WK_tcritical_current_atom_route`
3. `Q_nonneg_on_Weil_cone_current_atom_route`
4. `Weil_criterion`

Legacy `τ = 0` developments remain elsewhere in the tree for comparison and
compatibility, but they are not the active public route.

Important: this module is an explicitly imported compatibility surface, not the
default `Q3` export and not the corrected public RH contract after the
2026-03-07 target-cone audit.

Fatal square-class audit note (2026-06-25): this file still records the legacy
broad-cone wrapper through `Weil_cone`/`Weil_criterion`.  It is not the corrected
Weil-square RH export route; the new interface starts at
`Q3.Basic.WeilSquareClass`.
-/

import Q3.Proofs.PaperMainlineAtomRoute

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.Main

/-- Deprecated compatibility broad-cone positivity wrapper.

This wrapper preserves the legacy statement and dependency profile; it is not part
of the default `Q3` export. -/
@[deprecated
  Q3.Conditional.LegacyBroadCone.Q_nonneg_on_broadWeilCone_of_primeTermAxiom
  (since := "2026-08-27")]
theorem Q_nonneg_on_Weil_cone :
    ∀ Φ ∈ Q3.Weil_cone, Q3.Q Φ ≥ 0 :=
  Q3.Conditional.LegacyBroadCone.Q_nonneg_on_broadWeilCone_of_primeTermAxiom

/-- Deprecated compatibility RH wrapper for the compiled broad-cone route.

It records the retained route and dependency profile only.  It must not be used as
the corrected Weil-square RH export. -/
@[deprecated Q3.Conditional.LegacyBroadCone.RH_of_legacyBroadConeAxioms
  (since := "2026-08-27")]
theorem RH_of_Weil_and_Q3 : Q3.RH :=
  Q3.Conditional.LegacyBroadCone.RH_of_legacyBroadConeAxioms

-- Check what axioms the proof depends on.
#check RH_of_Weil_and_Q3
-- Axiom dependencies (run `#print axioms RH_of_Weil_and_Q3`):
-- Standard: propext, Classical.choice, Quot.sound
-- Tier-1: Q3.Weil_criterion
-- Tier-2 in main theorem: `Q3.prime_term_le_at_t_critical_axiom`

end Q3.Main

end
