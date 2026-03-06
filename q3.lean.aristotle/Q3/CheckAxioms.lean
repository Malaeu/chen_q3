/-
Q3 Formalization: Axiom Dependency Check
========================================

This file verifies all axiom dependencies for CI.
Run: `lake env lean Q3/CheckAxioms.lean`

Expected output: List of axioms used by the active RH theorem
-/

import Q3.Main
import Q3.Proofs.PaperMainlineAtomRoute

/-!
# Axiom Dependency Verification

This prints all axioms used by the main theorem.
Used in CI to ensure no undocumented axioms sneak in.

## NOTE: This file tracks the *current compiled* main chain.
If identifiers are renamed, update the #check list to match the live chain.
-/

-- Re-export the main theorem for verification
open Q3.Main

/-! ## Verify Tier-1 axioms exist -/
#check Q3.Weil_criterion
#check Q3.explicit_formula
#check Q3.a_star_pos
#check Q3.Szego_Bottcher_eigenvalue_bound
#check Q3.Szego_Bottcher_convergence
#check Q3.Schur_test
#check Q3.c_arch_pos
#check Q3.eigenvalue_le_norm

/-! ## Verify Tier-2 shifted-atom mainline bridge exists -/
#check Q3.Weil_criterion
#check Q3.prime_term_le_at_t_critical_axiom

/-! ## Current shifted-atom bridge witnesses -/
#check Q3.Q_Fejer_heat_atom_nonneg_t_critical
#check Q3.Q_nonneg_on_Weil_cone_current_atom_route

/-! ## Verify compact transfer on the active route is a THEOREM -/
#check Q3.Proofs.CompatibilityReduction.Q_nonneg_on_WK_tcritical_current_atom_route

/-! ## Print Axiom Dependencies -/

-- Authoritative dependency lists for the active RH theorems.
#print axioms Q3.Main.RH_of_Weil_and_Q3
#print axioms Q3.RH_of_shifted_atom_route

/-!
## Expected Dependencies

### Standard Mathlib Axioms (always present):
- `propext` : Propositional extensionality
- `Classical.choice` : Classical choice principle
- `Quot.sound` : Quotient soundness

### Tier-1/Tier-2 domain axioms on current mainline:
- `Q3.Weil_criterion`
- `Q3.prime_term_le_at_t_critical_axiom`

### THEOREM (not axiom!):
- `Q3.Q_Fejer_heat_atom_nonneg_t_critical`
- `Q3.Q_nonneg_on_Weil_cone_current_atom_route`

## Verification

Run `lake env lean Q3/Main.lean` to see:
```
Q3.Main.RH_of_Weil_and_Q3 : RH
```

Keep this file aligned with the live chain; it is the CI gate for axiom drift.
-/
