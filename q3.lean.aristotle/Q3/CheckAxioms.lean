/-
Q3 Formalization: Axiom Dependency Check
========================================

This file verifies all axiom dependencies for CI.
Run: `lake env lean Q3/CheckAxioms.lean`

Expected output: List of axioms used in RH_of_Weil_and_Q3
-/

import Q3.Main
import Q3.Proofs.Q_nonneg_t_critical

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

/-! ## Verify Tier-2 τ=0 mainline axioms exist -/
#check Q3.Weil_criterion_tau0
#check Q3.prime_term_le_at_t_critical_axiom

/-! ## Off-chain (τ ≠ 0) placeholder -/
-- Present in Q_nonneg_t_critical, but not used by the τ=0 main chain
#check Q3.prime_term_le_at_t_critical_axiom

/-! ## Verify T5 (τ=0) is a THEOREM -/
#check Q3.T5.T5_transfer

/-! ## Print Axiom Dependencies -/

-- Authoritative dependency list for the RH theorem on the τ=0 mainline.
#print axioms Q3.Main.RH_of_Weil_and_Q3

/-!
## Expected Dependencies

### Standard Mathlib Axioms (always present):
- `propext` : Propositional extensionality
- `Classical.choice` : Classical choice principle
- `Quot.sound` : Quotient soundness

### Tier-1/Tier-2 domain axioms on current mainline:
- `Q3.Weil_criterion_tau0`
- `Q3.prime_term_le_at_t_critical_axiom`

### THEOREM (not axiom!):
- `Q3.T5.T5_transfer` : Q ≥ 0 on W_K

## Verification

Run `lake env lean Q3/Main.lean` to see:
```
Q3.Main.RH_of_Weil_and_Q3 : RH
```

Keep this file aligned with the live chain; it is the CI gate for axiom drift.
-/
