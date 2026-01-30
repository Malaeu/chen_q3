/-
Q3 Formalization: Axiom Dependency Check
========================================

This file verifies all axiom dependencies for CI.
Run: `lake env lean Q3/CheckAxioms.lean`

Expected output: List of axioms used in RH_of_Weil_and_Q3
-/

import Q3.Main
import Q3.Proofs.Q_nonneg_t_critical
import Q3.Proofs.PrimeCert.Brange_2046
import Q3.Proofs.PrimeCert.BrangeCert_2046

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

/-! ## Verify Tier-2 axioms exist (τ=0 mainline) -/
-- PrimeCert (grid/heat bounds data + Lipschitz on B-range)
#check Q3.Proofs.PrimeCert.prime_b_grid_bounds_data
#check Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data
#check Q3.Proofs.PrimeCert.prime_heat_sum_data
#check Q3.Proofs.PrimeCert.prime_heat_bounds_data
#check Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange

-- Theorem (derived from grid bounds)
#check Q3.Proofs.PrimeCert.prime_b_grid_bounds_cert
#check Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin

/-! ## Off-chain (τ ≠ 0) placeholder -/
-- Present in Q_nonneg_t_critical, but not used by the τ=0 main chain
#check Q3.prime_term_le_at_t_critical_axiom

/-! ## Verify T5 (τ=0) is a THEOREM -/
#check Q3.T5.T5_transfer

/-! ## Print Axiom Dependencies -/

-- This is the authoritative dependency list for the full RH theorem.
#print axioms Q3.Main.RH_of_Weil_and_Q3

/-!
## Expected Dependencies

### Standard Mathlib Axioms (always present):
- `propext` : Propositional extensionality
- `Classical.choice` : Classical choice principle
- `Quot.sound` : Quotient soundness

### Tier-1 Classical Axioms:
- `Q3.Weil_criterion` : Weil (1952)

### Tier-2 Q3 Paper Axioms (τ=0 mainline):
- `Q3.Proofs.PrimeCert.prime_b_grid_bounds_data` : grid arch/prime bounds
- `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data` : heat-weighted arch bound
- `Q3.Proofs.PrimeCert.prime_heat_sum_data` : heat-weighted prime partial+tail data
- `Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange` : Lipschitz control on B-range

### THEOREM (not axiom!):
- `Q3.T5.T5_transfer` : Q ≥ 0 on W_K

## Verification

Run `lake env lean Q3/Main.lean` to see:
```
Q3.Main.RH_of_Weil_and_Q3 : RH
```

Keep this file aligned with the live chain; it is the CI gate for axiom drift.
-/
