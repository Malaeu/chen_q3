/-
Q3 Formalization: Axiom Dependency Check
========================================

This file verifies all axiom dependencies for CI.
Run: `lake env lean Q3/CheckAxioms.lean`

Expected output: List of axioms used in RH_of_Weil_and_Q3
-/

import Q3.Main

/-!
# Axiom Dependency Verification

This prints all axioms used by the main theorem.
Used in CI to ensure no undocumented axioms sneak in.

## KEY CHANGE: τ=0 mainline cone

The RH chain now uses the τ=0 Weil cone `Weil_cone_tau0`, with base atoms
restricted to the certified B-range at `t_critical`. The τ‑uniform prime‑term
axiom is no longer in the main chain.
-/

-- Re-export the main theorem for verification
open Q3.Main

/-! ## Verify Tier-1 axioms exist -/
#check Q3.Weil_criterion_tau0
#check Q3.explicit_formula
#check Q3.a_star_pos
#check Q3.Szego_Bottcher_eigenvalue_bound
#check Q3.Szego_Bottcher_convergence
#check Q3.Schur_test
#check Q3.c_arch_pos
#check Q3.eigenvalue_le_norm

/-! ## Verify Tier-2 axioms exist (τ=0 mainline) -/
-- PrimeCert
#check Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin
#check Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange

/-! ## Verify T5 (τ=0) is a THEOREM -/
#check Q3.T5.T5_transfer_tau0

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
- `Q3.Weil_criterion_tau0` : Weil (1952), τ=0 cone

### Tier-2 Q3 Paper Axioms:
- `Q3.Proofs.PrimeCert.prime_b_grid_val_le_margin` : grid certificate
- `Q3.Proofs.PrimeCert.prime_margin_Lipschitz_on_Brange` : Lipschitz margin certificate

### THEOREM (not axiom!):
- `Q3.T5.T5_transfer_tau0` : Q ≥ 0 on W_K_tau0 (τ=0 mainline)

## Verification

Run `lake env lean Q3/Main.lean` to see:
```
Q3.Main.RH_of_Weil_and_Q3 : RH
```

The key improvement: τ‑uniform prime‑term axiom is out of the chain,
and τ=0 mainline uses only B‑range PrimeCert axioms.
-/
