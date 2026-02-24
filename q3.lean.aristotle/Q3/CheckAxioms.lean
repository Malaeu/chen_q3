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

/-! ## Verify Tier-2 interfaces exist (τ=0 mainline) -/
#check Q3.PrimeCertMarginOnBrange

/-! ## Off-chain (τ ≠ 0) placeholder -/
-- Present in Q_nonneg_t_critical, but not used by the τ=0 main chain
#check Q3.prime_term_le_at_t_critical_axiom

/-! ## Verify T5 (τ=0) is a THEOREM -/
#check Q3.T5.T5_transfer

/-! ## Print Axiom Dependencies -/

-- Authoritative dependency list for the RH mainline.
-- `scripts/kb_refresh.py` parses the first `depends on axioms` block.
#print axioms Q3.Main.RH_of_Weil_and_Q3

-- Forward-compatible route: replaces τ=0 criterion axiom with an explicit
-- quantitative bridge hypothesis (`Tau0QApproxBridge`).
#print axioms Q3.Main.RH_of_Weil_and_Q3_via_qapprox

-- Same route, but with compact-approximation contracts on `W_K`.
#print axioms Q3.Main.RH_of_Weil_and_Q3_via_compact_approx

-- Amplifier route sanity check: should not depend on `Weil_criterion_tau0`.
#print axioms Q3.Proofs.WeilCoreTau0.criterion_via_axiomatic_amplifier

-- Auxiliary single-scale prime gate (off mainline while `h_margin_cert` is explicit).
#print axioms Q3.prime_term_le_at_t_critical_axiom

/-!
## Expected Dependencies

### Standard Mathlib Axioms (always present):
- `propext` : Propositional extensionality
- `Classical.choice` : Classical choice principle
- `Quot.sound` : Quotient soundness

### Tier-1 Classical Axioms:
- `Q3.Weil_criterion` : Weil (1952)

### Tier-2 interface (τ=0 mainline):
- `Q3.PrimeCertMarginOnBrange` is an explicit theorem hypothesis in `Q3.Main.RH_of_Weil_and_Q3`.
- `Q3.prime_term_le_at_t_critical_axiom` is tracked separately as the off-mainline prime gate.

### THEOREM (not axiom!):
- `Q3.T5.T5_transfer` : Q ≥ 0 on W_K

## Verification

Run `lake env lean Q3/Main.lean` to see:
```
Q3.Main.RH_of_Weil_and_Q3 : RH
```

Keep this file aligned with the live chain; it is the CI gate for axiom drift.
-/
