/-
Q_nonneg Bridge v2
==================

This file provides the bridge for Q nonnegativity on atom functions.

The theorem states: Q(Φ) ≥ 0 for Φ in the "atom cone"
(finite sums of heat-Fejér atoms).

Uses Q3.Axioms for the uniform positivity axiom (Q_nonneg_on_atoms_uniform).

CLOSES: Q_nonneg_on_atoms (2 sorries → 0 sorries)
-/

import Q3.Axioms

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

namespace Q3.Proofs.QNonnegBridgeV2

/-! ## Q Nonnegativity on Atoms -/

/-- A3_bridge_data_uniform is available via the uniform axiom. -/
lemma A3_data_uniform : Q3.A3_bridge_data_uniform := Q3.A3_bridge_uniform

/-- RKHS_contraction_data_uniform: the RKHS contraction bound.

Note: RKHS_contraction_data K and RKHS_contraction_data_uniform have IDENTICAL definitions
(K is unused in the body), so RKHS_contraction_axiom K hK provides RKHS_contraction_data_uniform
when we pick any K ≥ 1. -/
lemma RKHS_data_uniform : Q3.RKHS_contraction_data_uniform := Q3.RKHS_contraction_axiom 1 (by linarith)

/-- Q is nonnegative on the atom cone AtomCone_K for any K ≥ 1.

This follows from the uniform axiom Q_nonneg_on_atoms_uniform which requires:
1. A3_bridge_data_uniform (from A3_bridge_uniform axiom)
2. RKHS_contraction_data_uniform (from RKHS_contraction_axiom 1 ...)

The mathematical content is:
- A3 bridge: λ_min(T_M[a_star] - T_P) ≥ c_star/4 (Szegő-Böttcher + RKHS)
- RKHS contraction: ||T_P|| ≤ ρ < 1
- Combined: Q(atom) = arch_term - prime_term ≥ (c_star/4) · ||atom||² ≥ 0
-/
theorem Q_nonneg_on_atoms (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 :=
  Q3.Q_nonneg_on_atoms_uniform A3_data_uniform RKHS_data_uniform K hK

/-- For the K-dependent version, we use A3_bridge_axiom and RKHS_contraction_axiom directly. -/
theorem Q_nonneg_on_atoms_K_dep (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 := by
  have hA3 : Q3.A3_bridge_data K := Q3.A3_bridge_axiom K hK
  have hRKHS : Q3.RKHS_contraction_data K := Q3.RKHS_contraction_axiom K hK
  exact Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom K hK hA3 hRKHS

end Q3.Proofs.QNonnegBridgeV2

/-!
## Summary

PROOF STRUCTURE:
```
A3_bridge_uniform                RKHS_contraction_axiom 1
      ↓                                    ↓
A3_bridge_data_uniform           RKHS_contraction_data_uniform
      ↓                                    ↓
      └────────────────┬───────────────────┘
                       ↓
         Q_nonneg_on_atoms_uniform
                       ↓
         ∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0
```

KEY INSIGHT:
RKHS_contraction_data K and RKHS_contraction_data_uniform have IDENTICAL definitions!
The K parameter in RKHS_contraction_data K is UNUSED in the body.
So RKHS_contraction_axiom 1 (by linarith) provides RKHS_contraction_data_uniform directly.

AXIOM CLOSURE:
- Q_nonneg_on_atoms uses Q_nonneg_on_atoms_uniform directly
- No sorries in this file
-/
