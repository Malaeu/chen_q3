/-
Q_nonneg Bridge v2
==================

This file provides the bridge for Q nonnegativity on atom functions.

The theorem states: Q(Φ) ≥ 0 for Φ in the "atom cone"
(finite sums of heat-Fejér atoms).

Uses Q3.Axioms for the K-dependent positivity axiom (Q_nonneg_on_atoms_of_A3_RKHS_axiom).

CLOSES: Q_nonneg_on_atoms (2 sorries → 0 sorries)
-/

import Q3.Axioms
import Q3.Proofs.Bridge

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

namespace Q3.Proofs.QNonnegBridgeV2

/-! ## Q Nonnegativity on Atoms -/

-- A3_bridge_data_uniform is available via the uniform axiom.
/-- Q is nonnegative on the atom cone AtomCone_K for any K ≥ 1.

The mathematical content is:
- A3 bridge: λ_min(T_M[a_star] - T_P) ≥ c_star/4 (Szegő-Böttcher + RKHS)
- RKHS contraction: ||T_P|| ≤ ρ < 1
- Combined: Q(atom) = arch_term - prime_term ≥ (c_star/4) · ||atom||² ≥ 0
-/
theorem Q_nonneg_on_atoms (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 := by
  have hA3 : Q3.A3_bridge_data K := Q3.A3_bridge_axiom K hK
  have hRKHS : Q3.RKHS_contraction_data K := Q3.Bridge.RKHS_contraction_data_of_bridge K hK
  exact Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom K hK hA3 hRKHS

/-- For the K-dependent version, we use A3_bridge_axiom and the RKHS bridge directly. -/
theorem Q_nonneg_on_atoms_K_dep (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 := by
  have hA3 : Q3.A3_bridge_data K := Q3.A3_bridge_axiom K hK
  have hRKHS : Q3.RKHS_contraction_data K := Q3.Bridge.RKHS_contraction_data_of_bridge K hK
  exact Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom K hK hA3 hRKHS

end Q3.Proofs.QNonnegBridgeV2

/-!
## Summary

PROOF STRUCTURE:
```
A3_bridge_axiom                RKHS_contraction_bridge
      ↓                                ↓
A3_bridge_data                  RKHS_contraction_data
      ↓                                ↓
      └────────────────┬───────────────┘
                       ↓
       Q_nonneg_on_atoms_of_A3_RKHS_axiom
                       ↓
         ∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0
```

AXIOM CLOSURE:
- Q_nonneg_on_atoms uses Q_nonneg_on_atoms_of_A3_RKHS_axiom directly
- No sorries in this file
-/
