/-
Q Nonneg on Atoms - Integrated with Q3 Definitions
===================================================

Original: Aristotle proof (Q3/Proofs/Q_nonneg_on_atoms.lean)
This version: Uses Q3.Axioms definitions directly.

WRAPS: Q_nonneg_on_atoms_of_A3_RKHS_axiom

This module provides compatibility wrappers only. It does not derive the
nonnegativity statement independently.
-/

import Q3.Axioms

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators Real Nat Classical Pointwise Matrix.Norms.L2Operator
open MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

namespace Q3.Proofs.Q_Nonneg

/-! ## Key Lemmas -/

/-- Explicit consumption of the quarantined legacy compact-infimum assumption. -/
lemma rawKernelCompactInfPos_ofLegacyAssumption
    (K : ℝ) (hK : K ≥ 1) : Q3.c_arch K > 0 :=
  Q3.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption K (by linarith)

/-! ## Main Theorem -/

/-- Direct compatibility wrapper around the project assumption
`Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom`. -/
theorem Q_nonneg_on_atoms (K : ℝ) (hK : K ≥ 1) :
    Q3.A3_bridge_data K → Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 :=
  Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom K hK

/-! ## Legacy compatibility name -/

/-- Compatibility wrapper; this does not close or replace its source
assumption. -/
theorem Q_nonneg_on_atoms_legacyCompatibility (K : ℝ) (hK : K ≥ 1) :
    Q3.A3_bridge_data K → Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 :=
  Q_nonneg_on_atoms K hK

end Q3.Proofs.Q_Nonneg

/-!
## Honest status

Both exported theorems above are direct wrappers around
`Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom`. This module supplies no independent
proof of atom-cone nonnegativity and closes no project assumption.
-/
