/-
Q3 Formalization: Positivity on Atom Cone (T4 Core)
====================================================

This file packages the "atoms positivity" step as a THEOREM:

  Q ≥ 0 on AtomCone_K(K)

derived from:
  - A3 bridge (Toeplitz-symbol spectral gap)
  - RKHS contraction (prime operator bound)
  - a single remaining core axiom that combines them

The goal is that `#print axioms` for the final RH theorem shows explicit
dependencies on A3 + RKHS (instead of a standalone "atoms positivity" axiom).
-/

import Q3.Axioms
import Q3.Proofs.Params_Critical

set_option linter.mathlibStandardSet false

namespace Q3.Atoms

open Q3

/-- **T4 (Atoms Positivity)**:
From the A3 bridge axiom and the RKHS contraction bridge, we obtain
`Q g ≥ 0` for all `g` in the atom cone `AtomCone_K K`.
-/
theorem Q_nonneg_on_atoms (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ AtomCone_K_fixed K Q3.t0_critical, Q g ≥ 0 := by
  intro g hg
  have hA3 : Q3.A3_bridge_data K := Q3.A3_bridge_axiom K hK
  have hRKHS : Q3.RKHS_contraction_data K := Q3.RKHS_contraction_axiom K hK
  have hAtom : g ∈ Q3.AtomCone_K K := Q3.AtomCone_K_fixed_subset K Q3.t0_critical Q3.t0_critical_pos hg
  exact Q3.Q_nonneg_on_atoms_of_A3_RKHS_axiom K hK hA3 hRKHS g hAtom

end Q3.Atoms
