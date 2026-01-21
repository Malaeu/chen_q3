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
import Q3.Proofs.Bridge
import Q3.Proofs.P_A_Toeplitz_bridge
import Q3.Proofs.Q_nonneg_on_atoms_fourier_axiom

set_option linter.mathlibStandardSet false

namespace Q3.Atoms

open Q3

/-! ## Bundling A3 + RKHS into Atom Positivity -/

/-! ## Bundling A3 + RKHS into Atom Positivity (Fourier variant) -/

/-- A3 bridge data for `K` (Fourier Toeplitz with P_A). -/
abbrev A3_bridge_data := Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier

/-- RKHS contraction data for `K` (just re-exported from `Q3.Axioms`). -/
abbrev RKHS_contraction_data := Q3.RKHS_contraction_data

/-- **T4 (Atoms Positivity)**:
From the A3 bridge axiom and the RKHS contraction bridge, we obtain
`Q g ≥ 0` for all `g` in the atom cone `AtomCone_K K`.
-/
theorem Q_nonneg_on_atoms (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ AtomCone_K K, Q g ≥ 0 := by
  -- Build Fourier A3 bridge data from the weight-sum cap.
  have hKpos : 0 < K := by nlinarith [hK]
  have hA3 : A3_bridge_data K := by
    refine Q3.Proofs.P_A_Bridge.A3_bridge_rayleigh_from_weight_sum_P_A K ?_
    intro _inst
    exact Q3.Proofs.weight_sum_le_rho_one K K hKpos
  have hRKHS : RKHS_contraction_data K := Q3.Bridge.RKHS_contraction_data_of_bridge K hK
  -- Apply the Fourier A3 + RKHS positivity axiom.
  exact Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom K hK hA3 hRKHS

end Q3.Atoms
