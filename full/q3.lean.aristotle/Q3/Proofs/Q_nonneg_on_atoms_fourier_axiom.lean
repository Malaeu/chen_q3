/-
Q3 Core Positivity (Fourier A3 + RKHS)
======================================

This axiom is the Fourier/periodized A3 variant:
  A3_bridge_data_rayleigh_Fourier + RKHS_contraction_data => Q >= 0 on atoms.

It replaces the deprecated sampling/a_star axiom in the main chain.
-/

import Q3.Axioms
import Q3.Proofs.P_A_Toeplitz_bridge
import Q3.Proofs.HeatKernelParams

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3

/-- Core positivity transfer: Fourier A3 bridge + RKHS contraction => Q >= 0 on atoms. -/
axiom Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom :
  ∀ (K : ℝ) (hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K_fixed K Q3.t0_A1, Q3.Q g ≥ 0

/-! ## Theorem wrapper (to be closed) -/

/-- Core positivity transfer: Fourier A3 bridge + RKHS contraction => Q >= 0 on atoms. -/
theorem Q_nonneg_on_atoms_of_A3_Fourier_RKHS :
  ∀ (K : ℝ) (hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K_fixed K Q3.t0_A1, Q3.Q g ≥ 0 := by
  intro K hK hA3 hRKHS g hg
  exact Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom K hK hA3 hRKHS g hg

end Q3
