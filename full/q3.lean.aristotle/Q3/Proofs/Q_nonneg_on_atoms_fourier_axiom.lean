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
import Q3.Proofs.Params_Critical
import Q3.Proofs.Rayleigh_basis0_of_A3

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3

/-! ## A4 hook: Rayleigh lower bound at basis0 from Fourier A3 -/

abbrev rayleigh_basis0_of_A3_for_chain :=
  Q3.Proofs.QNonnegAtoms.rayleigh_basis0_of_A3

/-- Core positivity transfer: Fourier A3 bridge + RKHS contraction => Q >= 0 on atoms. -/
-- TODO(one-scale): replace A3_bridge_data_rayleigh_Fourier with the one-scale bridge at t_critical
-- once the A3 floor + weight-sum cap are proven at the same t.
axiom Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom :
  ∀ (K : ℝ) (hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K_fixed K Q3.t0_critical, Q3.Q g ≥ 0

/-! ## Theorem wrapper (to be closed) -/

/-- Core positivity transfer: Fourier A3 bridge + RKHS contraction => Q >= 0 on atoms. -/
theorem Q_nonneg_on_atoms_of_A3_Fourier_RKHS :
  ∀ (K : ℝ) (hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K_fixed K Q3.t0_critical, Q3.Q g ≥ 0 := by
  intro K hK hA3 hRKHS g hg
  exact Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom K hK hA3 hRKHS g hg

/-! ## Guarded corollary: τ = 0 (BaseAtomCone_K) -/

theorem Q_nonneg_on_base_atoms_of_A3_Fourier_RKHS :
  ∀ (K : ℝ) (hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.BaseAtomCone_K K Q3.t0_critical, Q3.Q g ≥ 0 := by
  intro K hK hA3 hRKHS g hg
  have hsubset := Q3.BaseAtomCone_K_subset_AtomCone_K_fixed K Q3.t0_critical
  exact Q_nonneg_on_atoms_of_A3_Fourier_RKHS K hK hA3 hRKHS g (hsubset hg)

end Q3
