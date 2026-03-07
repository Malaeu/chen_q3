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
import Q3.Proofs.Q_nonneg_atoms_closure
import Q3.Proofs.Q_nonneg_t_critical_tau0_bridge
import Q3.Proofs.W_Sum_Finite_Bridge

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3

/-! ## A4 hook: Rayleigh lower bound at basis0 from Fourier A3 -/

abbrev rayleigh_basis0_of_A3_for_chain :=
  Q3.Proofs.QNonnegAtoms.rayleigh_basis0_of_A3

/-- Core positivity transfer: Fourier A3 bridge + RKHS contraction => Q >= 0 on atoms. -/
-- TODO(one-scale): replace A3_bridge_data_rayleigh_Fourier with the one-scale bridge at t_critical
-- once the A3 floor + weight-sum cap are proven at the same t.
theorem Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom :
  ∀ (K : ℝ) (_hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K_fixed K Q3.t0_critical, Q3.Q g ≥ 0 := by
  intro K _hK hA3 hRKHS g hg
  classical
  have _inst : Fintype (Q3.Nodes K) :=
    Set.Finite.fintype (Q3.Proofs.W_sum_BridgeV3.Nodes_finite (K := K))
  -- Uses the single-scale closure proof (t = t_critical).
  exact
    (Q3.Proofs.QNonnegClosure.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm
      (K := K) (hK := _hK) hA3 hRKHS g hg)

/-! ## Theorem wrapper (to be closed) -/

/-- Core positivity transfer: Fourier A3 bridge + RKHS contraction => Q >= 0 on atoms. -/
theorem Q_nonneg_on_atoms_of_A3_Fourier_RKHS :
  ∀ (K : ℝ) (_hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.AtomCone_K_fixed K Q3.t0_critical, Q3.Q g ≥ 0 := by
  intro K _hK hA3 hRKHS g hg
  exact Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom K _hK hA3 hRKHS g hg

/-! ## Guarded corollary: τ = 0 (BaseAtomCone_K) -/

theorem Q_nonneg_on_base_atoms_of_A3_Fourier_RKHS :
  ∀ (K : ℝ) (_hK : K ≥ 1),
    Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K →
    Q3.RKHS_contraction_data K →
    ∀ g ∈ Q3.BaseAtomCone_K K Q3.t0_critical, Q3.Q g ≥ 0 := by
  intro K _hK hA3 hRKHS g hg
  have hsubset := Q3.BaseAtomCone_K_subset_AtomCone_K_fixed K Q3.t0_critical
  exact Q_nonneg_on_atoms_of_A3_Fourier_RKHS K _hK hA3 hRKHS g (hsubset hg)

/-! ## BaseAtomCone (B-range, τ=0) at t_critical -/

theorem Q_nonneg_on_base_atoms_brange_tcritical :
  ∀ (K : ℝ) (_hK : K ≥ 1),
    ∀ g ∈ Q3.BaseAtomCone_K_brange K Q3.t0_critical B_min prime_cert_B_max, Q g ≥ 0 := by
  intro K _hK g hg
  exact Q3.Proofs.QNonnegTau0Bridge.Q_nonneg_on_base_atoms_brange_tcritical K _hK g hg

end Q3
