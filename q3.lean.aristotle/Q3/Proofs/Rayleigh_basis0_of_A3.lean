/-
Rayleigh basis0 bound extracted from Fourier A3 bridge.
-/

import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.P_A_Toeplitz_bridge

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.QNonnegAtoms

lemma rayleigh_basis0_of_A3 (K : ℝ) (hK : K ≥ 1) [Fintype (Q3.Nodes K)]
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    ∃ t > 0, ∀ M : ℕ,
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
         Q3.T_P_comp_real K K t M)
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  classical
  obtain ⟨t, ht, hA3M⟩ := hA3 hK
  refine ⟨t, ht, ?_⟩
  intro M
  have hne : Q3.Proofs.RayleighQId.basis0 M ≠ 0 :=
    Q3.Proofs.RayleighQId.basis0_ne_zero M
  exact hA3M M (Q3.Proofs.RayleighQId.basis0 M) hne

end Q3.Proofs.QNonnegAtoms
