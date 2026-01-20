/-
Definitions for the Fourier A3 bridge (shared).
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.A3_Floor_Main

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.P_A_Bridge

/-- A3 bridge data using Fourier Toeplitz with P_A symbol.
    This is the CORRECT formulation (Fourier Toeplitz, not sampling). -/
def A3_bridge_data_rayleigh_Fourier (K : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Q3.Nodes K)],
    ∃ t > 0, ∀ M : ℕ,
      ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
        Q3.RayleighQuotient
            (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
             Q3.T_P_comp_real K K t M) v
          ≥ Q3.c_star / 4

end Q3.Proofs.P_A_Bridge
