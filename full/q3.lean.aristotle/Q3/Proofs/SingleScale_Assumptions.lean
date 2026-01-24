import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.Rayleigh_Q_identification

set_option linter.mathlibStandardSet false

/-!
Single-scale assumptions at t_critical.

These are temporary bridge axioms to close the fixed-t chain without the
two-scale `t_sym`/`t_rkhs_cap` mismatch. They can be proved or replaced later.
-/

noncomputable section

namespace Q3.Proofs.SingleScale

open Q3

/-! ## Continuity of the shifted symbol -/

axiom continuous_P_A_shift (B tau : ℝ) : Continuous (Q3.P_A_shift B t_critical tau)

/-! ## A3-style lower bound at basis0 (shifted symbol) -/

axiom rayleigh_basis0_shift_ge_cstar_quarter
    (K B tau : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical tau))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4

/-! ## Single-scale prime cap (sum form) -/

axiom prime_sum_phi_shift_le_cstar_quarter
    (K B tau : ℝ) [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : |tau| + B ≤ K) :
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_critical tau (Q3.xi_n n)
      ≤ Q3.c_star / 4

end Q3.Proofs.SingleScale
