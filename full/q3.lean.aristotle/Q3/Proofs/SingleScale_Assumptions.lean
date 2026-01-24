import Q3.Axioms
import Q3.Proofs.Q_nonneg_t_critical
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.RKHS_cap_rayleigh

set_option linter.mathlibStandardSet false

/-!
Single-scale assumptions at t_critical.

These are temporary bridge axioms to close the fixed-t chain without the
two-scale `t_sym`/`t_rkhs_cap` mismatch. They can be proved or replaced later.
-/

noncomputable section

namespace Q3.Proofs.SingleScale

open Q3

/-! ## Continuity of the shifted symbol (tau = 0 mainline) -/

axiom continuous_P_A_shift (B : ℝ) : Continuous (Q3.P_A_shift B t_critical 0)

/-! ## A3-style lower bound at basis0 (tau = 0 mainline) -/

axiom rayleigh_basis0_shift_ge_cstar_quarter
    (B : ℝ) (M : ℕ) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4

/-! ## Single-scale prime cap (tau = 0 mainline) -/

theorem rho_oneK_tcritical_le_cstar_quarter (_K : ℝ) :
    Q3.Proofs.rho_one ≤ Q3.c_star / 4 := by
  norm_num [Q3.Proofs.rho_one, Q3.c_star]

/-! ## Single-scale RKHS contraction (t = t_critical) -/

axiom rkhs_contraction_tcritical
    (K : ℝ) (hK : K ≥ 1) :
    ∃ ρ : ℝ, ρ < 1 ∧
      ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Q3.Nodes K) →
        let T_P : Matrix S S ℝ := fun i j =>
          Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
          Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t_critical))
        ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

theorem rkhs_contraction_data_of_tcritical (K : ℝ) (hK : K ≥ 1) :
    Q3.RKHS_contraction_data K := by
  classical
  obtain ⟨ρ, hρ_lt, hT⟩ := rkhs_contraction_tcritical (K := K) hK
  refine ⟨t_critical, t_critical_pos, ρ, hρ_lt, ?_⟩
  intro S hS
  exact hT S hS

end Q3.Proofs.SingleScale
