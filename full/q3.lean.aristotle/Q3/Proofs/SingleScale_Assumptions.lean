import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.PrimeTerm_t_bridge
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

axiom rho_oneK_tcritical_le_cstar_quarter (K : ℝ) :
    Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K ≤ Q3.c_star / 4

theorem prime_sum_phi_shift_le_cstar_quarter
    (K B tau : ℝ) [Fintype (Q3.Nodes K)] (hB : 0 < B) (hK : |tau| + B ≤ K) :
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_critical tau (Q3.xi_n n)
      ≤ Q3.c_star / 4 := by
  have hprime :
      Q3.prime_term (fun xi => Q3.phi_shift B t_critical tau xi) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_critical tau (Q3.xi_n n) := by
    simpa using
      (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift (B:=B) (t:=t_critical)
        (tau:=tau) (K:=K) hB hK)
  have hprime_le :
      Q3.prime_term (fun xi => Q3.phi_shift B t_critical tau xi) ≤
        Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K *
          ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    exact Q3.Proofs.PrimeTermBridge.prime_term_phi_shift_tcritical_le
      (K:=K) (B:=B) (tau:=tau) hB hK
  have hweight_prime :
      Q3.prime_term (fun xi => Q3.phi_shift B t_rkhs_cap tau xi) ≤
        Q3.Proofs.rho_oneK K := by
    exact Q3.Proofs.prime_term_phi_shift_le_rho_oneK (K:=K) (B:=B) (tau:=tau) hB hK
  have hweight :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤
        Q3.Proofs.rho_oneK K := by
    have hprime_rkhs :
        Q3.prime_term (fun xi => Q3.phi_shift B t_rkhs_cap tau xi) =
          ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
      simpa using
        (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift (B:=B) (t:=t_rkhs_cap)
          (tau:=tau) (K:=K) hB hK)
    simpa [hprime_rkhs] using hweight_prime
  have hexp_nonneg : 0 ≤ Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K := by
    unfold Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs
    exact (Real.exp_pos _).le
  have hprime_le' :
      Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K *
          ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)
        ≤ Q3.Proofs.PrimeTermBridge.exp_tcrit_to_rkhs K * Q3.Proofs.rho_oneK K := by
    exact mul_le_mul_of_nonneg_left hweight hexp_nonneg
  have hconst := rho_oneK_tcritical_le_cstar_quarter (K:=K)
  have hfinal :
      Q3.prime_term (fun xi => Q3.phi_shift B t_critical tau xi) ≤ Q3.c_star / 4 := by
    exact le_trans hprime_le (le_trans hprime_le' hconst)
  simpa [hprime] using hfinal

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
