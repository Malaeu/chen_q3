/- Helper lemmas for Fourier A3 -> atoms positivity. -/

import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.A3_bridge_rayleigh_first
import Q3.Proofs.PrimeTerm_t_bridge
import Q3.Proofs.Q_nonneg_lemmas

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

namespace Q3.Proofs.QNonnegAtoms

open scoped BigOperators Real Classical

lemma prime_sum_nonneg (K B t : ℝ) [Fintype (Q3.Nodes K)] :
    0 ≤ ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) := by
  classical
  refine Finset.sum_nonneg ?_
  intro n _
  exact mul_nonneg (Q3.w_Q_nonneg n) (Q3.fejer_heat_window_nonneg B t (Q3.xi_n n))

/-! ## A1: Linearity of Q over finite sums -/

lemma Q_finset_sum {n : ℕ} (atoms : Fin n → ℝ → ℝ) (coeffs : Fin n → ℝ)
    (h_int : ∀ i, MeasureTheory.Integrable (fun x => Q3.a_star x * atoms i x))
    (h_sum : ∀ i, Summable (fun k => Q3.w_Q k * atoms i (Q3.xi_n k))) :
    Q3.Q (fun x => ∑ i, coeffs i * atoms i x) =
      ∑ i, coeffs i * Q3.Q (atoms i) :=
  Q3.Proofs.Q_nonneg_lemmas.Q_finset_sum atoms coeffs h_int h_sum

/-! ## A5: Extension from atoms to AtomCone_K -/

lemma Q_nonneg_on_atomcone_of_atoms (K : ℝ) (hK : K ≥ 1)
    (h_atom : ∀ B t τ, B > 0 → t > 0 → |τ| + B ≤ K →
      Q3.Q (Q3.Fejer_heat_atom B t τ) ≥ 0) :
    ∀ g ∈ Q3.AtomCone_K K, Q3.Q g ≥ 0 :=
  Q3.Proofs.Q_nonneg_lemmas.Q_nonneg_on_atomcone_of_atoms K hK h_atom

/-! ## A5 (fixed-t): Extension to AtomCone_K_fixed -/

lemma Q_nonneg_on_atomcone_fixed_of_atoms (K t0 : ℝ) (hK : K ≥ 1) (ht0 : t0 > 0)
    (h_atom : ∀ B τ, B > 0 → |τ| + B ≤ K →
      Q3.Q (Q3.Fejer_heat_atom B t0 τ) ≥ 0) :
    ∀ g ∈ Q3.AtomCone_K_fixed K t0, Q3.Q g ≥ 0 := by
  intro g hg
  obtain ⟨n, c, B, τ, hc_nonneg, hB_pos, h_support, hg_eq, _hg_WK⟩ := hg
  have hg_fn : g = fun x => ∑ i, c i * Q3.Fejer_heat_atom (B i) t0 (τ i) x := by
    ext x; exact hg_eq x
  rw [hg_fn]
  have h_int : ∀ i, MeasureTheory.Integrable
      (fun x => Q3.a_star x * Q3.Fejer_heat_atom (B i) t0 (τ i) x) := by
    intro i
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_integrable_with_a_star
      (B i) t0 (τ i) (hB_pos i) ht0
  have h_sum : ∀ i, Summable
      (fun k => Q3.w_Q k * Q3.Fejer_heat_atom (B i) t0 (τ i) (Q3.xi_n k)) := by
    intro i
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_prime_summable
      (B i) t0 (τ i) (hB_pos i) ht0
  rw [Q_finset_sum _ _ h_int h_sum]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact hc_nonneg i
  · exact h_atom (B i) (τ i) (hB_pos i) (h_support i)

lemma Q_nonneg_fejer_heat_window
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (hK : B ≤ K) (hP : Continuous (P_A B t))
    (hM : 0 < 2 * M + 1)
    (h_rayleigh :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
         Q3.T_P_comp_real K B t M)
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4)
    (h_cap :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n) ≤
        Q3.Proofs.rho_one) :
    Q3.Q (fun ξ => Q3.fejer_heat_window B t ξ) ≥ 0 := by
  classical
  let S : ℝ :=
    ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)
  have hprime :
      Q3.prime_term (fun ξ => Q3.fejer_heat_window B t ξ) = S := by
    simpa [S] using
      (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum (B:=B) (t:=t) (K:=K) hB hK)
  have h_honest :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
         Q3.T_P_comp_real K B t M)
        (Q3.Proofs.RayleighQId.basis0 M) =
      Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) -
      (1 / (2 * M + 1 : ℝ)) * S := by
    simpa [S] using
      (Q3.Proofs.RayleighQId.honest_formula (B:=B) (t:=t) (K:=K) (M:=M) hB hP hM)
  have hQ :
      Q3.Q (fun ξ => Q3.fejer_heat_window B t ξ) =
        Q3.RayleighQuotient
          (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
           Q3.T_P_comp_real K B t M)
          (Q3.Proofs.RayleighQId.basis0 M) -
        (2 * M : ℝ) / (2 * M + 1 : ℝ) * S := by
    have harch :
        Q3.arch_term (fun ξ => Q3.fejer_heat_window B t ξ) =
          Q3.RayleighQuotient
            (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
             Q3.T_P_comp_real K B t M)
            (Q3.Proofs.RayleighQId.basis0 M) +
          (1 / (2 * M + 1 : ℝ)) * S := by
      linarith [h_honest]
    simp [Q3.Q, hprime, harch, S]
    have hpos : (2 * M + 1 : ℝ) ≠ 0 := by nlinarith [hM]
    field_simp [hpos]
    ring
  have hS_nonneg : 0 ≤ S := by
    have hsum := prime_sum_nonneg K B t
    simpa [S] using hsum
  have hcoef_le_one : (2 * M : ℝ) / (2 * M + 1 : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < 2 * M + 1 := by nlinarith [hM]
    have hle : (2 * M : ℝ) ≤ 2 * M + 1 := by nlinarith
    exact (div_le_iff₀ hpos).2 (by simp [hle])
  have hS_bound : (2 * M : ℝ) / (2 * M + 1 : ℝ) * S ≤ Q3.Proofs.rho_one := by
    have hS_le : S ≤ Q3.Proofs.rho_one := by simpa [S] using h_cap
    have hS_le' : (2 * M : ℝ) / (2 * M + 1 : ℝ) * S ≤ S := by
      exact mul_le_of_le_one_left hS_nonneg hcoef_le_one
    exact le_trans hS_le' hS_le
  have hRQ_bound :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B t) -
         Q3.T_P_comp_real K B t M)
        (Q3.Proofs.RayleighQId.basis0 M) -
      (2 * M : ℝ) / (2 * M + 1 : ℝ) * S ≥
      Q3.c_star / 4 - Q3.Proofs.rho_one := by
    nlinarith [h_rayleigh, hS_bound]
  have hfinal : Q3.c_star / 4 - Q3.Proofs.rho_one ≥ 0 := by
    norm_num [Q3.c_star, Q3.Proofs.rho_one]
  nlinarith [hQ, hRQ_bound, hfinal]

end Q3.Proofs.QNonnegAtoms

namespace Q3.Proofs.QNonnegAtoms

open Q3.Proofs.PrimeTermBridge

lemma Q_phi_shift_lower_bound
    (K B tau R : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (hK : |tau| + B ≤ K)
    (hP : Continuous (Q3.P_A_shift B t_sym tau))
    (hM : 0 < 2 * M + 1)
    (h_cap :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ R)
    (h_rayleigh :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t_sym tau))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4) :
    Q3.c_star / 4 - exp_tsym_to_rkhs K * R ≤
      Q3.Q (fun ξ => Q3.phi_shift B t_sym tau ξ) := by
  have harch :
      Q3.arch_term (fun ξ => Q3.phi_shift B t_sym tau ξ) =
        Q3.RayleighQuotient
          (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t_sym tau))
          (Q3.Proofs.RayleighQId.basis0 M) := by
    symm
    exact Q3.Proofs.RayleighQId.arch_rayleigh_eq_shift B t_sym tau M hP hB
  have harch_ge : Q3.c_star / 4 ≤ Q3.arch_term (fun ξ => Q3.phi_shift B t_sym tau ξ) := by
    simpa [harch] using h_rayleigh
  have hprime :
      Q3.prime_term (fun ξ => Q3.phi_shift B t_sym tau ξ) ≤
        exp_tsym_to_rkhs K * R :=
    prime_term_phi_shift_tsym_le_cap (K:=K) (B:=B) (tau:=tau) (R:=R) hB hK h_cap
  have hQ :
      Q3.Q (fun ξ => Q3.phi_shift B t_sym tau ξ) =
        Q3.arch_term (fun ξ => Q3.phi_shift B t_sym tau ξ) -
          Q3.prime_term (fun ξ => Q3.phi_shift B t_sym tau ξ) := rfl
  have hbound :
      Q3.c_star / 4 - exp_tsym_to_rkhs K * R ≤
        Q3.arch_term (fun ξ => Q3.phi_shift B t_sym tau ξ) -
          Q3.prime_term (fun ξ => Q3.phi_shift B t_sym tau ξ) := by
    nlinarith [harch_ge, hprime]
  simpa [hQ] using hbound

lemma Q_phi_shift_nonneg
    (K B tau R : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (hK : |tau| + B ≤ K)
    (hP : Continuous (Q3.P_A_shift B t_sym tau))
    (hM : 0 < 2 * M + 1)
    (h_cap :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ R)
    (h_rayleigh :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t_sym tau))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4)
    (hpos :
      0 ≤ Q3.c_star / 4 - exp_tsym_to_rkhs K * R) :
    0 ≤ Q3.Q (fun ξ => Q3.phi_shift B t_sym tau ξ) := by
  have hlower :=
    Q_phi_shift_lower_bound (K:=K) (B:=B) (tau:=tau) (R:=R) (M:=M) hB hK hP hM h_cap h_rayleigh
  exact le_trans hpos hlower

end Q3.Proofs.QNonnegAtoms
