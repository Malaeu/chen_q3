/- Helper lemmas for Fourier A3 -> atoms positivity. -/

import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.A3_bridge_rayleigh_first

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
