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

namespace Q3.Proofs.QNonnegAtoms

open Q3
open Q3.Proofs.ShiftedWindows

/-! ## phi_shift support, integrability, and summability -/

lemma phi_shift_support_subset (B t tau : ℝ) (hB : 0 < B) :
    Function.support (Q3.phi_shift B t tau) ⊆ Set.Icc (tau - B) (tau + B) := by
  intro xi hxi
  simp only [Function.mem_support] at hxi
  by_contra h_not
  by_cases hlt : xi < tau - B
  · have hneg : xi - tau < 0 := by linarith
    have hB' : B < -(xi - tau) := by linarith
    have hdist : B < |xi - tau| := by
      simpa [abs_of_neg hneg] using hB'
    have h_zero := phi_shift_support B t tau xi hB hdist
    exact hxi h_zero
  · have hge : tau - B ≤ xi := by
      have hnot : ¬ (tau - B > xi) := by
        simpa [gt_iff_lt] using hlt
      exact le_of_not_gt hnot
    have hgt : tau + B < xi := by
      have : ¬ xi ≤ tau + B := by
        intro hle
        exact h_not ⟨hge, hle⟩
      exact lt_of_not_ge this
    have hpos : 0 < xi - tau := by linarith
    have hB' : B < xi - tau := by linarith
    have hdist : B < |xi - tau| := by
      simpa [abs_of_pos hpos] using hB'
    have h_zero := phi_shift_support B t tau xi hB hdist
    exact hxi h_zero

lemma phi_shift_integrable_with_a_star (B t tau : ℝ) (hB : 0 < B) :
    MeasureTheory.Integrable (fun x => Q3.a_star x * Q3.phi_shift B t tau x) := by
  have h_phi_hcs : HasCompactSupport (Q3.phi_shift B t tau) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (phi_shift_support_subset B t tau hB)
  have h_prod_cont : Continuous (fun x => Q3.a_star x * Q3.phi_shift B t tau x) :=
    Q3.a_star_continuous.mul (continuous_phi_shift B t tau)
  have h_prod_hcs : HasCompactSupport (fun x => Q3.a_star x * Q3.phi_shift B t tau x) :=
    h_phi_hcs.mul_left
  exact h_prod_cont.integrable_of_hasCompactSupport h_prod_hcs

lemma phi_shift_prime_summable (B t tau : ℝ) (hB : 0 < B) :
    Summable (fun k => Q3.w_Q k * Q3.phi_shift B t tau (Q3.xi_n k)) := by
  let N := Nat.ceil (Real.exp (2 * Real.pi * (|tau| + B))) + 1
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  suffices h : Q3.phi_shift B t tau (Q3.xi_n k) = 0 by simp [h]
  have h_xi_large : Q3.xi_n k > |tau| + B := by
    apply Q3.Proofs.Q_nonneg_lemmas.xi_n_large_of_k_large
    omega
  have h_right : tau + B < Q3.xi_n k := by
    have htau : tau ≤ |tau| := le_abs_self tau
    linarith
  have h_not_in_Icc : Q3.xi_n k ∉ Set.Icc (tau - B) (tau + B) := by
    intro h
    exact (not_lt_of_ge h.2) h_right
  have h_supp := phi_shift_support_subset (B:=B) (t:=t) (tau:=tau) hB
  by_contra h_ne
  exact h_not_in_Icc (h_supp (Function.mem_support.mpr h_ne))

/-! ## Fejer_heat_atom decomposition and single-atom nonnegativity (abstract) -/

lemma Fejer_heat_atom_decomposition (B t tau : ℝ) (ht : 0 < t) :
    ∃ c > 0, ∀ xi, Q3.Fejer_heat_atom B t tau xi =
      c * (Q3.phi_shift B (1 / (16 * Real.pi ^ 2 * t)) tau xi +
        Q3.phi_shift B (1 / (16 * Real.pi ^ 2 * t)) (-tau) xi) := by
  -- Choose t' = 1/(16*pi^2*t) and c = 1/sqrt(4*pi*t)
  refine ⟨1 / Real.sqrt (4 * Real.pi * t), ?_, ?_⟩
  · apply div_pos one_pos
    apply Real.sqrt_pos_of_pos
    apply mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) ht
  · intro xi
    have exp_eq1 :
        -(xi - tau) ^ 2 / (4 * t) =
          -4 * Real.pi ^ 2 * (1 / (16 * Real.pi ^ 2 * t)) * (xi - tau) ^ 2 := by
      field_simp
      ring
    have exp_eq2 :
        -(xi + tau) ^ 2 / (4 * t) =
          -4 * Real.pi ^ 2 * (1 / (16 * Real.pi ^ 2 * t)) * (xi + tau) ^ 2 := by
      field_simp
      ring
    have exp_eq2' :
        -(tau + xi) ^ 2 / (4 * t) =
          -4 * Real.pi ^ 2 * (1 / (16 * Real.pi ^ 2 * t)) * (tau + xi) ^ 2 := by
      simpa [add_comm] using exp_eq2
    simp [Q3.Fejer_heat_atom, Q3.heat_kernel_A1, Q3.Fejer_kernel, Q3.phi_shift,
      Q3.fejer_heat_window, exp_eq1, exp_eq2', add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
    ring

lemma Q_scale_add (f g : ℝ → ℝ) (c : ℝ)
    (h_int_f : MeasureTheory.Integrable (fun x => Q3.a_star x * f x))
    (h_int_g : MeasureTheory.Integrable (fun x => Q3.a_star x * g x))
    (h_sum_f : Summable (fun k => Q3.w_Q k * f (Q3.xi_n k)))
    (h_sum_g : Summable (fun k => Q3.w_Q k * g (Q3.xi_n k))) :
    Q3.Q (fun x => c * (f x + g x)) = c * (Q3.Q f + Q3.Q g) := by
  classical
  let atoms : Fin 2 → ℝ → ℝ := fun i => if i.val = 0 then f else g
  let coeffs : Fin 2 → ℝ := fun _ => c
  have h_int : ∀ i, MeasureTheory.Integrable (fun x => Q3.a_star x * atoms i x) := by
    intro i
    fin_cases i <;> simp [atoms, h_int_f, h_int_g]
  have h_sum : ∀ i, Summable (fun k => Q3.w_Q k * atoms i (Q3.xi_n k)) := by
    intro i
    fin_cases i <;> simp [atoms, h_sum_f, h_sum_g]
  have hQ := Q3.Proofs.Q_nonneg_lemmas.Q_finset_sum
    (atoms:=atoms) (coeffs:=coeffs) h_int h_sum
  have h_eval :
      (fun x => ∑ i : Fin 2, coeffs i * atoms i x) =
        fun x => c * (f x + g x) := by
    funext x
    simp [atoms, coeffs, Fin.sum_univ_two, mul_add, add_mul]
  have h_eval2 :
      (fun x => coeffs 0 * atoms 0 x + coeffs 1 * atoms 1 x) =
        fun x => c * (f x + g x) := by
    funext x
    simp [atoms, coeffs, mul_add, add_mul]
  have hQ' : Q3.Q (fun x => c * (f x + g x)) =
      ∑ i : Fin 2, coeffs i * Q3.Q (atoms i) := by
    simpa [h_eval2] using hQ
  calc
    Q3.Q (fun x => c * (f x + g x)) = ∑ i : Fin 2, coeffs i * Q3.Q (atoms i) := hQ'
    _ = c * (Q3.Q f + Q3.Q g) := by
      simp [atoms, coeffs, Fin.sum_univ_two, mul_add, add_mul]

lemma Q_single_atom_nonneg_of_phi_shift
    (K B t tau R : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (ht : 0 < t) (hK : |tau| + B ≤ K)
    (htsym : (1 / (16 * Real.pi ^ 2 * t)) = t_sym)
    (hP : Continuous (Q3.P_A_shift B t_sym tau))
    (hP_neg : Continuous (Q3.P_A_shift B t_sym (-tau)))
    (hM : 0 < 2 * M + 1)
    (h_cap :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ R)
    (h_cap_neg :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap (-tau) (Q3.xi_n n) ≤ R)
    (h_rayleigh :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t_sym tau))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4)
    (h_rayleigh_neg :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t_sym (-tau)))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4)
    (hpos : 0 ≤ Q3.c_star / 4 - PrimeTermBridge.exp_tsym_to_rkhs K * R)
    (h_int :
      MeasureTheory.Integrable (fun x => Q3.a_star x * Q3.phi_shift B t_sym tau x))
    (h_int_neg :
      MeasureTheory.Integrable (fun x => Q3.a_star x * Q3.phi_shift B t_sym (-tau) x))
    (h_sum :
      Summable (fun k => Q3.w_Q k * Q3.phi_shift B t_sym tau (Q3.xi_n k)))
    (h_sum_neg :
      Summable (fun k => Q3.w_Q k * Q3.phi_shift B t_sym (-tau) (Q3.xi_n k))) :
    0 ≤ Q3.Q (Q3.Fejer_heat_atom B t tau) := by
  obtain ⟨c, hc, h_decomp⟩ := Fejer_heat_atom_decomposition B t tau ht
  have hK_neg : |(-tau)| + B ≤ K := by simpa [abs_neg] using hK
  have hQ_phi :
      0 ≤ Q3.Q (fun xi => Q3.phi_shift B t_sym tau xi) := by
    exact Q_phi_shift_nonneg (K:=K) (B:=B) (tau:=tau) (R:=R) (M:=M)
      hB hK hP hM h_cap h_rayleigh hpos
  have hQ_phi_neg :
      0 ≤ Q3.Q (fun xi => Q3.phi_shift B t_sym (-tau) xi) := by
    exact Q_phi_shift_nonneg (K:=K) (B:=B) (tau:=(-tau)) (R:=R) (M:=M)
      hB hK_neg hP_neg hM h_cap_neg h_rayleigh_neg hpos
  have hQ :
      Q3.Q (Q3.Fejer_heat_atom B t tau) =
        c * (Q3.Q (fun xi => Q3.phi_shift B t_sym tau xi) +
          Q3.Q (fun xi => Q3.phi_shift B t_sym (-tau) xi)) := by
    have h_eval :
        (fun xi => c * (Q3.phi_shift B t_sym tau xi +
          Q3.phi_shift B t_sym (-tau) xi)) =
          fun xi => Q3.Fejer_heat_atom B t tau xi := by
      funext xi
      simp [h_decomp, htsym, add_comm, add_left_comm, add_assoc]
    have hQ' := Q_scale_add
      (f:=fun xi => Q3.phi_shift B t_sym tau xi)
      (g:=fun xi => Q3.phi_shift B t_sym (-tau) xi)
      (c:=c) h_int h_int_neg h_sum h_sum_neg
    simpa [h_eval] using hQ'
  have hsum_nonneg :
      0 ≤ Q3.Q (fun xi => Q3.phi_shift B t_sym tau xi) +
        Q3.Q (fun xi => Q3.phi_shift B t_sym (-tau) xi) := by
    linarith
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hfinal : 0 ≤ c *
      (Q3.Q (fun xi => Q3.phi_shift B t_sym tau xi) +
        Q3.Q (fun xi => Q3.phi_shift B t_sym (-tau) xi)) :=
    mul_nonneg hc_nonneg hsum_nonneg
  simpa [hQ] using hfinal

lemma Q_single_atom_nonneg_of_phi_shift_basic
    (K B t tau R : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (hB : 0 < B) (ht : 0 < t) (hK : |tau| + B ≤ K)
    (htsym : (1 / (16 * Real.pi ^ 2 * t)) = t_sym)
    (hP : Continuous (Q3.P_A_shift B t_sym tau))
    (hP_neg : Continuous (Q3.P_A_shift B t_sym (-tau)))
    (hM : 0 < 2 * M + 1)
    (h_cap :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ R)
    (h_cap_neg :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap (-tau) (Q3.xi_n n) ≤ R)
    (h_rayleigh :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t_sym tau))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4)
    (h_rayleigh_neg :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (Q3.P_A_shift B t_sym (-tau)))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4)
    (hpos : 0 ≤ Q3.c_star / 4 - PrimeTermBridge.exp_tsym_to_rkhs K * R) :
    0 ≤ Q3.Q (Q3.Fejer_heat_atom B t tau) := by
  have h_int :
      MeasureTheory.Integrable (fun x => Q3.a_star x * Q3.phi_shift B t_sym tau x) :=
    phi_shift_integrable_with_a_star (B:=B) (t:=t_sym) (tau:=tau) hB
  have h_int_neg :
      MeasureTheory.Integrable (fun x => Q3.a_star x * Q3.phi_shift B t_sym (-tau) x) :=
    phi_shift_integrable_with_a_star (B:=B) (t:=t_sym) (tau:=(-tau)) hB
  have h_sum :
      Summable (fun k => Q3.w_Q k * Q3.phi_shift B t_sym tau (Q3.xi_n k)) :=
    phi_shift_prime_summable (B:=B) (t:=t_sym) (tau:=tau) hB
  have h_sum_neg :
      Summable (fun k => Q3.w_Q k * Q3.phi_shift B t_sym (-tau) (Q3.xi_n k)) :=
    phi_shift_prime_summable (B:=B) (t:=t_sym) (tau:=(-tau)) hB
  exact Q_single_atom_nonneg_of_phi_shift
    (K:=K) (B:=B) (t:=t) (tau:=tau) (R:=R) (M:=M)
    hB ht hK htsym hP hP_neg hM h_cap h_cap_neg h_rayleigh h_rayleigh_neg hpos
    h_int h_int_neg h_sum h_sum_neg

end Q3.Proofs.QNonnegAtoms
