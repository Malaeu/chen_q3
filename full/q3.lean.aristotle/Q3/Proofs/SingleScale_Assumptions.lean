import Q3.Axioms
import Q3.Proofs.Q_nonneg_t_critical
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.RKHS_cap_rayleigh
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.A3_Floor_Critical_Goal

set_option linter.mathlibStandardSet false

/-!
Single-scale assumptions at t_critical.

These are temporary bridge axioms to close the fixed-t chain without the
two-scale `t_sym`/`t_rkhs_cap` mismatch. They can be proved or replaced later.
-/

noncomputable section

namespace Q3.Proofs.SingleScale

open Q3

/-! ## Single-scale floor at t_critical (from certificate) -/

theorem A3_floor : Q3.Proofs.A3FloorCritical.FloorGoal := by
  intro θ hθ
  have h := Q3.P_A_ge_c_star_at_t_critical (θ := θ)
  have h_eq : Q3.P_A_critical B_min θ = P_A B_min t_critical θ := by
    simp [Q3.P_A_critical, Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g,
      Q3.Proofs.RayleighQId.w_eq_fejer_heat_window]
  simpa [h_eq] using h

/-! ## Continuity of the shifted symbol (single-scale) -/

theorem continuous_P_A_shift (B tau : ℝ) (hB : 0 < B) :
    Continuous (Q3.P_A_shift B t_critical tau) := by
  simpa using
    (Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=tau) hB)

/-! ## A3-style lower bound at basis0 (tau = 0 mainline) -/

/-! ### Reduction: rayleigh_basis0 from the one-scale floor -/

theorem rayleigh_basis0_shift_ge_cstar_quarter_of_floor
    (B : ℝ) (M : ℕ) (hBmin : B = B_min)
    (h_floor : Q3.Proofs.A3FloorCritical.FloorGoal) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  classical
  subst hBmin
  have h_eq : Q3.P_A_shift B_min t_critical 0 = P_A B_min t_critical := by
    ext θ
    simp [Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g,
      Q3.Proofs.RayleighQId.w_eq_fejer_heat_window]
  have hB_pos : 0 < B_min := by
    norm_num [B_min]
  have hP_cont : Continuous (Q3.P_A_shift B_min t_critical 0) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B_min) (t:=t_critical) (tau:=0) hB_pos
  have hM : (2 * M + 1) > 0 := by
    exact Nat.succ_pos _
  have hRQ_full :
      Q3.RayleighQuotient
          (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
            (Q3.P_A_shift B_min t_critical 0))
          (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star := by
    have hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
        Q3.c_star ≤ Q3.P_A_shift B_min t_critical 0 θ := by
      intro θ hθ
      have h' := h_floor θ hθ
      simpa [h_eq] using h'
    exact RayleighFourier.rayleigh_lower_bound_real
      (M := 2 * M + 1) (hM := hM)
      (P := Q3.P_A_shift B_min t_critical 0) (hP_cont := hP_cont)
      (m := Q3.c_star) (hP_ge := hP_ge)
      (v := Q3.Proofs.RayleighQId.basis0 M)
      (hv := Q3.Proofs.RayleighQId.basis0_ne_zero M)
  have h_quarter : Q3.c_star / 4 ≤ Q3.c_star := by
    nlinarith [Q3.c_star_pos]
  exact le_trans h_quarter hRQ_full

lemma floor_P_A_shift_tcritical_Bmin
    (h_floor : Q3.Proofs.A3FloorCritical.FloorGoal) :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      Q3.c_star ≤ Q3.P_A_shift B_min t_critical 0 θ := by
  intro θ hθ
  have h' := h_floor θ hθ
  have h_eq : Q3.P_A_shift B_min t_critical 0 = P_A B_min t_critical := by
    ext t
    simp [Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g,
      Q3.Proofs.RayleighQId.w_eq_fejer_heat_window]
  simpa [h_eq] using h'

/-! ### Reduction: rayleigh_basis0 from arch_term at t_critical (Option 2) -/

theorem rayleigh_basis0_shift_ge_cstar_quarter_of_arch_term
    (B : ℝ) (M : ℕ) (hB : 0 < B)
    (h_arch : Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) ≥ Q3.c_star) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  have hP_cont : Continuous (Q3.P_A_shift B t_critical 0) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=0) hB
  have h_eq :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M)
        =
      Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) := by
    simpa using
      (Q3.Proofs.RayleighQId.arch_rayleigh_eq_shift
        (B:=B) (t:=t_critical) (tau:=0) (M:=M) hP_cont hB)
  have hRQ_full :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star := by
    simpa [h_eq] using h_arch
  have h_quarter : Q3.c_star / 4 ≤ Q3.c_star := by
    nlinarith [Q3.c_star_pos]
  exact le_trans h_quarter hRQ_full

theorem rayleigh_basis0_shift_ge_cstar_quarter
    (B : ℝ) (M : ℕ) (hB : 0 < B)
    (h_floor : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      Q3.c_star ≤ Q3.P_A_shift B t_critical 0 θ) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  have h_arch' :
      Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) ≥
        Q3.c_star * (1 - |(0 : ℝ)| / B) := by
    simpa using (Q3.arch_term_ge_at_t_critical (B:=B) (τ:=0) hB h_floor)
  have h_arch :
      Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) ≥ Q3.c_star := by
    simpa using h_arch'
  exact rayleigh_basis0_shift_ge_cstar_quarter_of_arch_term (B:=B) (M:=M) hB h_arch

theorem rayleigh_basis0_shift_ge_cstar_quarter_Bmin
    (M : ℕ) (h_floor : Q3.Proofs.A3FloorCritical.FloorGoal) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B_min t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  have hB : 0 < B_min := by
    norm_num [B_min]
  have h_floor' := floor_P_A_shift_tcritical_Bmin h_floor
  exact rayleigh_basis0_shift_ge_cstar_quarter (B:=B_min) (M:=M) hB h_floor'

theorem rayleigh_basis0_shift_ge_cstar_quarter_Bmin_from_floor
    (M : ℕ) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B_min t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  exact rayleigh_basis0_shift_ge_cstar_quarter_Bmin (M:=M) A3_floor

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
