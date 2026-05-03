import Q3.Axioms
import Q3.Proofs.Params_Critical
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.FloorCert.Defs
import Q3.Proofs.FloorCert.Grid_2219
import Q3.Proofs.FloorCert.Lipschitz_2219
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.RKHS_PrimeCap_Analytic
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.Q_nonneg_atoms_helpers
import Q3.Proofs.Q_nonneg_lemmas
import Q3.Proofs.off_diag_exp_sum_integrated

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3.Proofs.QNonnegTau0Bridge

open Q3.Proofs.FloorCert
open Q3.Proofs.PrimeCert

/-- t_critical > t_sym (0.15 > 0.06), so heat decay is stronger -/
lemma t_critical_gt_t_sym : t_critical > t_sym := by
  norm_num [t_critical, t_sym]

/-- At t_critical, the param conversion still matches `exp(-x^2/(4*t0_critical))`. -/
lemma exp_reparam_critical' (x : ℝ) :
    Real.exp (-x^2 / (4 * t0_critical)) = Real.exp (-4 * Real.pi ^ 2 * t_critical * x^2) :=
  Q3.exp_reparam_critical x

/-- Fejér-heat window at t_critical -/
def fejer_heat_window_critical (B : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t_critical * ξ^2)

lemma fejer_heat_window_critical_eq (B ξ : ℝ) :
    fejer_heat_window_critical B ξ = fejer_heat_window B t_critical ξ := by
  rfl

lemma fejer_heat_window_critical_nonneg (B ξ : ℝ) :
    0 ≤ fejer_heat_window_critical B ξ := by
  unfold fejer_heat_window_critical
  apply mul_nonneg
  · exact le_max_left _ _
  · exact Real.exp_nonneg _

/-- φ_shift at t_critical -/
def phi_shift_critical (B τ ξ : ℝ) : ℝ :=
  phi_shift B t_critical τ ξ

lemma phi_shift_critical_nonneg (B τ ξ : ℝ) :
    0 ≤ phi_shift_critical B τ ξ := by
  unfold phi_shift_critical phi_shift
  exact fejer_heat_window_nonneg B t_critical (ξ - τ)

/-- P_A at t_critical: periodized Archimedean density -/
def P_A_critical (B : ℝ) (θ : ℝ) : ℝ :=
  P_A_shift B t_critical 0 θ

/-- P_A additivity under integer shifts. -/
lemma P_A_add_int (B t : ℝ) (k : ℤ) (θ : ℝ) :
    P_A B t (θ + k) = P_A B t θ := by
  classical
  unfold P_A
  have htsum :
      (∑' m : ℤ, g B t (θ + k + m)) = ∑' m : ℤ, g B t (θ + m) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (Equiv.tsum_eq (Equiv.addRight k) (fun m : ℤ => g B t (θ + m)))
  simpa [add_assoc] using htsum

/-- Reduce any θ to the fundamental domain [-1/2, 1/2] by subtracting floor(θ + 1/2). -/
lemma sub_floor_add_half_mem_Icc (θ : ℝ) :
    θ - (Int.floor (θ + 1/2) : ℤ) ∈ Set.Icc (-1/2) (1/2) := by
  have h₁ : ((Int.floor (θ + 1/2) : ℤ) : ℝ) ≤ θ + 1/2 := by
    exact Int.floor_le (θ + 1/2)
  have h₂ : θ + 1/2 < ((Int.floor (θ + 1/2) : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one (θ + 1/2)
  constructor
  · nlinarith
  ·
    have : θ - (Int.floor (θ + 1/2) : ℤ) < 1/2 := by nlinarith
    exact le_of_lt this

/-- Grid cover certificate: every θ in Icc is within h/2 of some grid point. -/
lemma floor_cert_grid_cover_cert :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      ∃ i : Fin (floor_cert_N + 1),
        floor_grid i ∈ Set.Icc (-1/2 : ℝ) (1/2) ∧
          |θ - floor_grid i| ≤ floor_cert_h / 2 := by
  intro θ hθ
  -- rescale to [0, N]
  set t : ℝ := (θ + 1/2) / floor_cert_h
  have ht0 : 0 ≤ t := by
    have hθ' : 0 ≤ θ + 1/2 := by
      have hθl : (-1/2 : ℝ) ≤ θ := hθ.1
      nlinarith
    exact div_nonneg hθ' (le_of_lt floor_cert_h_pos)
  have htN : t ≤ (floor_cert_N : ℝ) := by
    have hθ' : θ + 1/2 ≤ 1 := by
      have hθu : θ ≤ (1/2 : ℝ) := hθ.2
      nlinarith
    -- (θ+1/2)/h ≤ N since N*h = 1
    have hdiv : (θ + 1/2) / floor_cert_h ≤ (floor_cert_N : ℝ) := by
      have hmul : θ + 1/2 ≤ (floor_cert_N : ℝ) * floor_cert_h := by
        simpa [floor_cert_N_mul_h] using hθ'
      exact (div_le_iff₀ (by exact floor_cert_h_pos)).2 hmul
    simpa [t] using hdiv
  -- choose nearest grid index via floor(t+1/2)
  set n : ℕ := Nat.floor (t + 1/2)
  have hn_le : (n : ℝ) ≤ t + 1/2 := Nat.floor_le (by nlinarith [ht0])
  have ht_lt : t + 1/2 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t + 1/2)
  have hn_lt : n < floor_cert_N + 1 := by
    have hnonneg : 0 ≤ t + 1/2 := by nlinarith [ht0]
    have h1 : t + 1/2 ≤ (floor_cert_N : ℝ) + 1/2 := by linarith [htN]
    have h2 : (floor_cert_N : ℝ) + 1/2 < (floor_cert_N : ℝ) + 1 := by
      nlinarith
    have htop' : t + 1/2 < ((floor_cert_N + 1 : ℕ) : ℝ) := by
      simpa using lt_of_le_of_lt h1 h2
    exact (Nat.floor_lt hnonneg).2 htop'
  have hn_leN : n ≤ floor_cert_N := Nat.lt_succ_iff.mp hn_lt
  -- build Fin index
  refine ⟨⟨n, hn_lt⟩, ?_, ?_⟩
  ·
    have h0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hN : (n : ℝ) ≤ (floor_cert_N : ℝ) := by exact_mod_cast hn_leN
    have hgrid_lo : (-1 / 2 : ℝ) ≤ floor_grid ⟨n, hn_lt⟩ := by
      simp [floor_grid]
      nlinarith [h0, floor_cert_h_pos]
    have hgrid_hi : floor_grid ⟨n, hn_lt⟩ ≤ (1 / 2 : ℝ) := by
      simp [floor_grid]
      -- -1/2 + n*h ≤ -1/2 + N*h = 1/2
      have hmul : (n : ℝ) * floor_cert_h ≤ (floor_cert_N : ℝ) * floor_cert_h := by
        exact mul_le_mul_of_nonneg_right hN (le_of_lt floor_cert_h_pos)
      nlinarith [hmul, floor_cert_N_mul_h]
    exact ⟨hgrid_lo, hgrid_hi⟩
  ·
    have h_repr : t * floor_cert_h = θ + 1 / 2 := by
      unfold t
      field_simp [floor_cert_h_ne_zero]
    have hdiff :
        θ - floor_grid ⟨n, hn_lt⟩ = floor_cert_h * (t - n) := by
      simp [floor_grid]
      -- use t*h = θ+1/2
      nlinarith [h_repr]
    have habs_t : |t - n| ≤ (1 / 2 : ℝ) := by
      have h1 : (n : ℝ) - 1/2 ≤ t := by nlinarith [hn_le]
      have h2 : t ≤ (n : ℝ) + 1/2 := by nlinarith [ht_lt]
      exact (abs_le.mpr ⟨by nlinarith [h1], by nlinarith [h2]⟩)
    have habs : |θ - floor_grid ⟨n, hn_lt⟩| ≤ floor_cert_h / 2 := by
      -- |θ - grid| = h*|t-n|
      have hmul : |θ - floor_grid ⟨n, hn_lt⟩| = floor_cert_h * |t - n| := by
        simp [hdiff, abs_mul, abs_of_pos floor_cert_h_pos]
      have hmul' : floor_cert_h * |t - n| ≤ floor_cert_h * (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left habs_t (le_of_lt floor_cert_h_pos)
      simpa [hmul] using hmul'
    simpa using habs

/-- P_A floor at t_critical from the grid/Lipschitz certificate. -/
lemma P_A_floor_cert_on_Icc_cert :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 ≤
        P_A B_min t_critical θ := by
  intro θ hθ
  rcases floor_cert_grid_cover_cert θ hθ with ⟨i, hi_mem, hdist⟩
  have hgrid : floor_cert_min_lb ≤ P_A B_min t_critical (floor_grid i) :=
    P_A_floor_cert_on_grid_cert i
  have hLip :
      |P_A B_min t_critical θ - P_A B_min t_critical (floor_grid i)| ≤
        floor_cert_L_ub * |θ - floor_grid i| := by
    simpa [sub_eq_add_neg, abs_sub_comm] using
      (P_A_Lipschitz_on_Icc_cert θ (floor_grid i) hθ hi_mem)
  have hLip_lower :
      P_A B_min t_critical (floor_grid i) - floor_cert_L_ub * |θ - floor_grid i| ≤
        P_A B_min t_critical θ := by
    have h' := (abs_sub_le_iff).1 hLip
    -- h'.2: P_A(grid) - P_A(θ) ≤ L*|θ-grid|
    nlinarith [h'.2]
  have hdist' :
      floor_cert_L_ub * |θ - floor_grid i| ≤ floor_cert_L_ub * (floor_cert_h / 2) := by
    exact mul_le_mul_of_nonneg_left hdist floor_cert_L_ub_nonneg
  nlinarith [hgrid, hLip_lower, hdist']

lemma P_A_floor_cert_on_Icc :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 ≤
        P_A B_min t_critical θ := by
  simpa using P_A_floor_cert_on_Icc_cert

/-- P_A floor at t_critical: min P_A ≥ c_star = 11/10. -/
lemma P_A_ge_c_star_at_t_critical (θ : ℝ) :
    P_A_critical B_min θ ≥ c_star := by
  have hPA : P_A_critical B_min θ = P_A B_min t_critical θ := by
    simp [P_A_critical, Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g, w, Q3.fejer_heat_window]

  let k : ℤ := Int.floor (θ + 1/2)
  have hk : θ - k ∈ Set.Icc (-1/2 : ℝ) (1/2) := by
    simpa [k] using (sub_floor_add_half_mem_Icc (θ := θ))

  have hgrid :
      floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 ≤
        P_A B_min t_critical (θ - k) := by
    exact P_A_floor_cert_on_Icc (θ - k) hk

  have hcert : c_star ≤ floor_cert_min_lb - floor_cert_L_ub * floor_cert_h / 2 := by
    simpa using floor_cert_margin_ge_c_star

  have hshift : P_A B_min t_critical θ = P_A B_min t_critical (θ - k) := by
    -- use periodicity with integer shift k
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (P_A_add_int (B := B_min) (t := t_critical) (k := k) (θ := θ - k))

  have hPAθ : c_star ≤ P_A B_min t_critical θ := by
    have h1 : c_star ≤ P_A B_min t_critical (θ - k) := le_trans hcert hgrid
    simpa [hshift] using h1

  have : c_star ≤ P_A_critical B_min θ := by
    simpa [hPA] using hPAθ

  exact this

/-- arch_term at t_critical is bounded below. -/
lemma arch_term_ge_at_t_critical (B τ : ℝ) (hB : B > 0)
    (h_floor : ∀ θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
      c_star ≤ P_A_shift B t_critical τ θ) :
    arch_term (fun ξ => phi_shift_critical B τ ξ) ≥
      c_star * (1 - |τ| / B) := by
  have hab : (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have h_cont : Continuous (fun θ => P_A_shift B t_critical τ θ) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=τ) hB
  have h_int : IntervalIntegrable (fun θ => P_A_shift B t_critical τ θ) volume (-1 / 2) (1 / 2) :=
    h_cont.intervalIntegrable _ _
  have h_const : IntervalIntegrable (fun _ : ℝ => (c_star : ℝ)) volume (-1 / 2) (1 / 2) := by
    simpa using
      (intervalIntegrable_const (μ := volume) (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        (c := (c_star : ℝ)))
  have h_mono :
      (∫ θ in (-1 / 2 : ℝ)..(1 / 2), (c_star : ℝ)) ≤
        ∫ θ in (-1 / 2 : ℝ)..(1 / 2), P_A_shift B t_critical τ θ := by
    exact intervalIntegral.integral_mono_on
      (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (μ := volume)
      (f := fun _ : ℝ => (c_star : ℝ)) (g := fun θ => P_A_shift B t_critical τ θ)
      (hab := hab) (hf := h_const) (hg := h_int) h_floor
  have hlen : ((2⁻¹ : ℝ) - (-1/2)) = (1 : ℝ) := by norm_num
  have h_const_int :
      (∫ θ in (-1 / 2 : ℝ)..(1 / 2), (c_star : ℝ)) = c_star := by
    simp [intervalIntegral.integral_const, hlen]
  have h_arch_eq :
      ∫ θ in (-1 / 2 : ℝ)..(1 / 2), P_A_shift B t_critical τ θ =
        arch_term (fun ξ => phi_shift_critical B τ ξ) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.ShiftedWindows.integral_P_A_shift_eq_arch_term (B:=B) (t:=t_critical)
        (tau:=τ) hB)
  have h_arch_ge : arch_term (fun ξ => phi_shift_critical B τ ξ) ≥ c_star := by
    have h_mono' := h_mono
    rw [h_const_int] at h_mono'
    rw [h_arch_eq] at h_mono'
    exact h_mono'
  have h_factor : c_star * (1 - |τ| / B) ≤ c_star := by
    have h_nonneg : 0 ≤ |τ| / B := by
      exact div_nonneg (abs_nonneg _) (le_of_lt hB)
    nlinarith [h_nonneg, c_star_pos]
  exact le_trans h_factor h_arch_ge

/-- bridge through margin certificate on B-range. -/
lemma prime_term_le_at_t_critical_tau0_brange_of_margin
    (h_margin_cert : PrimeCertMarginOnBrange)
    (B : ℝ) (hB : B ∈ Set.Icc B_min prime_cert_B_max) :
    Q3.prime_term (fun ξ => phi_shift_critical B 0 ξ) ≤
      Q3.arch_term (fun ξ => phi_shift_critical B 0 ξ) := by
  have hprime : prime_cert_margin_lb ≤
      arch_term (fun ξ => phi_shift_critical B 0 ξ) - prime_term (fun ξ => phi_shift_critical B 0 ξ) :=
    h_margin_cert B hB
  have h0 : 0 ≤ prime_cert_margin_lb := le_of_lt prime_cert_margin_pos
  have hnonneg : 0 ≤ arch_term (fun ξ => phi_shift_critical B 0 ξ)
      - Q3.prime_term (fun ξ => phi_shift_critical B 0 ξ) := by
    exact le_trans h0 hprime
  exact sub_nonneg.mp hnonneg

lemma Q_phi_shift_nonneg_t_critical_tau0_brange_of_margin
    (h_margin_cert : PrimeCertMarginOnBrange) (B : ℝ)
    (hBmin : B_min ≤ B) (hBmax : B ≤ prime_cert_B_max) :
    Q3.Q (fun ξ => phi_shift_critical B 0 ξ) ≥ 0 := by
  unfold Q
  have hBrange : B ∈ Set.Icc B_min prime_cert_B_max := ⟨hBmin, hBmax⟩
  have hprime :
      prime_term (fun ξ => phi_shift_critical B 0 ξ) ≤
        arch_term (fun ξ => phi_shift_critical B 0 ξ) := by
    exact prime_term_le_at_t_critical_tau0_brange_of_margin h_margin_cert B hBrange
  linarith

/-- Q ≥ 0 on BaseAtomCone_K_brange at t_critical (τ = 0) via margin certificate. -/
theorem Q_nonneg_on_base_atoms_at_t_critical_brange_of_margin
    (K : ℝ) (_hK : K ≥ 1) (h_margin_cert : PrimeCertMarginOnBrange) :
    ∀ g ∈ Q3.BaseAtomCone_K_brange K t0_critical B_min prime_cert_B_max,
    Q3.Q g ≥ 0 := by
  haveI : Fintype (Q3.Nodes K) := Q3.Proofs.OffDiagExpSum.Nodes_Fintype K
  intro g hg
  rcases hg with ⟨n, c, B, hc, hBmin, hBmax, hg_sum, _hg_WK⟩

  have hBmin_pos : (0 : ℝ) < B_min := by
    norm_num [B_min]

  have h_int : ∀ i, MeasureTheory.Integrable
      (fun x => Q3.a_star x * Q3.Fejer_heat_atom (B i) t0_critical 0 x) := by
    intro i
    have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_integrable_with_a_star
      (B i) t0_critical 0 hBpos t0_critical_pos

  have h_sum : ∀ i, Summable
      (fun k => Q3.w_Q k * Q3.Fejer_heat_atom (B i) t0_critical 0 (Q3.xi_n k)) := by
    intro i
    have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
    exact Q3.Proofs.Q_nonneg_lemmas.fejer_heat_atom_prime_summable
      (B i) t0_critical 0 hBpos t0_critical_pos

  have hQ_sum :
      Q3.Q (fun x => ∑ i, c i * Q3.Fejer_heat_atom (B i) t0_critical 0 x) =
        ∑ i, c i * Q3.Q (Q3.Fejer_heat_atom (B i) t0_critical 0) := by
    exact Q3.Proofs.Q_nonneg_lemmas.Q_finset_sum
      (atoms := fun i => Q3.Fejer_heat_atom (B i) t0_critical 0)
      (coeffs := c) h_int h_sum

  have h_atom : ∀ i, Q3.Q (Q3.Fejer_heat_atom (B i) t0_critical 0) ≥ 0 := by
    intro i
    obtain ⟨c0, hc0_pos, hdecomp⟩ :=
      Q3.Proofs.QNonnegAtoms.Fejer_heat_atom_decomposition
        (B := B i) (t := t0_critical) (tau := 0) t0_critical_pos
    have h_int_f :
        MeasureTheory.Integrable (fun x => Q3.a_star x * phi_shift_critical (B i) 0 x) := by
      have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_integrable_with_a_star
          (B := B i) (t := t_critical) (tau := 0) (hB := hBpos))
    have h_sum_f :
        Summable (fun k => Q3.w_Q k * phi_shift_critical (B i) 0 (Q3.xi_n k)) := by
      have hBpos : B i > 0 := by nlinarith [hBmin i, hBmin_pos]
      simpa [phi_shift_critical] using
        (Q3.Proofs.QNonnegAtoms.phi_shift_prime_summable
          (B := B i) (t := t_critical) (tau := 0) (hB := hBpos))
    have hQ_scale_add :
        Q3.Q (fun x => c0 * (phi_shift_critical (B i) 0 x + phi_shift_critical (B i) 0 x)) =
          c0 * (Q3.Q (fun x => phi_shift_critical (B i) 0 x) +
            Q3.Q (fun x => phi_shift_critical (B i) 0 x)) := by
      exact
        (Q3.Proofs.QNonnegAtoms.Q_scale_add
          (f := fun x => phi_shift_critical (B i) 0 x)
          (g := fun x => phi_shift_critical (B i) 0 x)
          (c := c0) h_int_f h_int_f h_sum_f h_sum_f)
    have hQphi : Q3.Q (fun x => phi_shift_critical (B i) 0 x) ≥ 0 := by
      exact Q_phi_shift_nonneg_t_critical_tau0_brange_of_margin
        (h_margin_cert := h_margin_cert) (B := B i)
        (hBmin := hBmin i) (hBmax := hBmax i)
    have hQ_nonneg :
        0 ≤ c0 * (Q3.Q (fun x => phi_shift_critical (B i) 0 x) +
          Q3.Q (fun x => phi_shift_critical (B i) 0 x)) := by
      have hc0 : 0 ≤ c0 := le_of_lt hc0_pos
      have hsum : 0 ≤ Q3.Q (fun x => phi_shift_critical (B i) 0 x) +
          Q3.Q (fun x => phi_shift_critical (B i) 0 x) := by
        nlinarith [hQphi]
      exact mul_nonneg hc0 hsum
    have h_eq :
        Q3.Q (Q3.Fejer_heat_atom (B i) t0_critical 0) =
          c0 * (Q3.Q (fun x => phi_shift_critical (B i) 0 x) +
            Q3.Q (fun x => phi_shift_critical (B i) 0 x)) := by
      have hfun :
          (fun x => Q3.Fejer_heat_atom (B i) t0_critical 0 x) =
            fun x => c0 * (phi_shift_critical (B i) 0 x + phi_shift_critical (B i) 0 x) := by
        funext x
        have htcrit : (1 / (16 * Real.pi ^ 2 * t0_critical)) = t_critical := by
          have hden : (16 * Real.pi ^ 2 * t_critical) ≠ 0 := by
            have hpi : 0 < (Real.pi ^ 2) := pow_pos Real.pi_pos 2
            have h16 : 0 < (16 : ℝ) := by norm_num
            have h1 : 0 < (16 * Real.pi ^ 2) := mul_pos h16 hpi
            have hpos : 0 < (16 * Real.pi ^ 2 * t_critical) := mul_pos h1 t_critical_pos
            exact ne_of_gt hpos
          by_cases hzero : (16 * Real.pi ^ 2 * t_critical) = 0
          · exfalso
            exact hden hzero
          · unfold t0_critical
            field_simp [hzero]
        simpa [phi_shift_critical, htcrit] using hdecomp x
      simpa [hfun] using hQ_scale_add
    have hQ : 0 ≤ Q3.Q (Q3.Fejer_heat_atom (B i) t0_critical 0) := by
      simpa [h_eq] using hQ_nonneg
    exact hQ

  have hQ : Q3.Q g = ∑ i, c i * Q3.Q (Q3.Fejer_heat_atom (B i) t0_critical 0) := by
    have hfun : g = (fun x => ∑ i, c i * Q3.Fejer_heat_atom (B i) t0_critical 0 x) := by
      funext x
      exact hg_sum x
    simpa [hfun] using hQ_sum

  rw [hQ]
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact hc i
  · exact h_atom i

/-- Base τ = 0 B-range bridge for `Main` API. -/
theorem Q_nonneg_on_base_atoms_brange_tcritical
    (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ Q3.BaseAtomCone_K_brange K t0_critical B_min prime_cert_B_max, Q3.Q g ≥ 0 := by
  intro g hg
  exact
    (Q_nonneg_on_base_atoms_at_t_critical_brange_of_margin
      (K := K) (_hK := hK) (h_margin_cert := Q3.prime_cert_margin_from_rkhs)) g hg

end Q3.Proofs.QNonnegTau0Bridge
