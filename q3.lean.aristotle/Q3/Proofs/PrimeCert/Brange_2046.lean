import Mathlib
import Q3.Proofs.PrimeCert.Defs
import Q3.Proofs.PrimeCert.BrangeGrid_2046
import Q3.Proofs.PrimeCert.BrangeCert_2046
import Q3.Proofs.PrimeCert.PrimeHeatMarginKernel
import Q3.Proofs.PrimeCert.PrimeHeatMarginWitness_2026_01_28
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical
import Q3.Proofs.ShiftedWindows

/-!
Prime-term B-range certificate at t_critical, tau = 0.
Source: output/prime_cert_brange_tcritical_interval_2026-01-30_2206.txt
-/

noncomputable section

namespace Q3.Proofs.PrimeCert

open Q3

/-- Grid cover certificate on [B_min, B_max]. -/
lemma prime_b_grid_cover_cert :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      ∃ i : Fin prime_b_grid_size,
        |B - prime_b_grid i| ≤ prime_cert_B_h / 2
  := by
  intro B hB
  rcases hB with ⟨hBmin, hBmax⟩
  -- rescale to [0, N]
  set t : ℝ := (B - B_min) / prime_cert_B_h
  have hB_h_pos : (0 : ℝ) < prime_cert_B_h := by
    norm_num [prime_cert_B_h]
  have ht0 : 0 ≤ t := by
    exact div_nonneg (sub_nonneg.mpr hBmin) (le_of_lt hB_h_pos)
  have htN : t ≤ (19 : ℝ) := by
    have hsub : B - B_min ≤ prime_cert_B_max - B_min := sub_le_sub_right hBmax _
    -- t = (B - B_min) / 0.1 = 10 * (B - B_min)
    have ht_repr : t = (10 : ℝ) * (B - B_min) := by
      have : t = (B - B_min) * (10 : ℝ) := by
        simp [t, prime_cert_B_h, div_eq_mul_inv, mul_assoc]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have hmax_repr : (10 : ℝ) * (prime_cert_B_max - B_min) = (19 : ℝ) := by
      norm_num [prime_cert_B_max, B_min]
    nlinarith [ht_repr, hmax_repr, hsub]
  -- choose nearest grid index via floor(t+1/2)
  set n : ℕ := Nat.floor (t + 1/2)
  have hn_le : (n : ℝ) ≤ t + 1/2 := Nat.floor_le (by nlinarith [ht0])
  have ht_lt : t + 1/2 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t + 1/2)
  have hn_lt : n < prime_b_grid_size := by
    have hnonneg : 0 ≤ t + 1/2 := by nlinarith [ht0]
    have h1 : t + 1/2 ≤ (19 : ℝ) + 1/2 := by
      linarith [htN]
    have h2 : (19 : ℝ) + 1/2 < (19 : ℝ) + 1 := by
      nlinarith
    have htop' : t + 1/2 < (19 : ℝ) + 1 := lt_of_le_of_lt h1 h2
    have htop : t + 1/2 < ((20 : ℕ) : ℝ) := by
      nlinarith [htop']
    have hnlt : n < 20 := (Nat.floor_lt hnonneg).2 htop
    simpa using hnlt
  refine ⟨⟨n, hn_lt⟩, ?_⟩
  -- distance ≤ h/2
  have h_repr : t * prime_cert_B_h = B - B_min := by
    unfold t
    field_simp [prime_cert_B_h]
  have hdiff :
      B - prime_b_grid ⟨n, hn_lt⟩ = prime_cert_B_h * (t - n) := by
    simp [prime_b_grid]
    nlinarith [h_repr]
  have habs_t : |t - n| ≤ (1/2 : ℝ) := by
    have h1 : (n : ℝ) - 1/2 ≤ t := by nlinarith [hn_le]
    have h2 : t ≤ (n : ℝ) + 1/2 := by nlinarith [ht_lt]
    exact (abs_le.mpr ⟨by nlinarith [h1], by nlinarith [h2]⟩)
  have hmul : |B - prime_b_grid ⟨n, hn_lt⟩| = prime_cert_B_h * |t - n| := by
    simp [hdiff, abs_mul, abs_of_pos hB_h_pos]
  have hmul' : prime_cert_B_h * |t - n| ≤ prime_cert_B_h * (1/2 : ℝ) := by
    exact mul_le_mul_of_nonneg_left habs_t (le_of_lt hB_h_pos)
  have hfinal : |B - prime_b_grid ⟨n, hn_lt⟩| ≤ prime_cert_B_h / 2 := by
    simpa [hmul, mul_div_assoc] using hmul'
  simpa using hfinal

/-- Margin certificate on B-range at t_critical (tau = 0). -/
lemma prime_cert_margin_on_Brange_axiom :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      prime_cert_margin_lb ≤
        arch_term (fun ξ => phi_shift B t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift B t_critical 0 ξ)
  := by
  intro B hB
  rcases prime_b_grid_cover_cert B hB with ⟨i, hdist⟩
  -- shorthand for the margin function
  set margin := fun x : ℝ =>
    arch_term (fun ξ => phi_shift x t_critical 0 ξ) -
      prime_term (fun ξ => phi_shift x t_critical 0 ξ)
  have hgrid_lb :
      prime_cert_margin_lb + prime_cert_L_ub * prime_cert_B_h / 2 ≤ prime_b_grid_val i := by
    exact prime_b_grid_val_ge_lb_with_slack i
  have hgrid_margin : prime_b_grid_val i ≤ margin (prime_b_grid i) := by
    simpa [margin] using (prime_b_grid_val_le_margin i)
  have hLip :
      |margin B - margin (prime_b_grid i)| ≤
        prime_cert_L_ub * |B - prime_b_grid i| := by
    simpa [margin, sub_eq_add_neg, abs_sub_comm] using
      (prime_margin_Lipschitz_on_Brange B (prime_b_grid i) hB
        (by
          -- grid point is in the B-range by construction
          have hi_nat : i.1 < 20 := by
            simpa using i.2
          have hi : (i.1 : ℝ) ≤ 19 := by
            exact_mod_cast (Nat.lt_succ_iff.mp hi_nat)
          have hBmin' : B_min ≤ prime_b_grid i := by
            have hi0 : (0 : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast (Nat.zero_le i.1)
            have hBh0 : 0 ≤ prime_cert_B_h := by norm_num [prime_cert_B_h]
            have hprod : 0 ≤ (i.1 : ℝ) * prime_cert_B_h := mul_nonneg hi0 hBh0
            have : B_min ≤ B_min + (i.1 : ℝ) * prime_cert_B_h :=
              le_add_of_nonneg_right hprod
            simpa [prime_b_grid] using this
          have hBmax' : prime_b_grid i ≤ prime_cert_B_max := by
            have hBh0 : 0 ≤ prime_cert_B_h := by norm_num [prime_cert_B_h]
            have hmul : (i.1 : ℝ) * prime_cert_B_h ≤ (19 : ℝ) * prime_cert_B_h :=
              mul_le_mul_of_nonneg_right hi hBh0
            have hbound : prime_b_grid i ≤ B_min + (19 : ℝ) * prime_cert_B_h := by
              have : B_min + (i.1 : ℝ) * prime_cert_B_h ≤ B_min + (19 : ℝ) * prime_cert_B_h :=
                add_le_add_left hmul B_min
              simpa [prime_b_grid] using this
            have h19 : B_min + (19 : ℝ) * prime_cert_B_h = prime_cert_B_max := by
              norm_num [B_min, prime_cert_B_h, prime_cert_B_max]
            simpa [h19] using hbound
          exact ⟨hBmin', hBmax'⟩))
  have hLip' := (abs_sub_le_iff).1 hLip
  have hdist' :
      prime_cert_L_ub * |B - prime_b_grid i| ≤
        prime_cert_L_ub * (prime_cert_B_h / 2) := by
    exact mul_le_mul_of_nonneg_left hdist prime_cert_L_ub_nonneg
  -- combine: margin B ≥ margin(grid) - L*|B-grid|
  have hmargin_ge :
      margin (prime_b_grid i) - prime_cert_L_ub * |B - prime_b_grid i| ≤ margin B :=
    by
      -- use the second inequality from `abs_sub_le_iff`
      nlinarith [hLip'.2]
  have hgrid_ge :
      prime_cert_margin_lb ≤ margin (prime_b_grid i) - prime_cert_L_ub * (prime_cert_B_h / 2) := by
    have : prime_cert_margin_lb + prime_cert_L_ub * prime_cert_B_h / 2 ≤ margin (prime_b_grid i) := by
      exact le_trans hgrid_lb hgrid_margin
    nlinarith
  have hfinal : prime_cert_margin_lb ≤ margin B := by
    have : prime_cert_margin_lb ≤ margin (prime_b_grid i) - prime_cert_L_ub * |B - prime_b_grid i| := by
      have hL : prime_cert_L_ub * |B - prime_b_grid i| ≤ prime_cert_L_ub * (prime_cert_B_h / 2) := hdist'
      nlinarith [hgrid_ge, hL]
    exact le_trans this hmargin_ge
  simpa [margin] using hfinal

/-- Kernel-backed margin certificate on B-range at `t_critical`, `tau = 0`.

This is the proof-carrying route consumed by the mainline tau-0 gate.
-/
lemma prime_cert_margin_on_Brange_kernel_shadow :
    ∀ B ∈ Set.Icc B_min prime_cert_B_max,
      prime_cert_margin_lb ≤
        arch_term (fun ξ => phi_shift B t_critical 0 ξ) -
          prime_term (fun ξ => phi_shift B t_critical 0 ξ) := by
  have hcheck :
      checkPrimeHeatMarginCert prime_heat_margin_cert_2026_01_28 = true :=
    prime_heat_margin_cert_2026_01_28_checked
  have hgrid_margin :
      ∀ i : Fin prime_b_grid_size, prime_b_grid_val i ≤ margin_tau0 (prime_b_grid i) := by
    intro i
    simpa [margin_tau0, phi_shift_critical_tau0] using prime_b_grid_val_le_margin i
  have hcore :
      ∀ B ∈ Set.Icc B_min prime_cert_B_max,
        prime_cert_margin_lb ≤ margin_tau0 B := by
    exact margin_lb_on_brange_of_checked_cert
      (cert := prime_heat_margin_cert_2026_01_28)
      (_hcheck := hcheck)
      (h_cover := prime_b_grid_cover_cert)
      (h_grid_margin := hgrid_margin)
  intro B hB
  simpa [margin_tau0, phi_shift_critical_tau0] using hcore B hB

end Q3.Proofs.PrimeCert
